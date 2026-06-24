package toml

// Struct field handling is adapted from code in encoding/json:
//
// Copyright 2010 The Go Authors.  All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the Go distribution.

import (
	"reflect"
	"sort"
	"strings"
	"sync"
)

// A field represents a single field found in a struct.
type field struct {
	name      string       // the name of the field (`toml` tag included)
	tag       bool         // whether field has a `toml` tag
	index     []int        // represents the depth of an anonymous field
	typ       reflect.Type // the type of the field
	lowerName string       // lowercase name, used for case-insensitive comparison
}

// byName sorts field by name, breaking ties with depth,
// then breaking ties with "name came from toml tag", then
// breaking ties with index sequence.
type byName []field

func (x byName) Len() int      { return len(x) }
func (x byName) Swap(i, j int) { x[i], x[j] = x[j], x[i] }
func (x byName) Less(i, j int) bool {
	if x[i].lowerName != x[j].lowerName {
		return x[i].lowerName < x[j].lowerName
	}
	if len(x[i].index) != len(x[j].index) {
		return len(x[i].index) < len(x[j].index)
	}
	if x[i].tag != x[j].tag {
		return x[i].tag
	}
	return byIndex(x).Less(i, j)
}

// byIndex sorts field by index sequence.
type byIndex []field

func (x byIndex) Len() int      { return len(x) }
func (x byIndex) Swap(i, j int) { x[i], x[j] = x[j], x[i] }
func (x byIndex) Less(i, j int) bool {
	for k, xik := range x[i].index {
		if k >= len(x[j].index) {
			return false
		}
		if xik != x[j].index[k] {
			return xik < x[j].index[k]
		}
	}
	return len(x[i].index) < len(x[j].index)
}

// fieldCollision records when multiple struct fields share the same TOML name
// (case-insensitive) and cannot be resolved by Go's embedding rules, causing
// all candidates to be silently dropped. This information is surfaced during
// decoding so users know why their fields are missing.
type fieldCollision struct {
	name          string // the TOML field name (case-insensitive match target)
	candidateType string // the parent struct type where the collision occurred
	count         int    // number of conflicting candidate fields that were dropped
}

// typeFieldsResult is the cached output of typeFields, including both the
// usable fields and any collisions that were silently dropped.
type typeFieldsResult struct {
	fields     []field
	collisions []fieldCollision
}

// typeFields returns a list of fields that TOML should recognize for the given
// type. The algorithm is breadth-first search over the set of structs to
// include - the top struct and then any reachable anonymous structs.
func typeFields(t reflect.Type) typeFieldsResult {
	// Anonymous fields to explore at the current level and the next.
	current := []field{}
	next := []field{{typ: t}}

	// Count of queued names for current level and the next.
	var count map[reflect.Type]int
	var nextCount map[reflect.Type]int

	// Types already visited at an earlier level.
	visited := map[reflect.Type]bool{}

	// Fields found.
	var fields []field

	for len(next) > 0 {
		current, next = next, current[:0]
		count, nextCount = nextCount, map[reflect.Type]int{}

		for _, f := range current {
			if visited[f.typ] {
				continue
			}
			visited[f.typ] = true

			// Scan f.typ for fields to include.
			for i := 0; i < f.typ.NumField(); i++ {
				sf := f.typ.Field(i)
				if sf.PkgPath != "" && !sf.Anonymous { // unexported
					continue
				}
				opts := getOptions(sf.Tag)
				if opts.skip {
					continue
				}
				index := make([]int, len(f.index)+1)
				copy(index, f.index)
				index[len(f.index)] = i

				ft := sf.Type
				if ft.Name() == "" && ft.Kind() == reflect.Pointer {
					// Follow pointer.
					ft = ft.Elem()
				}

				// Record found field and index sequence.
				if opts.name != "" || !sf.Anonymous || ft.Kind() != reflect.Struct {
					tagged := opts.name != ""
					name := opts.name
					if name == "" {
						name = sf.Name
					}
					fields = append(fields, field{name, tagged, index, ft, strings.ToLower(name)})
					if count[f.typ] > 1 {
						// If there were multiple instances, add a second,
						// so that the annihilation code will see a duplicate.
						// It only cares about the distinction between 1 or 2,
						// so don't bother generating any more copies.
						fields = append(fields, fields[len(fields)-1])
					}
					continue
				}

				// Record new anonymous struct to explore in next round.
				nextCount[ft]++
				if nextCount[ft] == 1 {
					f := field{name: ft.Name(), index: index, typ: ft, lowerName: strings.ToLower(ft.Name())}
					next = append(next, f)
				}
			}
		}
	}

	sort.Sort(byName(fields))

	// Delete all fields that are hidden by the Go rules for embedded fields,
	// except that fields with TOML tags are promoted.

	// The fields are sorted in primary order of lowercase name, secondary order
	// of field index length. Loop over names; for each name, delete
	// hidden fields by choosing the one dominant field that survives.
	var collisions []fieldCollision
	out := fields[:0]
	for advance, i := 0, 0; i < len(fields); i += advance {
		// One iteration per name (case-insensitive).
		// Find the sequence of fields with the lowercased name of this first field.
		fi := fields[i]
		name := fi.lowerName
		for advance = 1; i+advance < len(fields); advance++ {
			fj := fields[i+advance]
			if fj.lowerName != name {
				break
			}
		}
		if advance == 1 { // Only one field with this (lowercased) name
			out = append(out, fi)
			continue
		}
		dominant, ok, dropped := dominantField(fields[i : i+advance])
		if ok {
			out = append(out, dominant)
			if dropped > 0 {
				collisions = append(collisions, fieldCollision{
					name:          fi.name,
					candidateType: t.String(),
					count:         dropped,
				})
			}
		} else {
			// All candidates were dropped due to a tie at the same level.
			collisions = append(collisions, fieldCollision{
				name:          fi.name,
				candidateType: t.String(),
				count:         dropped,
			})
		}
	}

	fields = out
	sort.Sort(byIndex(fields))

	return typeFieldsResult{fields: fields, collisions: collisions}
}

// dominantField looks through the fields, all of which are known to
// have the same lowercased name, to find the single field that dominates the
// others using Go's embedding rules, modified by the presence of
// TOML tags. If there are multiple top-level fields, the boolean
// will be false: This condition is an error in Go and we skip all
// the fields. The second return value is the number of candidate
// fields dropped due to the conflict (0 when there's no conflict).
func dominantField(fields []field) (field, bool, int) {
	// The fields are sorted in increasing index-length order. The winner
	// must therefore be one with the shortest index length. Drop all
	// longer entries, which is easy: just truncate the slice.
	length := len(fields[0].index)
	tagged := -1 // Index of first tagged field.
	dropped := 0
	for i, f := range fields {
		if len(f.index) > length {
			dropped += len(fields) - i
			fields = fields[:i]
			break
		}
		if f.tag {
			if tagged >= 0 {
				// Multiple tagged fields at the same level: conflict
				// (even if their tag names differ only by case).
				// Return no field, reporting all candidates dropped.
				return field{}, false, len(fields)
			}
			tagged = i
		}
	}
	if tagged >= 0 {
		return fields[tagged], true, len(fields) - 1
	}
	// All remaining fields have the same length. If there's more than one,
	// we have a conflict (two fields whose names match case-insensitively
	// at the same level) and we return no field.
	if len(fields) > 1 {
		return field{}, false, len(fields)
	}
	return fields[0], true, 0
}

var fieldCache struct {
	sync.RWMutex
	m map[reflect.Type]typeFieldsResult
}

// cachedTypeFields is like typeFields but uses a cache to avoid repeated work.
func cachedTypeFields(t reflect.Type) []field {
	return cachedTypeFieldsResult(t).fields
}

// cachedTypeFieldsResult returns the full typeFieldsResult including collision
// information, for the given struct type.
func cachedTypeFieldsResult(t reflect.Type) typeFieldsResult {
	fieldCache.RLock()
	r, ok := fieldCache.m[t]
	fieldCache.RUnlock()
	if ok {
		return r
	}

	// Compute fields without lock.
	// Might duplicate effort but won't hold other computations back.
	r = typeFields(t)
	if r.fields == nil {
		r.fields = []field{}
	}

	fieldCache.Lock()
	if fieldCache.m == nil {
		fieldCache.m = map[reflect.Type]typeFieldsResult{}
	}
	fieldCache.m[t] = r
	fieldCache.Unlock()
	return r
}
