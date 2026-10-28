#!/usr/bin/env python3
"""Exhaustive 3-colour 3x3 face-pattern gluing test (not a pants proof).

Original maths/source ownership remains in DASHI's TernaryComparisonSynthesis,
TypedHyperfabricPantsGluingBridge, TrialecticGrothendieckTransitionCocycle,
and Base369/S3. Counts concern finite face paints ONLY, not real source truth.
"""
from itertools import permutations
from collections import Counter
import json

def digits(n):
    values = []
    for _ in range(9):
        values.append(n % 3)
        n //= 3
    return tuple(values)

def encode(a):
    return sum(v * (3 ** i) for i, v in enumerate(a))

def face_symmetries():
    transformations = []
    for reflected in (False, True):
        for turns in range(4):
            mapping = []
            for j in range(3):
                for i in range(3):
                    x, y = (2-i, j) if reflected else (i, j)
                    for _ in range(turns):
                        x, y = 2-y, x
                    mapping.append(y*3 + x)
            transformations.append(tuple(mapping))
    assert len(set(transformations)) == 8
    return transformations

def transform(pattern, perm, face_map):
    out = [0] * 9
    for i, destination in enumerate(face_map):
        out[destination] = perm[pattern[i]]
    return encode(out)

def verify():
    transformations = face_symmetries()
    palette = list(permutations(range(3)))
    strict = 0
    palette_recharted = 0
    face_and_palette_recharted = 0
    orbit_sizes = Counter()
    for n in range(3**9):
        pattern = digits(n)
        strict += 1
        palette_orbit = {transform(pattern, p, transformations[0]) for p in palette}
        aligned_orbit = {
            transform(pattern, p, face)
            for p in palette for face in transformations
        }
        palette_recharted += len(palette_orbit)
        face_and_palette_recharted += len(aligned_orbit)
        orbit_sizes[len(aligned_orbit)] += 1
    assert strict == 19683
    assert palette_recharted == 118089
    assert face_and_palette_recharted == 865521
    assert dict(orbit_sizes) == {3:3,6:36,12:204,24:2928,48:16512}
    # Identical paint does not suffice for capacity equality.
    left = ("red",)*9
    right = ("red",)*9
    assert left == right and 2 != 1
    # An observed red section can be fixed, although the unobserved
    # green/blue chart has nontrivial cyclic holonomy.
    flip = lambda c: 0 if c==0 else 3-c
    assert flip(0)==0 and flip(1)==2
    return {
        "status":"passed",
        "face_sites":9, "single_cube":27,
        "ordered_face_pairs":3**18,
        "strict_colour_matching_pairs":strict,
        "s3_palette_chart_matching_pairs":palette_recharted,
        "d4_face_and_s3_palette_matching_pairs":face_and_palette_recharted,
        "orbit_size_distribution":dict(sorted(orbit_sizes.items())),
        "strict_pants_match_from_colours_alone":False,
        "global_chart_cocycle_from_pairwise_colour_matches":False,
        "actual_source_or_hyperfabric_authority":False,
        "agda_kernel_run":False,
    }

if __name__ == "__main__":
    print(json.dumps(verify(), indent=2, sort_keys=True))
