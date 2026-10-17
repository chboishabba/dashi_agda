#!/usr/bin/env python3
from __future__ import annotations

import json
from collections import deque
import numpy as np

from exceptional_e8_normalizer_e6_same_action import (
    P, J, NORMALIZER_WORD, CENTRALIZER_WORD_A, CENTRALIZER_WORD_B,
    e8_data, eval_word, induced4,
)


def key(a):
    return tuple(int(x) for x in a.reshape(-1))


def matrix_group(gens):
    ident = np.eye(4, dtype=int) % P
    seen = {key(ident): ident}
    queue = deque([ident])
    while queue:
        g = queue.popleft()
        for s in gens:
            h = (s @ g) % P
            k = key(h)
            if k not in seen:
                seen[k] = h
                queue.append(h)
    return list(seen.values())


def multiplier(a):
    form = (a.T @ J @ a) % P
    if np.array_equal(form, J):
        return 1
    if np.array_equal(form, (2 * J) % P):
        return 2
    return 0


def compute_receipt():
    _, reflections, _ = e8_data()
    a = induced4(eval_word(CENTRALIZER_WORD_A, reflections))
    b = induced4(eval_word(CENTRALIZER_WORD_B, reflections))
    n = induced4(eval_word(NORMALIZER_WORD, reflections))
    group = matrix_group((a,b,n))
    assert len(group) == 103680
    counts = {1:0, 2:0, 0:0}
    for g in group:
        counts[multiplier(g)] += 1
    assert counts == {1:51840, 2:51840, 0:0}
    return {
        "normalizer_vector_image_order": len(group),
        "symplectic_multiplier_plus_one_count": counts[1],
        "antisymplectic_multiplier_minus_one_count": counts[2],
        "other_multiplier_count": counts[0],
        "centralizer_order_from_previous_exact_receipt": 155520,
        "normalizer_order_from_nontrivial_aut_c3_coset": 311040,
    }


if __name__ == "__main__":
    print(json.dumps(compute_receipt(), indent=2, sort_keys=True))
