import numpy as np

P = 3
B = np.array([
    [2,2,0,0,0],
    [2,2,2,0,2],
    [0,2,2,2,0],
    [0,0,2,2,0],
    [0,2,0,0,2],
], dtype=int) % P
E_PLUS = np.array([
    [1,1,1],
    [0,0,2],
    [0,1,2],
    [2,0,2],
    [0,0,1],
], dtype=int) % P
E_MINUS = np.array([
    [0,0,0],
    [0,0,0],
    [0,0,1],
    [1,1,1],
    [1,2,2],
], dtype=int) % P
G_PLUS = E_PLUS.T @ B @ E_PLUS % P
G_MINUS = E_MINUS.T @ B @ E_MINUS % P
T = np.array([
    [2,0,1],
    [0,1,0],
    [1,0,0],
], dtype=int) % P
WEYL = np.array([
    [2,0,1,2,1],
    [1,1,2,1,0],
    [0,1,0,2,0],
    [2,0,2,2,0],
    [0,1,2,2,0],
], dtype=int) % P
WEYL_WORD_LEFT_ACTION = (0,1,3,2,4,1,5,4,1,0,2,1)


def rank_mod3(m):
    a = np.array(m, dtype=int) % 3
    r = 0
    for c in range(a.shape[1]):
        pivot = next((i for i in range(r, a.shape[0]) if a[i,c]), None)
        if pivot is None:
            continue
        a[[r,pivot]] = a[[pivot,r]]
        if a[r,c] == 2:
            a[r] = 2*a[r] % 3
        for i in range(a.shape[0]):
            if i != r and a[i,c]:
                a[i] = (a[i] - a[i,c]*a[r]) % 3
        r += 1
    return r


def verify():
    assert np.array_equal(E_MINUS @ T % 3, WEYL @ E_PLUS % 3)
    pulled = T.T @ G_MINUS @ T % 3
    assert np.array_equal(pulled, G_PLUS)
    identity_aggregate = (G_PLUS + G_MINUS) % 3
    weyl_aggregate = (G_PLUS + pulled) % 3
    assert rank_mod3(identity_aggregate) == 3
    assert rank_mod3(weyl_aggregate) == 2
    assert np.array_equal(weyl_aggregate, 2 * G_PLUS % 3)
    return {
        "weyl_word_left_action": WEYL_WORD_LEFT_ACTION,
        "weyl_matrix": WEYL.tolist(),
        "local_transition": T.tolist(),
        "identity_coregistration_rank": 3,
        "weyl_coregistration_rank": 2,
        "pulled_minus_equals_plus": True,
        "weyl_covariant_quadratic_gluing_resolves_radical": False,
        "additional_nontransported_structure_required": True,
    }


if __name__ == "__main__":
    for k, v in verify().items():
        print(f"{k}: {v}")
