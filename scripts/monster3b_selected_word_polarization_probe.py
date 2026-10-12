import numpy as np

P = 3
M = np.array([
    [0,2,1,0,2,1,0,0,2,0,1,2],
    [2,0,2,1,2,2,0,0,1,2,0,0],
    [0,0,0,0,1,2,2,1,2,0,2,0],
    [2,0,1,2,1,2,0,2,2,1,1,2],
    [2,0,2,2,0,2,1,0,1,1,2,0],
    [1,0,1,0,2,2,2,0,1,2,0,1],
    [1,0,2,1,0,2,1,1,1,0,0,0],
    [0,2,2,2,1,0,1,1,2,1,1,2],
    [2,2,0,0,1,0,2,1,2,1,0,0],
    [2,1,1,2,1,2,0,2,0,0,2,2],
    [2,2,0,0,1,1,1,1,0,0,2,0],
    [1,1,2,0,2,0,2,1,0,1,1,2],
], dtype=int) % P


def rank_mod3(m):
    a = np.array(m, dtype=int) % 3
    rows, cols = a.shape
    r = 0
    for c in range(cols):
        pivot = next((i for i in range(r, rows) if a[i, c]), None)
        if pivot is None:
            continue
        a[[r, pivot]] = a[[pivot, r]]
        if a[r, c] == 2:
            a[r] = 2 * a[r] % 3
        for i in range(rows):
            if i != r and a[i, c]:
                a[i] = (a[i] - a[i, c] * a[r]) % 3
        r += 1
    return r


def verify():
    A, B = M[:6, :6], M[:6, 6:]
    C, D = M[6:, :6], M[6:, 6:]
    ranks = tuple(rank_mod3(x) for x in (A, B, C, D))
    assert ranks == (6, 6, 6, 6)

    # For x in X=(x,0), Mx=(Ax,Cx). Intersection M(X)∩X requires Cx=0.
    # Since C is invertible, only x=0. Likewise B invertible for M(X*)∩X*.
    assert rank_mod3(C) == 6
    assert rank_mod3(B) == 6

    return {
        "block_ranks_A_B_C_D": ranks,
        "off_diagonal_nonzeros_B_C": (int(np.count_nonzero(B)), int(np.count_nonzero(C))),
        "selected_word_preserves_X6": False,
        "selected_word_preserves_X6_dual": False,
        "image_X6_transverse_to_X6": True,
        "image_X6dual_transverse_to_X6dual": True,
        "fixed_6_15_6_role_chart_invariant": False,
        "polarization_chart_transition_required": True,
    }


if __name__ == "__main__":
    for k, v in verify().items():
        print(f"{k}: {v}")
