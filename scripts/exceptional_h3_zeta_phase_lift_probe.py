from itertools import product

P = 3
G = (
    (1, 0, 1),
    (0, 1, 0),
    (1, 0, 1),
)
ELL = (1, 0, 2)  # x-z; nonzero on radical r=(1,0,-1)


def outer(v):
    return tuple(tuple(v[i] * v[j] % 3 for j in range(3)) for i in range(3))


def add(a, b):
    return tuple(tuple((a[i][j] + b[i][j]) % 3 for j in range(3)) for i in range(3))


def det3(m):
    return (
        m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1])
        - m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])
        + m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0])
    ) % 3


def matvec(m, v):
    return tuple(sum(m[i][j]*v[j] for j in range(3)) % 3 for i in range(3))


def dot(v, w):
    return sum(v[i]*w[i] for i in range(3)) % 3


def verify():
    radical = (1, 0, 2)
    assert matvec(G, radical) == (0, 0, 0)
    assert dot(ELL, radical) == 2  # nonzero; orientation can rescale to 1
    phase_gram = outer(ELL)
    lifted = add(G, phase_gram)
    assert lifted == ((2,0,0),(0,1,0),(0,0,2))
    assert det3(G) == 0
    assert det3(lifted) == 1

    # phase coordinate splits every point uniquely into kernel(ell)+t*radical.
    # Since ell(radical)=2, t = 2*ell(point) over F3.
    kernel = [p for p in product(range(3), repeat=3) if dot(ELL, p) == 0]
    assert len(kernel) == 9
    recovered = set()
    for k in kernel:
        for t in range(3):
            recovered.add(tuple((k[i] + t*radical[i]) % 3 for i in range(3)))
    assert len(recovered) == 27

    return {
        "h3_gram": G,
        "radical": radical,
        "phase_functional": ELL,
        "phase_on_radical": 2,
        "phase_kernel_size": 9,
        "phase_lifted_gram": lifted,
        "phase_lifted_determinant": 1,
        "phase_lift_resolves_radical": True,
        "e8_zeta_same_action_assignment_paid": False,
    }


if __name__ == "__main__":
    for k, v in verify().items():
        print(f"{k}: {v}")
