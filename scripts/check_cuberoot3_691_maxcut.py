"""Exact integer-arithmetic test fixture: cube-root-three / F_691 C3.

Existing DASHI owners: Foundations/RepresentationChartInvariant,
Foundations/RadixValuationStageBridge,
Foundations/Base369Ternary27HypervoxelFabricGeometryExact,
Moonshine/Base369Ternary27SpectralSymmetryIrrepBridgeExact,
Moonshine/C3FourierConjugationExact.

This is an external executable arithmetic receipt, not an Agda kernel proof.
"""
P = 691

def icbrt(n: int) -> int:
    if n < 0:
        raise ValueError("negative radicand")
    lo, hi = 0, 1
    while hi ** 3 <= n:
        hi *= 2
    while hi - lo > 1:
        mid = (hi + lo) // 2
        if mid ** 3 <= n:
            lo = mid
        else:
            hi = mid
    return lo

def fractional_prefix(base: int, length: int) -> tuple[int, ...]:
    """Exact digits after radix point: no floating-point approximations."""
    if base < 2 or length < 0:
        raise ValueError("invalid base or length")
    if length == 0:
        return ()
    scale = base ** length
    value = icbrt(3 * scale ** 3) - scale
    digits = [0] * length
    for i in range(length - 1, -1, -1):
        digits[i], value = value % base, value // base
    assert value == 0
    return tuple(digits)

def spectrum(base: int) -> int:
    return fractional_prefix(base, 1)[0]

OMEGA = pow(3, 230, P)

def multiply(a: tuple[int,int,int], b: tuple[int,int,int]) -> tuple[int,int,int]:
    """Polynomial multiplication modulo X^3 - 3 over F_691."""
    coefficients = [0] * 5
    for i in range(3):
        for j in range(3):
            coefficients[i+j] += a[i] * b[j]
    return ((coefficients[0] + 3 * coefficients[3]) % P,
            (coefficients[1] + 3 * coefficients[4]) % P,
            coefficients[2] % P)

def frobenius(a: tuple[int,int,int]) -> tuple[int,int,int]:
    """Since x^691 = 3^230*x = 437*x in the extension field."""
    return (a[0] % P, OMEGA * a[1] % P, OMEGA ** 2 * a[2] % P)

def test_exact_receipt() -> None:
    assert OMEGA == 437
    assert OMEGA != 1 and pow(OMEGA, 3, P) == 1
    assert fractional_prefix(2, 6) == (0, 1, 1, 1, 0, 0)
    assert fractional_prefix(3, 6) == (1, 0, 2, 2, 2, 1)
    assert fractional_prefix(10, 5) == (4, 4, 2, 2, 4)
    assert fractional_prefix(16, 6) == (7, 1, 3, 7, 4, 4)
    assert fractional_prefix(691, 6) == (305, 410, 530, 36, 70, 523)
    for b in range(3, 1000):
        assert spectrum(b) - spectrum(b-1) in (0, 1)
    for c in range(P):
        for a in ((c,0,0),(0,c,0),(0,0,c)):
            assert frobenius(frobenius(frobenius(a))) == a
    probes = [(0,0,0),(1,2,3),(690,683,617),(0,1,0),(0,0,1)]
    for a in probes:
        for b in probes:
            assert frobenius(multiply(a,b)) == multiply(frobenius(a),frobenius(b))
    assert multiply((0,1,0),(0,0,1)) == (3,0,0)

if __name__ == "__main__":
    test_exact_receipt()
    print("PASS: radix prefixes, spectrum, cubic nonresidue, Frobenius C3")
