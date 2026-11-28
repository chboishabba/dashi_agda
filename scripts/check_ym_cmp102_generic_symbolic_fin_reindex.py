#!/usr/bin/env python3
"""Original CMP102 five-term G vs signed finite Cauchy triangle/wings.

This is a genuinely coefficient-INDEPENDENT finite-polynomial
identity, not a check that happens to pass with factorial numbers.
Use SymPy independent variables a_j,b_j; verify the exact original
SeriesOf count convention and the singleton even/odd shifted rows
at all c=1..12. Signed original factorial parity is a separate
existing all-degree source theorem. Not native Agda acceptance.
"""
import sympy as s


def check(count):
    X = s.Symbol("X")
    a = s.symbols(f"a0:{count}")
    b = s.symbols(f"b0:{count}")
    A = sum((a[j] * X**j for j in range(count)), s.Integer(0))
    B = sum((b[j] * X**j for j in range(count)), s.Integer(0))

    def conv(v, k):
        return sum(
            (v[i] * v[k-i] for i in range(max(0, k-count+1), min(k, count-1)+1)),
            s.Integer(0),
        )

    G = 1 - 2*A - X*A*A + 2*X*B + X**2*B*B
    signed = sum(
        ((1 if k == 0 else 2*b[k-1] + (conv(b,k-2) if k >= 2 else 0))
         - (2*a[k] + (conv(a,k-1) if k >= 1 else 0))) * X**k
        for k in range(count)
    )
    low_a = sum((conv(a,k) * X**k for k in range(count-1)), s.Integer(0))
    low_b = sum((conv(b,k) * X**k for k in range(max(0,count-2))), s.Integer(0))
    wing_a = A*A - low_a
    wing_b = B*B - low_b
    omitted_b = 2*X*b[count-1]*X**(count-1)
    tail = -X*wing_a + omitted_b + X**2*wing_b
    assert s.Poly(s.expand(G - signed - tail), X).is_zero

    # The last original B term is essential at ALL positive counts.
    assert not s.Poly(s.expand(G-signed-(tail-omitted_b)),X).is_zero
    assert s.Poly(s.expand(tail),X).degree() >= count
    return 3


def main():
    passed = sum(check(c) for c in range(1,13))
    assert passed == 36
    print(f"ORIGINAL CMP102 GENERIC SOURCE FIN REINDEX {passed}/36 PASS")
    print("arbitrary symbolic coefficients, count 1..12; negative controls pass")


if __name__ == "__main__":
    main()
