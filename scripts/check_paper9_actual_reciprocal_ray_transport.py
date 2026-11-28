#!/usr/bin/env python3
"""Exact diagnostic for Paper 9 CM163 reciprocal ray and coefficient transport.
Uses the original degree-41 maps and exact Q(i*sqrt(163)) arithmetic.
This does not execute Agda, certify convergence, or prove the period.
"""
import sympy as s


def main():
    r = s.sqrt(163)
    t = (-1 + s.I * r) / 2
    tb = s.conjugate(t)
    d = t - tb
    w, z = s.symbols("w z")
    alpha = (-81 - s.I * r) / 82
    beta = s.conjugate(alpha)

    def forward(x):
        return -41 / (x + 1)

    def reverse(x):
        return -41 / x - 1

    def undisk(v):
        return t + d * v / (1 - v)

    a, b, p, e = s.symbols("a b p e")
    ell = -2 * p
    checks = {
        "CM quadratic": t*t+t+41,
        "forward fixed": forward(t)-t,
        "reverse fixed": reverse(t)-t,
        "reciprocal multipliers": alpha*beta-1,
        "forward cleared rotation": (-41-t*(z+1))*(z-tb)-alpha*(-41-tb*(z+1))*(z-t),
        "reverse cleared rotation": (-41-z-t*z)*(z-tb)-beta*(-41-z-tb*z)*(z-t),
        "forward inverse disk": forward(undisk(w))-undisk(alpha*w),
        "reverse inverse disk": reverse(undisk(w))-undisk(beta*w),
        "forward and reverse maps inverse": reverse(forward(z))-z,
        "disk second coefficient": ell*a+ell**2*b/2-(-2*p*a+2*p**2*b),
        "first jet rotation": (z*ell)*a-z*(ell*a),
        "second jet rotation": (z*z*ell)*a+(z*ell)**2*e-z*z*(ell*a+ell**2*e),
    }
    for name, residual in checks.items():
        result = s.simplify(s.cancel(residual, extension=s.I*r))
        assert result == 0, (name, result)
        print("PASS", name)
    print(f"{len(checks)}/{len(checks)} exact symbolic checks PASS")


if __name__ == "__main__":
    main()
