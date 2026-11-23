#!/usr/bin/env python3
"""CMP102: exact-rational original exponential Cauchy signs and shifted A/B source.

Finite reference only. The unbounded Agda proof and analytic series remain separate.
"""
from fractions import Fraction as Q
from math import factorial


def exp_term(x: int, k: int) -> Q:
    return Q(x**k, factorial(k))


def even(x: int, k: int) -> Q:
    return exp_term(x, 2*k)


def odd(x: int, k: int) -> Q:
    return exp_term(x, 2*k + 1)


def a(k: int) -> Q:
    return Q(1, factorial(2*k + 2))


def b(k: int) -> Q:
    return Q(1, factorial(2*k + 3))


def cauchy(left, right, n: int) -> Q:
    return sum((left(k)*right(n-k) for k in range(n+1)), Q(0))


def main(N: int = 128) -> None:
    count = dict(even_sign_term=0, odd_sign_term=0, shifted_a=0,
                 shifted_b=0, even_row=0, odd_row=0,
                 original_exp_zero=0, shifted_bracket_zero=0,
                 endpoint_negative=0)
    for n in range(N):
        for k in range(n+2):
            assert even(-1, k) == even(1, k)
            count['even_sign_term'] += 1
        for k in range(n+1):
            assert odd(-1, k) == -odd(1, k)
            count['odd_sign_term'] += 1
        assert even(1, n+1) == a(n)
        count['shifted_a'] += 1
        assert odd(1, n+1) == b(n)
        count['shifted_b'] += 1
        ep = cauchy(lambda k: even(1,k), lambda k: even(1,k), n+1)
        es = cauchy(lambda k: even(1,k), lambda k: even(-1,k), n+1)
        op = cauchy(lambda k: odd(1,k), lambda k: -odd(1,k), n)
        os = cauchy(lambda k: odd(1,k), lambda k: odd(-1,k), n)
        assert es == ep
        count['even_row'] += 1
        assert os == op
        count['odd_row'] += 1
        assert es+os == Q(0)
        count['original_exp_zero'] += 1
        E = 2*a(n) + sum((a(k)*a(n-1-k) for k in range(n)), Q(0))
        O = Q(1) if n == 0 else 2*b(n-1) + sum((b(k)*b(n-2-k) for k in range(n-1)), Q(0))
        assert ep == E and op == -O and O-E == Q(0)
        count['shifted_bracket_zero'] += 1
        # If the last even original endpoint is omitted, the signed sum is nonzero.
        assert ep - even(1,n+1)*even(1,0) + op == -a(n)
        count['endpoint_negative'] += 1
    print(count)
    print('PASS', sum(count.values()), 'exact Fraction assertions, degrees 0..', N-1)


if __name__ == '__main__':
    main()
