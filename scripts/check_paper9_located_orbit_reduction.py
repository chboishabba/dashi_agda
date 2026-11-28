#!/usr/bin/env python3
"""Exact rational finite-fuel diagnostics, not an Agda proof or real-order oracle."""
from fractions import Fraction as Q
from math import factorial


def run():
    for high_first in (True, False):
        count = steps = maxsteps = 0
        for den in range(1, 25):
            for a in range(-32, 33):
                for b in range(1, 9):
                    x, y = Q(a, den), Q(b, den)
                    y0 = y
                    delta = y / 3
                    fuel = int(1 / delta) + 1
                    s = 0
                    while fuel and (y <= Q(1, 3) if high_first else y < Q(1, 2)):
                        assert y >= y0 and y + fuel * delta >= Q(1, 3)
                        n = int(abs(x)) + 1
                        x += n
                        left = 2 * n
                        assert 0 <= x <= left + Q(2, 3)
                        while left and (x >= Q(2, 3) if high_first else x > Q(1, 3)):
                            assert x > Q(1, 3)
                            x -= 1
                            left -= 1
                            assert -Q(2, 3) <= x <= left + Q(2, 3)
                        assert -Q(2, 3) <= x <= Q(2, 3)
                        d = x*x + y*y
                        assert 0 < d < Q(3, 4)
                        old_y = y
                        x, y = -x/d, y/d
                        assert y >= Q(4, 3) * old_y and y >= old_y + delta
                        fuel -= 1
                        assert y + fuel * delta >= Q(1, 3)
                        s += 1
                    assert y >= Q(1, 3)
                    count += 1
                    steps += s
                    maxsteps = max(maxsteps, s)
        print(f'overlap_high_first={high_first}: cases={count} inversions={steps} max={maxsteps}')
    assert sum(Q(19,10)**k/factorial(k) for k in range(5)) == Q(1533881,240000) > 6
    assert Q(6)*(Q(1,3)-Q(1,64)) == Q(61,32) > Q(19,10)
    print('radius inequalities PASS; no native kernel acceptance claimed')


if __name__ == '__main__':
    run()
