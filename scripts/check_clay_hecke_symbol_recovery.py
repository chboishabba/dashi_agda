"""Finite exact controls for Hecke-symbol recovery, not actual modular symbols."""
from fractions import Fraction as Q
from math import isqrt
from sympy import factorint, primerange

checks = 0

def check(ok):
    global checks
    if not ok:
        raise AssertionError('exact control failed')
    checks += 1

# Root-of-unity trace for q^(n/l) under the l translations.
# Count powers as coefficients of the group algebra, with exact cyclotomic
# reduction for prime l: 1+X+...+X^(l-1)=0.
for l in primerange(2, 24):
    for n in range(1, 81):
        c = [0]*l
        for b in range(l):
            c[(n*b)%l] += 1
        reduced = [c[j]-c[-1] for j in range(l-1)]
        check(reduced == ([l]+[0]*(l-2) if n%l == 0 else [0]*(l-1)))

# q-series Hecke action and its integrated (a_n/n) primitive action.
# Use independent coefficient data; this is an identity on any polynomial,
# not a claim that the polynomial is an eigenform.
for l in primerange(2, 24):
    for good in (False, True):
        for j in range(1, 41):
            a = lambda n: (n*n+3*n+7)%23-11
            from_form = Q(a(l*j) + (l*a(j//l) if good and j%l==0 else 0), j)
            from_path = l*Q(a(l*j), l*j)
            if good and j%l==0:
                from_path += Q(a(j//l), j//l)
            check(from_form == from_path)

# Precision loss at nonunit anchor, signed balanced reconstruction.
for p in (2, 3, 5, 7, 11):
    for v in range(4):
        for n in range(1, 33):
            B = 2*n
            k = v+1
            while p**(k-v) <= 2*B:
                k += 1
            M = p**k
            m = p**(k-v)
            for unit in (1, p+1, -(2*p+1)):
                D = p**v*unit % M
                for a in (-B, -B+1, -1, 0, 1, B-1, B):
                    H = (a*D)%M
                    x = ((H//p**v)*pow(D//p**v,-1,m))%m
                    x = x-m if 2*x>m else x
                    check(x == a)
            # Insufficient modulus: residues cannot distinguish all integers.
            small = p**(k-v-1)
            check(small <= 2*B and (-B)%small == (-B+small)%small)

# Actual conductors from existing BSD roadmap; compute Sturm indices using
# exact integer arithmetic, not an actual modular-symbol evaluation.
for N in (11, 32, 37, 389, 8840664):
    index = N
    for p in factorint(N):
        index = index//p*(p+1)
    B = index//6
    check(index == N*__import__('functools').reduce(lambda a,p:a*Q(p+1,p), factorint(N), Q(1)))
    k=1
    while 5**k <= 4*B:
        k+=1
    check(5**(k-1)<=4*B<5**k)
    # Prime-only coefficients: Hasse gives |a_l| <= floor(2 sqrt(B)).
    # Recurrences supply composite coefficients (including bad primes).
    H = isqrt(4*B)
    kp=1
    while 5**kp <= 2*H:
        kp+=1
    check(5**(kp-1)<=2*H<5**kp)
    for a in (-H, -H+1, -1, 0, 1, H-1, H):
        x=a % 5**kp
        x=x-5**kp if 2*x>5**kp else x
        check(x==a)
    print(f'N={N} index={index} Sturm={B} p=5 all-n precision={k} prime-only precision={kp}')
print(f'{checks}/{checks} exact controls PASS')
