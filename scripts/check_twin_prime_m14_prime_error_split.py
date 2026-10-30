#!/usr/bin/env python3
"""Independent exact symbolic check for the M14 nine-case prime/error split.

(p,q) is a formal log(p)*log(q) monomial, not a float. Finite tests
do NOT establish Agda typechecking or the unproved analytic estimate.
Original source owners: RiemannVonMangoldtSpecification,
ChebyshevPrimeCounting and NatPrimeCountingInstance.
"""
from collections import Counter
from math import isqrt
from random import Random

def classify(n):
    if n < 2:
        return "outside", None
    q, factors = n, []
    for p in range(2, isqrt(n) + 1):
        if q % p == 0:
            k = 0
            while q % p == 0:
                k += 1
                q //= p
            factors.append((p, k))
    if q > 1:
        factors.append((q, 1))
    if len(factors) != 1:
        return "outside", None
    p, k = factors[0]
    return ("prime" if k == 1 else "proper"), p

def trial_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))

def triple(n):
    a, b = classify(n), classify(n + 2)
    if a[0] == "outside" or b[0] == "outside":
        return None, None, None
    term = (a[1], b[1])
    return (term, term, None) if a[0] == b[0] == "prime" else (term, None, term)

def main():
    maxn = 30000
    categories = Counter()
    triples = []
    for n in range(maxn):
        a, b = classify(n), classify(n + 2)
        categories[(a[0], b[0])] += 1
        weight, prime_only, error = triple(n)
        assert (weight is not None) == (prime_only is not None or error is not None)
        assert (prime_only is not None) == (trial_prime(n) and trial_prime(n + 2))
        triples.append((weight, prime_only, error))
    assert len(categories) == 9
    assert triple(25) == ((5, 3), None, (5, 3))
    assert triple(59) == ((59, 61), (59, 61), None)
    rng = Random(190273)
    cases = [(0,0), (25,4), (59,1), (209,270), (269,500), (10000,300)]
    cases += [(rng.randrange(maxn-700), rng.randrange(1,650)) for _ in range(700)]
    for start, count in cases:
        whole, prime, error = Counter(), Counter(), Counter()
        for w, p, e in triples[start:start+count]:
            if w is not None: whole[w] += 1
            if p is not None: prime[p] += 1
            if e is not None: error[e] += 1
        assert whole == prime + error
    print({"status": "PASS", "pair_terms": maxn,
           "finite_interval_decompositions": len(cases),
           "support_case_frequencies": dict(categories),
           "proper_pair_error_terms": sum(e is not None for _, _, e in triples),
           "agda_kernel_verified": False, "analytic_error_bound_proved": False})

if __name__ == "__main__":
    main()
