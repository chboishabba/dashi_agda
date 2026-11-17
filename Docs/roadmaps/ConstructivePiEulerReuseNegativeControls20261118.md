# Euler arctangent reuse check and negative controls — 18 November 2026

## Source archaeology
Default-branch code search for `EulerArctan`, `EulerAtan`,
`arctanEuler`, `Euler hypergeometric`, and related names found **no
dedicated same-source Euler arctangent transformation**. Existing
Euler-related modules include Euler products, Euler series and several
different analytic constructions; those do not by themselves discharge
the required arctangent identity. A pull-request changed-file inspection
of YM PR #1444 likewise found no dedicated Euler-arctangent owner. A
non-default branch elsewhere could still contain such a proof.

## Exact Euler series and the correct optimization estimate
For positive integer q,

  arctan(1/q) = q/(q²+1) * Σ_{k>=0}
                       4^k (k!)² / ((2k+1)! (q²+1)^k).

The first term is q/(q²+1), and the ratio of term k+1 to term k is

  2(k+1) / ((2k+3)(q²+1)).

It approaches 1/(q²+1), compared with 1/q² for the Taylor
arctangent terms. Thus at q=5 the contraction changes from 1/25
to 1/26: small asymptotic term-count benefit, **not 4–5×**.

Euler finite prefixes are NOT identical to Taylor finite prefixes.
The missing Agda theorem identifies their infinite limits using a
valid transformation and an explicit Cauchy/tail bound.

Since the Euler coefficients are positive and the ratio is <= 1/d,
where d=q²+1, the tail after n terms obeys

  0 <= arctan(1/q) - E_n(q) <= t_n * d/(d-1),

where t_n is the next exact rational term. Since t_n <= q/d^(n+1),
a sufficient upper bound is q/[d^n(d-1)].
A schedule using q/[d^(n+1)(d-1)] is UNSOUND (off by one
factor d). The script uses the correct conservative bound.

## Exact paired Taylor terms
  term(2j)+term(2j+1)
    = [(4j+3)q²-(4j+1)] /
      [(4j+1)(4j+3)q^(4j+3)].

The regression proves these paired finite sums equal original even
Taylor prefixes exactly for tested rational inputs. The generic
P/Q/T tree evaluates the rationally paired hypergeometric ratios.

## Local observed wall-time comparison
Python exact rational evaluator, seven-run median, same local machine.
No Agda compiler was available. These times are not guaranteed
on other environments and depend on repeated allocations and backend.

| Decimal digits | Taylor P/Q/T (ms) | Paired P/Q/T (ms) | Euler P/Q/T (ms) |
|---:|---:|---:|---:|
| 100 | 0.041 | 0.040 | 0.038 |
| 1,000 | 0.758 | 1.058 | 0.723 |
| 3,000 | 4.312 | 7.140 | 4.063 |
| 10,000 | 34.663 | 57.493 | 31.886 |

The paired tree was slower at high precision despite halving its leaf
count; denser ratio numerators/denominators outweigh reduced tree
overhead in this baseline. Euler delivered ~1.09× at 10,000 digits,
not ~4–5×. The measured reduction in term count is 9,253 to 9,170
at 10,000 digits. These are isolated term evaluation timings: total
certificate cost requires interval construction and checking.

## Formal boundaries
- Reuse `BishopMachinArctanConstructionExact` and existing
  `BishopArctanHalfBallInterlacingExact` for the same-original Taylor
  series; do not invent a duplicate Bishop real.
- Paired Taylor: prove exact finite regrouping and split evaluation
  equivalence. This needs no new analytic identity.
- Euler: construct `bishopEulerAtan` as a Cauchy limit with positive
  term/tail bound; independently prove `bishopEulerAtan ≃ bishopAtan`
  by an Euler transform of the actual arctangent series or derivative/
  integral identity and identical initial condition. Mere numerical
  interval overlap up to any fixed cutoff cannot prove this.
- Original period `MachinQuarterAnalyticInputs`, C3 modular equations,
  Chudnovsky modular identity, and YM.REAL remain open.
- No Agda kernel typechecking or proof closure claimed.

This adds `scripts/check_bishop_fast_pi_euler_pair.py` as an
independent experimental/checkable reference only.
