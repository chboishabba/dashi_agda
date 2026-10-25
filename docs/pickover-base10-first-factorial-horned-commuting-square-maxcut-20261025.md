# Pickover factorial phase: base-10-first max-cut (2026-10-25)

## Original goal and authorial status
The classical problem is to determine the sign of sin(99^(9999!)). The classical
identity sign sin(N)=(-1)^floor(N/pi) for integer N>0 reduces the problem to
a single quotient-parity bit. No solution of that terminal bit is claimed.
The numerical experiments and certificate interfaces below are DASHI
consumers of classical Machin arctangent and Chebyshev identities; neither
identity is original to DASHI.

## Actual same-object target
N=99^(9999!), alpha=1/(2*pi).
Prove one of the equivalent inequalities
  {N*alpha} in (0,1/2), or {N*alpha} in (1/2,1).
The exact rational-interval checker already formalises the finite verification
of a supplied pi enclosure. It does NOT efficiently produce an enclosure of
the needed width at this exponent.

## Base-10-first laboratory; do not mix with 99 or 9999 rounds
Study A(k)=sin(10^k), then A(n!) and the genuine factorial jump
  10^((n+1)!) = (10^(n!))^(n+1).
Use signed Chebyshev U9 and C3/torque observer only as exact type/transition
maps. Test against **independently certified** rational Machin signs.
  python3 scripts/check_pickover_base10_factorial_maxcut.py
Locally PASS, exact integer calculations, no floating-point sine:
  k=1:-,2:-,3:+,4:-,5:+,6:-,10:-,20:-,
  24:-,30:-,40:-,50:-,100:-,120:-,
  720:+,999:+,1000:+,5040:+.
Within factorial subsequence the signs at n=1..7 are
  [-,-,-,-,-,+,+].
The same zero mod 10 occurs at k=2 and3 (opposite signs),
and at factorial k=120 and 720 (opposite signs).
Therefore zero 10-adic image does not determine the real sine sign.
Any proposed jump algorithm must beat the exact rational baseline and prove
its same-phase orientation invariant; fitting signs is not evidence of proof.

## Concrete prior-art reuse and limits
- Horned-C3 parent PR #1244: nontrivial infinite-order abstract group / finite
  quotient non-descent and C3 action. Its specific infinite-order theorem does
  not impose the order on the real unit-circle orbit e^(i*10^k), nor produce
  a 2*pi argument certificate.
- JInvariant369ReflectionEquivarianceExact: existing commuting-square *interface*
  for reflecting a continuous phase and negating finite C3/9/27 states.
  It does not assert that the quantiser intertwines z->z^10 or z->z^99.
- OggSSPP2BalancedTernaryPuncturedPlaneExact: punctured nine has 8 nonzero
  points; two copies have cardinality 16. No ring isomorphism to hex digits,
  BBP extractor, or inverse-pi digit random access follows from cardinality.
- BishopMachinPiRationalWindowExact: actual constructive Machin pi intervals;
  source-root Machin 1706 and Bishop/Bridges 1985 retain original credit.
- FinitePrimeProductSieveExact: exact integer residue coordinates. No map from
  integer CRT residues to the ordered real quotient floor(N/pi) mod 2.
- JInvariantBishopTrigUnitPhaseExact and JInvariantBishopQFromUnitPhaseExact:
  phase unit certificates; E4/E6 convergence needs |q|<1 and the actual target
  q=e^i lies on |q|=1. A radial regularisation preserves sign when it is
  known, but does not compute it.

## Highest alpha remaining, with falsification requirements
1. Identify a particular same-object continuously rendered phase and prove
   the analytic reflection/real sine-sign observer at base 10, source-driven.
2. Find/test a compact sufficient fine-state S(k) for jump k->m*k, and reject
   finite observers via same-residue opposite-sign fixtures.
3. Search for source-specific analytic extraction of the floor parity at
   position 9999!, including effective irrationality lower bounds that pay
   an explicit finite precision budget; a general bound is not itself a
   sublinear algorithm.
4. Transfer a proven base10 factorial-jump theorem to base99 with **all
   hypotheses explicitly paid**, never by numeral/carry analogy.
5. Establish exact-head Agda typecheck; current additions are source-written
   and local Python-tested only.

No sign for the original 9999!-exponent expression is established.
