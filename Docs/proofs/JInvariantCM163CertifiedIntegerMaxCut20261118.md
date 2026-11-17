# CM discriminant -163: exact short certificate and class-one proof
18 November 2026 — proof roadmap / source attribution / execution receipts

## Main result (rigorous arithmetic, conditional analytic binding)
For tau=(1+sqrt(-163))/2 and the classical modular j, the exact
outward-rounded 128-bit dyadic calculation proves

  K - 1/2 < j(tau) < K + 1/2,
  K = -262537412640768000 = -640320^3,

provided the standard Machin π identity, exponential interpretation
and normalized E4/E6 q-series are used as analytic source identities.
All numerical acceptance checks are integer/rational, NOT floating point.

The 128-bit certificate is:
  scale=2^128=340282366920938463463374607431768211456;
  lower = K - 121397398953732472506062368501224644 / scale;
  upper = K + 12147930101178244703017603450764613085 / scale.
Both deviation numerators are strictly less than scale/2.

A standalone Agda endpoint checker is now in
DASHI/Moonshine/JInvariantCM163DyadicHalfIntegerExact.agda:
it uses the existing pinned stdlib Nat decidable order to verify those
specific inequalities under --safe. It does NOT assert that the original
Bishop j lies within those bounds without a separate analytic producer.
Pinned compiler acceptance is still pending.

Increasing dyadic precision keeps the SAME integer K:
  128 bits: interval width approximately 0.0360563129119842
  160 bits: interval width approximately 8.395014543082611e-12
  256 bits: interval width approximately 1.44851224556475e-31.
Nine-run local median wall times for the core complete fixed-precision
certificate: 128 bits 0.801 ms, 160 bits 0.819 ms,
256 bits 0.988 ms (Python built-in integer arithmetic, warm runs).
No Agda kernel benchmark is implied. Independent 100-digit mpmath
q-series evaluation landed inside the exact interval but is NOT relied
on for acceptance.

## Analytic calculation and tail proof
Take q=exp(2πiτ)=-exp(-π sqrt(163)) with |q|=r.

Obtain rational π bounds from the original two-term Machin arctan
alternating series at (90,30) terms and sqrt(163) from
floor(sqrt(163 * 2^(2b))) / 2^b and the next dyadic endpoint.
Exponential series partial sums are positive. With N=180 and
x <= π sqrt(163)<(N+1)/2, the positive tail is bounded by
twice the N-th term. Inverting the positive exp interval gives r,
and q=-r is enclosed.

The literal normalized weight 4/6 series are

  E4(q)=1+240 Σ_{n>=1} σ3(n) q^n,
  E6(q)=1-504 Σ_{n>=1} σ5(n) q^n,

whose first 3 divisor sums are σ3=(1,9,28),
σ5=(1,33,244).

For k=3,5: σk(n)<=n^(k+1). For n>=4 and r<1/128,
successive majorant ratios are at most 2^(k+1)r<1/2.
Therefore the missing tail is bounded by

  |E4 - E4_prefix3| <= 2*240*4^4*r^4,
  |E6 - E6_prefix3| <= 2*504*4^6*r^4.

At every stage, interval multiplication/division uses 2^b scaling,
rounding lower down and upper up, including reciprocal of a strictly
negative discriminant interval. The script asserts the computed
discriminant upper bound <0 before dividing.

The target j is then evaluated as
  1728 E4(q)^3 / (E4(q)^3-E6(q)^2).

The arithmetic verification is fully reproducible with:
  python3 scripts/check_cm163_dyadic_j_integer_certificate.py
It runs 128,160,256 bits by default.

## Exact proof that the discriminant -163 has class number 1
Use standard reduction of positive-definite primitive binary quadratic
forms (a,b,c) with discriminant b²-4ac=-163. Every reduced form
has |b|<=a<=c and 3a²<=163, so 1<=a<=7; b must be odd.
Then 4a divides b²+163.

For each a>=2, allowed odd |b| and the residues of b²+163 mod 4a:
  a=2: b=1 => 4 mod 8
  a=3: b=1,3 => 8,4 mod 12
  a=4: b=1,3 => 4,12 mod 16
  a=5: b=1,3,5 => 4,12,8 mod 20
  a=6: b=1,3,5 => 20,4,20 mod 24
  a=7: b=1,3,5,7 => 24,4,20,16 mod 28.
None is zero. At a=1, b=±1 yields c=41;
the standard reduced-form tie-break retains (1,1,41).
Thus the unique proper reduced class is [(1,1,41)] and h(-163)=1.

This finite arithmetic is independently exhaustively checked by the
Python script; Agda proof of exhaustiveness and reduction equivalence
remains a typed task, not silently attributed to the integer checker.

## Why this implies the *exact* singular modulus
The classical complex multiplication theorem states: a modular
singular j-value for an imaginary quadratic order is an algebraic
integer, and its degree over Q is the class number. For fundamental
D=-163, h(D)=1, so the actual j(tau) is an INTEGER.
A proven real enclosure of width <1 contained in (K-1/2,K+1/2)
therefore forces j(tau)=K exactly.

This route avoids directly calculating the huge constant term of
the Hilbert class polynomial. Its remaining Agda math debt is:
  * the original Bishop π/period and exp identifications;
  * q-series-to-lattice E4/E6 and standard-j same-object;
  * certified dyadic arithmetic soundness;
  * actual CM algebraic integrality and degree/class-number theorem;
  * exact finite reduced-form exhaustion and its correspondence
    to the original imaginary quadratic order;
  * pinned full --safe compiler acceptance.

The executable calculation is a certified ARITHMETIC interval.
It is not a kernel-checked CM theorem until those analytic premises
are linked in Agda.

## Complexity / MDL proxy
At fixed precision b the core series uses 90+30 Machin terms,
180 exp terms, and 3 E4 + 3 E6 terms; dyadic operations use
integer division and multiplication on O(b)-bit or O(2b)-bit
intermediates, excluding the finite exact Fraction Machin prefix.
Generic arithmetic scales with the costs of integer multiplication
M(b), and faster binary-split Machin can replace the reference
π prefix without changing the final arithmetic certificate.
The 128-bit endpoint witness needs just two signed offset magnitudes
plus 128-bit scale metadata; do not mislabel this as measured
Kolmogorov complexity of π or j.

## Primary references / attribution
Eisenstein modular forms and Klein-j: Serre (1973), Miyake (2006).
Dedekind eta and discriminant: Apostol.
Classical complex multiplication and imaginary quadratic class
polynomials: standard CM theorem, see
https://flintlib.org/doc/acb_modular/class-polynomials.html.
Repo source owners: JInvariantAnalyticNormalizedKleinAdapterExact,
JInvariantBishopLatticeEisensteinSameObjectCompilerExact,
LeanMoonshineDeltaIdentityPinnedReceiptExact,
BishopMachinArctanConstructionExact, BishopNatSquareRootSemanticSquareExact.
