# YM R445 interacting Wilson: common-density maximum cut (14 Nov 2026)

## Already-built original source owners

- YMClayE1D1OriginalR445QuantitativeThreeMomentRGCutExact.agda
  already bounds original covariance error by the three RG
  moment errors epsilon_F, epsilon_G, epsilon_FG.
- YMClayE1D1OriginalR445BoundedMomentMajorantsExact.agda
  already constructs unit-bounded coarse test F,G,FG and the
  explicit nonnegative complement to the product FG.
- YMClayE1A3OriginalR445CrossCutoffSourceExact.agda owns the
  original effective 3→1 blocked pushforward source.

Do NOT identify effective and bare original Wilson Gibbs laws.

## One same-carrier physical inequality controls three moments

On an actual finite common original coarse carrier X, denote the
normalized interacting Wilson effective and bare laws by P,Q.
Define D=(1/2)sum_x |P(x)-Q(x)|. Their signed difference sums to
zero, so its positive and negative parts EACH sum to D.
For any F:X→[0,1], -D <= sum_x(P-Q)F <= D.
The original bounded product closure gives 0<=FG<=1.
Thus all THREE errors for F,G,FG are bounded by the SAME D.
The existing original three-moment theorem then yields

  |Cov_P(F,G)-Cov_Q(F,G)| <= 3D.

No actual physical estimate for D was established by this
elementary probability inequality.

## Pointwise relative-density source alternative

Suppose original unnormalized physical Wilson effective/bare
coarse weights wP,wQ are positive and on the SAME X, and
0<=eps<1 with

  1-eps <= s(x)=wP(x)/wQ(x) <= 1+eps  FOR EVERY x.

Let Z=E_Q[s]. Then 1-eps<=Z<=1+eps and the normalized
density ratio r=s/Z has E_Q[r]=1 with

  m=(1-eps)/(1+eps) <= r <= M=(1+eps)/(1-eps).

For r in [m,M], (r-1)_+ is bounded by the chord joining
(m,0) and (M,M-1). Therefore

  TV(P,Q)=E_Q[(r-1)_+]
   <= ((M-1)*(1-m))/(M-m) = eps.

Consequently all three original bounded moment errors are <=eps,
and the original R445 covariance error is <=3eps.

This is only an if-then result: the actual effective-to-bare
Wilson density ratio bound remains a physical RG obligation;
the RG coupling renormalisation may make it false or nonvanishing
for a fixed unmatched bare coupling.

## Explicit nonbare negative control

Take X={0,1}, Q=(1/2,1/2), P=(3/4,1/4),
F=G=indicator of state 0. Then

  Cov_Q(F,G)=1/4, Cov_P(F,G)=3/16,
  absolute covariance mismatch=1/16.

This finite source counterexample can repeat at every cutoff;
a finite blocked pushforward alone DOES NOT imply matching
the original bare law or closing continuum E1/D1.

## Reproduce

  python3 scripts/check_ym_r445_relative_density_three_moment_cut.py

The script uses exact Python Fraction arithmetic.
No Agda 2.9 kernel receipt was produced for this new lemma.
The original physical cutoff-uniform R445 bound, interacting E1,
D1 decay, D2 same-H spectral gap and Clay YM remain OPEN.

Highest-alpha next: estimate actual D at each cutoff, or prove a
uniform effective/bare Wilson density-ratio bound, from the
original fully interacting n=3 blocked density against the
n=1 bare Wilson weight. Verify the same F,G,FG tests and
renormalized action/coupling at the source, not just a generic
probability surrogate.
