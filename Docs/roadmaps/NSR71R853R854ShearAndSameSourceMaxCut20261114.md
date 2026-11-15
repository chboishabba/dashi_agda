# NS R71 → R853 → R854, physical source maximum cut (14 Nov 2026)

Owner: Agda PR #1501, Lean PR #109. The attachment is an argument
outline, **not** evidence that the claimed original-source declarations
have been inhabited and kernel-accepted. Do not promote an auxiliary
reserve countermodel into a global Navier–Stokes conclusion.

## 1. Reuse the strongest original owners

- `NSTriadKNFixedCanonicalRealityVectorFieldRound71Exact`: fixed geometry,
  original reality-preserving Galerkin right-hand side and conjugate
  negative-mode reconstruction.
- `NSTriadKNFixedCanonicalTransverseInvariantRound71Exact`: divergence-free
  mode subspace invariance.
- `NSTriadKNFixedCanonicalVectorFieldDegreeTwoRound71Exact`: literal
  original RHS agrees with a degree-at-most-two expression.
- `NSTriadKNFiniteRationalSlotAssignmentBridgeRound74Exact`: explicit
  finite rational chart and Round28 Lipschitz bound; the flag
  `round74PhysicalRHSAgreesWithFiniteChartPolynomial` remains false.
- `NSTriadKNR650Rational345RealODEMaxCutRound833Exact`: two independent
  remaining leaves are original physical RHS → complete-real finite
  quadratic ODE, and selected R828/rate transport on the same solution.
- `NSTriadKNR650CanonicalSelectedRateNormalFormRound853Exact`: for
  a live physical packet, the exact selected source functional is
  `r=6*(12*C-P+(2nu-delta)*D)`; at `nu=delta=1`,
  `r=6*(12*C-P+D)`. The real-trajectory weld is explicitly false.
- `NSTriadKNR650Rational345LipschitzIntegralRound854Exact` and
  `...RelaxedEnvelopeRound855Exact`: exact rational, conditional
  affine-envelope arithmetic, not construction of an actual real-time
  R853 rate.

## 2. Correct finite-dimensional Picard admissibility

The usual finite-dimensional theorem is applicable after a *true* source
equivalence to complete real coordinates. With
`F(u)=Au+B(u,u)+f`, `a=||A||`, `b=||B||`, `g=||f||`,
and ball `B_rho(u0)` contained in `||u||≤R=||u0||+rho`, derive

`||F(u)|| ≤ M(R):=aR+bR²+g`;
`||F(u)-F(v)|| ≤ (a+2bR)||u-v||`.

An explicit sufficient Picard interval has
`T ≤ min(rho/(2M(R)), 1/(2(a+2bR)))`
when the denominators are positive, with zero-denominator cases handled
separately. Existence on the source R854 interval additionally requires
`T_R854≤T` or an actual continuation theorem. The attachment's bare
`T*=1/[2(C_B||u0||+nu N²)]` suppresses radius, forcing and source
coefficient dependencies and is not a general original-source receipt.
Do not replace the original R830/R854 fixed horizon with an
independently selected shorter time and call it same-source.

## 3. The rate definition is NOT the displayed enstrophy balance

For smooth unforced 3D incompressible NS on the periodic torus,
the vorticity equation gives

`(1/2) d/dt ||omega||² + nu||grad omega||²
  = integral ((omega·grad)u)·omega`.

Hence the attachment's proposed quantity

`2<omega_t,omega> + 2nu||grad omega||²
  -2 integral ((omega·grad)u)·omega`

is identically **zero**, not the nonzero selected R853
`-28273644/125`. A forced equation has the relevant forcing
contribution and still is not the R853 normal form by definition.
The correct original-source work is to evaluate
`6*(12*C-P+D)` along the **same** real Galerkin solution,
prove its initial equality to R829, and differentiate this polynomial
under the actual chart and ODE.

## 4. A rigorous R823 shear negative control

The attachment proposes
`u_bad=(sin(Kz)+eps*cos(x)sin(Kz),cos(Kz),-eps*sin(x)cos(Kz))`.
The exact divergence is

`div u_bad = eps*(K-1)*sin(x)*sin(Kz)`.

For `K>1,eps≠0`, the claimed high-frequency field is not
incompressible; it is not an admissible example of the claimed flow.

The natural divergence-free correction is

`u=(sin(Kz)+eps*cos(x)sin(Kz), cos(Kz),
     -(eps/K)*sin(x)cos(Kz))`, `K∈ℕ_{>0}`.

It has only vertical Fourier frequencies `±K`. Any cubic integral
of three differentiated or undifferentiated components has no zero
vertical frequency (sum of three `±K` is never 0). Thus its initial
unforced cubic H¹ transfer is exactly zero, independently of
horizontal algebra.

For torus mean normalized to one:

`E=1+eps²(1+K^-2)/4`,
`G=K²+eps²(K²+2+K^-2)/4`,
`H=K⁴+eps²(K²+1)²(1+K^-2)/4`.

For the **specific attachment** reserve
`Phi=E+c log(1+G)` with `nu>0,c≥0` the exact initial rate is

`Phi'(0)=-2nu*(G+cH/(1+G))<0`.

Hence this corrected helical family does not furnish the asserted
positive-derivative reserve counterexample either. This does not
prove or refute the original *different* R823 universal reserve,
which must be inspected in its exact source type.

Reproduce 72 exact rational cases (no floats or extra libraries):
`python3 scripts/check_ns_r823_shear_negative_control_20261114.py`.
Example `K=2,eps=nu=c=1`: bad divergence coefficient 1,
corrected `E=21/16, G=89/16, H=381/16, Phi'=-5147/280`.
These are Fourier-algebra checks, not an Agda or Lean kernel receipt.

## 5. Still-open exact lemma producers, in required order

| Tier | Exact target | Source-specific acceptance |
| --- | --- | --- |
| A1 | `originalR71R74PhysicalRHSIsRealQuadraticField` | actual R71 field equals finite chart on complete `ℝ^M`, real order/norm/derivative transport |
| A2 | `originalR71RealGalerkinLocalSolution` | true C¹ flow of same projected vector field and same initial 345 datum on at least the R854 horizon |
| A3 | `originalR853SignedRateAlongGalerkinSolution` | pointwise same packet `C,P,D` equals original rate on the flow, including `r(0)=R829.expectedRate345` |
| B1 | `originalR828R854RateLipschitzAlongSolution` | `|r'(t)|≤L` or valid R855 relaxed bound on actual flow; verify constants, source (H^3) ball and all derivatives |
| B2 | `originalR854PhysicalRateEnvelope` | derivative FTC and same-object time interval |
| B3 | `nsR854OriginalRealRateIntegralStrictlyNegative` | integrate true R853 function; use already proved R854/R855 negative rational envelope |
| Separate | `originalR823UniversalReserveCounterexample` | test literal source R823 rate; proposed shear is INVALID for the stated claim |

**Acceptance:** pinned Agda 2.9 source root, Lean 4.28 proof checker,
transitive axioms/trust and no reserved physical hypothesis smuggled in
as an interface. **Current status: A1–B3 remain open; R823 proposed
example refuted as a *method*, original R823 result undecided.**
