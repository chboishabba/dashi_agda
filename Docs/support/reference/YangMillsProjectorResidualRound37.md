# Yang–Mills Round 37 — projector, residual, reversal and certificate route

## Status

This round is stacked on Round 36 / PR #470. It implements the proof-bearing portions of the cross-lane proposal without promoting analogies to physical theorems.

The finite Wilson pair and deep channels remain closed as in Round 36. The remaining Gate-I analytic task is still the selected-background local variation, but its shape is now substantially more concrete:

```text
raw four-bond plaquette extractor
  -> finite physical projector
  -> gauge / constraint / Euler residual cancellation
  -> raw-localization plus projector-defect spillover
  -> 55/18874368 cross-charge budget.
```

No successful Agda-kernel result is claimed until the cumulative root is observed to pass.

## Literal physical coordinate projector

`BalabanP33PhysicalCoordinateProjectorExact.agda` constructs a diagonal Boolean-mask projector on the repository’s actual 3,072-coordinate side-four SU(2) carrier.

For a mask `m`,

```text
(P_m v)(x) = m(x) v(x).
```

The module proves:

```text
P_m(P_m v) = P_m v
<u,P_m v> = <P_m u,v>
P_m v = v  <->  v vanishes outside m
(P_m M P_m)v = P_m(M(P_m v))
v^T(P_m M P_m)v = (P_m v)^T M(P_m v)
```

It also proves the literal constrained resolution

```text
P_m v = sum_x (P_m e_x) v_x
```

from the repository’s existing physical basis and identity kernel. Thus a projected Hessian matrix and its form compatibility are derived from one projector rather than supplied independently.

## Four-bond plaquette boundary projector

`BalabanP33PlaquetteBoundaryProjectorExact.agda` constructs the actual local mask for

```text
U_mu(x) U_nu(x+mu) U_mu(x+nu)^-1 U_nu(x)^-1.
```

All three Lie coordinates on exactly those four positive bond cells are retained. The raw local extractor is

```text
w_(p,h) = P_boundary(p) encode(h).
```

Its support/image theorem, idempotence, self-adjointness and basis resolution are proved.

This is a real construction. It is not yet the gauge-admissible, constraint-tangent selected variation.

## Commuting projector composition

`BalabanP33PhysicalProjectorCompositionExact.agda` proves that coordinate-mask intersection realizes commuting composition:

```text
P_(m and n) = P_m P_n = P_n P_m.
```

The triple mask

```text
P_constr = P_gauge P_tangent P_boundary
```

is therefore idempotent and self-adjoint whenever the three physical conditions are represented by diagonal coordinate masks. The image is the intersection of the three component images.

This does not claim that the eventual covariant Hodge/gauge projector is diagonal. If it is non-diagonal, its commutator and order must be proved separately.

## Exact projector spillover identity

`BalabanSelectedVariationProjectionSpilloverExact.agda` represents the first variation by a literal finite covector. For raw extractor `w` and mask projector `P`, define

```text
discarded = (I - P) w.
```

Finite dot-product algebra proves

```text
dA(w) = dA(Pw) + dA(discarded)
```

and hence

```text
dA(Pw) = dA(w) - dA(discarded).
```

If

```text
dA(w) = singleton + rawLocalizationSpillover,
```

then

```text
dA(Pw)
  = singleton
    + (rawLocalizationSpillover - dA(discarded)).
```

The two owned bounds

```text
rawLocalizationSpillover <= alpha C_p(h)
-dA(discarded)          <= beta  C_p(h)
alpha + beta = 55/18874368
```

are combined exactly into the Round-36 singleton budget.

Thus the unresolved estimate is no longer an opaque `spilloverUpper` field: it is the sum of a raw localization estimate and a physical projector-defect pairing estimate.

## Same-object Noether residual reduction

`BalabanSelectedVariationProjectedNoetherResidualExact.agda` requires the projected variation itself to carry:

```text
gauge admissibility
constraint tangency
local support
charge control
```

and decomposes its first variation as

```text
gauge residual
+ constraint residual
+ selected Euler residual.
```

Separate vanishing proofs imply stationarity. A second exact equality identifies the same first variation with the literal four-singleton Wilson term plus the projector/localization residual.

The module then constructs the existing Round-36 `SingletonExtractionWitness`, the full selected-background variation selector, and therefore the singleton lower-bound reducer.

The following remain physical analytic inputs:

```text
selectedPhysicalGaugeProjector
selectedConstraintTangentProjector
projectedGaugeAdmissible
projectedConstraintTangent
rawLocalizationSpilloverUpper
projectorDefectPairingUpper
```

## Orientation reversal

`BalabanP33PlaquetteOrientationReversalExact.agda` proves over exact rational quaternions:

```text
conj(conj q) = q
conj(qr) = conj(r) conj(q)
conj(q-r) = conj(q)-conj(r)
```

and therefore

```text
conj(a0 a1 a2 a3)
  = conj(a3) conj(a2) conj(a1) conj(a0).
```

The scalar Wilson value is invariant. The theorem is factor-pattern agnostic and applies to singleton, pair, triple and quartic subset atoms. This supplies the algebraic core of positive/inverse-orientation reuse; geometric plaquette reversal and selected-variation covariance remain separate constructions.

## Sixteen-atom centred probe

`BalabanWilsonSixteenAtomCentredProbeExact.agda` proves the division-free identity

```text
16 sum_i w_i (b + delta_i)
  = (sum_i w_i)(16 b + sum_i delta_i)
    + sum_i (16 w_i - sum_j w_j) delta_i.
```

Uniform weights annihilate the centred coefficients. This unifies augmentation and placement-defect audits without claiming that any currently configured physical coefficient is optimal.

## Finite spectral certificate

`BalabanP33LiteralHessianSpectralCertificateExact.agda` proves that an exact finite eigenpair satisfies

```text
v^T M v = lambda ||v||^2.
```

A supplied quadratic floor `M >= c I` therefore yields `lambda >= c` for every normalized eigenvector. With `c=1/32`, a normalized zero eigenvector is impossible.

This is a finite regression/certificate theorem. It does not construct the literal selected-background Hessian or replace its analytic coercivity proof.

## State / covector Combes–Thomas adapter

`BalabanP33PhysicalStateDualTiltExact.agda` makes the physical state and test-covector roles explicit and proves

```text
M_mu(x,y) = W_mu(x) M(x,y) W_mu^-1(y),
M_mu(x,y)-M(x,y)
  = (W_mu(x)W_mu^-1(y)-1) M(x,y).
```

The weight maps are exact pointwise inverses. A zero Hessian entry remains zero after tilting. This reuses the existing physical Combes–Thomas proof rather than introducing a new decay assumption.

## Maximal cores and owned RG losses

`BalabanP33StrictOwnedMarginExact.agda` provides two later-Gate patterns.

A decomposition

```text
commonCore + scaleResidual = available,
scaleResidual >= 0
```

proves every such core is at most `available`; the zero-residual candidate attains it.

The one-step RG loss owner type is explicitly:

```text
coarse block
fluctuation inverse
coarse/fine derivative
small-field nonlinear
large-field polymer
boundary collar
gauge projection
```

`StrictOwnedMargin` requires exact erasure/reconstruction of the physical remainder and the actual strict inequality. It does not manufacture contribution estimates or the target `32 E_k < 2 - theta_k`.

## E8 quantitative root data

`BalabanE8QuantitativeRootDataExact.agda` connects existing repository values:

```text
112 + 128 = 240 roots
rank = 8
dimension = 248
dual Coxeter number = 30
8 + 240 = 248.
```

This is useful algebraic data for the all-compact-simple-group gate. It does not construct the compact real form, Haar measure, BCH constants, chart radius, selected background or RG theorem for E8.

## Typed 196608 atlas

`BalabanCommon196608AtlasExact.agda` records three distinct typed charts:

```text
24 * 8192       = 196608
3 * 65536       = 196608
196560 + 24 + 24 = 196608
196608 + 276    = 196884.
```

The chart constructors are distinct. Equality of the integer does not provide a coordinate map, operator intertwiner, representation isomorphism or physical defect transport.

## Current highest-alpha cut

The shortest Gate-I producer is now:

```text
1. construct the selected physical gauge/Hodge projector;
2. construct the selected constraint-tangent projector;
3. prove the projected boundary extractor is admissible and local;
4. prove rawLocalizationSpilloverUpper;
5. prove projectorDefectPairingUpper;
6. split their coefficients with alpha + beta = 55/18874368.
```

Those inputs construct the Round-36 selector and therefore produce

```text
H_A[h,h] >= 10739/196608 ||h||^2 >= 1/32 ||h||^2.
```

After Gate I, the highest-alpha physical work remains the literal selected-background Hessian/stencil/right inverse and the already-prepared Combes–Thomas endgame, followed by one genuinely scale-uniform RG step.

## Validation

```bash
AGDA_JOBS=1 bash scripts/check_yang_mills_clay_highest_alpha_round37.sh
```

The checker cascades through Round 36, rejects holes and trust escapes, checks provenance and theorem surfaces, and invokes the cumulative Round-37 Agda root.
