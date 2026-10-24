## 2026-10-24 additional A max-cut: full-frequency physical H¹ source majorant

The low-frequency-only estimate has a second, already-standard,
same-source physical input. Let `u∈H¹(R³)^3` be distributionally
divergence free, `E=||u||²_L²`, and `D=||grad u||²_L²`.

1. Divergence form and `u⊗u∈L¹` give
   `|F[P div(u⊗u)](xi)| ≤ E*|xi|`.
2. The original smooth-field identity
   `div(u⊗u)=(u·grad)u` extends as an `L¹` identity for
   `u∈H¹`. Pointwise
   `|(u·grad)u|≤|u|*|grad u|`; Cauchy–Schwarz implies
   `||div(u⊗u)||_1≤sqrt(E*D)`.
   Fourier boundedness and Leray contraction give
   `|F[P div(u⊗u)](xi)|≤sqrt(E*D)`.
3. Therefore, with the **same physical source** and `nu>0`,

```text
source(xi) <= min(E*|xi|, sqrt(E*D)).
heat_inverse(xi) <= (1/nu) min(E/|xi|, sqrt(E*D)/|xi|²).
crossover r_* = sqrt(D/E) (if E,D>0).

int_(R3) |heat_inverse(xi)|² dxi
 <= (4*pi/nu²) [
      int_0^r_* E² dr
      + int_r_*^∞ (E*D/r²) dr
    ]
 = (8*pi/nu²) E^(3/2) sqrt(D).
```

This **globally square-integrable** direct stationary viscous-response
majorant controls both zero and infinite frequency from finite energy
and enstrophy, without an arbitrary Fourier flux field and without
a nonintegrable positive independent-R9 Gram pair. Its physical
space norm differs by the conventional inverse-Plancherel factor
`(2*pi)^(-3/2)`, since the convention is the unnormalized
`Ff(xi)=int exp(-ix·xi)f(x)dx`.

Source proof combines elementary standard Plancherel/Fourier-product
continuity, divergence-form identity, Hölder and radial integration.
Exact symbolic crossover/integral arithmetic was independently
checked locally and is asserted in
`scripts/ns_a_schwartz_fourier_same_object.py` and its test.
This is **not a new global regularity theorem**: the bound depends
on D(t), which is not known uniformly in time in the desired
regularity conclusion. Nor does it automatically control the canonical
A2 signed *centered double resolvent* or ensure the A3 continuation
criterion. The next meaningful A cut is to replace the old
source-free Bishop `FourierTransformVelocity:Set` field by a checked
Plancherel/distribution Fourier source, and weld these direct
physical low/high bounds into the actual signed A2 estimate on the
same continuum solution. Avoid repeatedly deriving heat/Young algebra.

---

## 2026-10-24 max-cut continuation — B4 ED no-go discharged, A finite-energy Fourier source identified

### Algebraic single-row padding mechanism (source-shaped Lean receipt)

Existing non-Round `dashi_lean4/NSUnforcedAnalyticCuts.lean` now
contains `physicalR440_zero_padding_increment` and
`physicalR440_shear_padding_increment`. They isolate the precise
four-moment defect rather than merely plotting growing tables.

Writing `V_X=W(M,M_X)` for raw modal mixed sums and
`W_X=W(M,R_X)` for weighted R440 sums, the literal negative
noncore/core work is

```text
D_NC = -[ n_C*W_N + n_N*W_C - r_N*V_C - r_C*V_N ].
```

Appending a ZERO-amplitude noncore cell at input rate `s`
leaves `W_N` and `V_N` unchanged but changes
`n_N -> n_N+1`, `r_N -> r_N+s`; therefore the EXACT
one-row change is

```text
D_new - D_old = s*V_C-W_C.
```

For the smooth physical shear, `V_C=1,W_C=2`, so each added
zero-amplitude noncore cell adds precisely `s-2` to the B4
signed defect. This algebraic result explains the failure on the
literal **same-object** R440 four-fold source. A positive replacement
must eliminate the unphysical dependence on zero-amplitude
incidences while retaining an exactly proved connection to NS
critical production. It is not enough merely to restrict an
arbitrary `FiniteSet` or rename a signed covariance.

The Lean terms were committed, but exact-head Lean kernel receipts
were NOT produced; the corresponding rational four-moment identity
was independently checked and pinned in
`tests/test_ns_b4_literal_padding_adversary.py`.

### B4: the ED qualification has been paid by existing theorem owners

The canonical B4 full-output-fibre source reduction is still the exact
Agda algebra. Its proposed `theta_D<1/2` physical ED payment is **false**
when `localED` is the already-defined genuine R219/R469/R109
selected-pair currency, on the fixed globally smooth shear state
from the adversarial section below:

- `R219.physicalModalED`: `E_m=||u_hat_m||²` and
  `D_m=|m|²||u_hat_m||²`.
- `R109.pairKernel(p,q)=D_p E_q+E_p D_q`; `R469.selectedTriadValue`
  and `PhysicalCriticalRegionUniformFamilyProducer.localED` fold
  this **nonnegative** kernel over one output fibre.
- Only four modes are populated (`±e_x,±e_y`), each having E=D=1;
  `sum E=sum D=4`. The global R109 selected-pair ED is `<=32`.
- At `k=e_x+e_y` ONLY two ordered physical pairs can contribute:
  `(e_x,e_y)` and `(e_y,e_x)`, each with pair kernel `2`.
  Therefore `0<=localED_N(k)<=4` for **every cutoff N** and
  every Boolean selector (independently of shell and helicity).
- The previous strict-source R63 corrected computation has
  `M_core_N=1345859672` for all `N>=9`, while
  `defect_N>=2*sum_(m=10)^N m(m-1) -> +infinity`.
  Consequently no cutoff-independent finite `c_D>=0` and
  `0<=theta_D<1/2` can satisfy
  `defect_N <= theta_D*M_core_N+c_D*localED_N(k)`.
  This is a **mathematical no-go for the original full-fibre auxiliary
  B4 inequality**, not an unforced Navier–Stokes counterexample.

At N=40, merely permitting `theta_D=1/2` (weaker than the demanded
strict inequality) already forces `c_D >=249560621` from localED<=4.
No fixed `c_D` suffices as N grows.

**Do not spend another cut trying to prove that estimate.** In the
existing physical owner, preserve the exact literal R440 aggregate
`R= sum_tau inputMass(tau)*A_tau`, which is invariant under padding
with `A_tau=0`. The fixed witness has `R=2M`, while
`|k|²=2`, so its actual output-relative heat work
`W(M,R-|k|² M)=0`, despite the divergent full-fibre covariance.
The next positive-B theorem must prove an exact *same-source* identity
between a proposed zero-padding-invariant physical quantity and the
original NS critical production; a new weighted covariance cannot be
substituted merely because its bound looks easier. B1/2/3, B7 and B
continuation remain open. The generic PR #1234 B4 interface permits
a freely specified source-attachment predicate, so it must **not**
override this fixed physical ED negative result.

**New executed receipt:** the independently evaluated local script
`ns_b4_padding_no_go.py` reproduced N=4,8,9,16,24,36,40 exact
full-fibre values, and the source/maths ED bound was checked directly.
Source changes:
`scripts/ns_b4_literal_padding_adversary.py` and
`tests/test_ns_b4_literal_padding_adversary.py`; committed tests
themselves still require a normal checkout run. No kernel proof
receipt from these Python checks.

### A1/A2: actual finite-energy continuum Fourier source theorem

There is MORE already-paid A source than the old A1 status implies:
`NSTriadKNEuclideanCanonicalProjectedInteractionExact` constructs the
pointwise divergence-form/Leray cell, and
`NSWholeSpaceFiniteConvolutionSingleLimitExact` reduces product
convergence to one energy quadrature. No more raw-cell records.

The following *standard Fourier/Plancherel lemma* provides an exact
mathematical physical-state producer, not just a chosen `Set` meaning:

Let `u:R³->R³` be divergence-free in distributions with
`u in L²(R³)`, and set `E=||u||²_L²<∞`. Then
`u_i*u_j` (POINTWISE product) is in L¹. Write
`G_ij(xi)=F[u_i u_j](xi)` for
`Ff(xi)=∫exp(-i*x·xi)f(x)dx`.
It has a continuous bounded representative and
`||G(xi)||_F <= ∫||u(x)⊗u(x)||_F dx = E`.
For Schwartz `u`, Fourier inversion and Fubini yield the **same**
original Fourier interaction

```text
G_ij(xi) = (2*pi)^(-3) int_eta uhat_i(eta) uhat_j(xi-eta) d eta
F[div(u⊗u)]_i(xi) = i*sum_j xi_j G_ji(xi)
F[P div(u⊗u)]_i(xi) = i*sum_j (P_xi)_(i l) xi_j G_(j l)(xi),
P_xi = I - (xi xi^T)/|xi|², xi!=0.
```

Approximate an arbitrary finite-energy `u` in `L²` by Schwartz
`u_n`: `u_n⊗u_n -> u⊗u` in `L¹`, and their Fourier convolutions
converge uniformly pointwise by L² Cauchy–Schwarz/Plancherel.
Thus the same identity holds as a *tempered distribution* for
finite-energy `u`, even where `uhat` has no pointwise classical
values. This is the relevant same-solution **physical Fourier
identification**, mathematically rigorous with standard Fourier
normalization; constructing the corresponding Agda Bishop
Fourier/Plancherel semantics and a kernel receipt is still unpaid.

By Leray contraction `||P_xi||op<=1`,
`|F[P div(u⊗u)](xi)| <= E|xi|`.
For positive viscosity `nu`, the actual viscous-heat inverse has
near-origin bound `E/(nu*|xi|)`; in THREE dimensions

```text
int_(|xi|<=R) (E/(nu*|xi|))^2 dxi
    = 4*pi*R*(E/nu)^2 < infinity.
int_(|xi|<=R) E/(nu*|xi|) dxi
    = 2*pi*R^2*E/nu.
```

This supplies a **genuine finite-energy low-frequency bound for the
physical projected nonlinear source**, no artificial positive R9
Gram-pair integral and no L⁴-frequency hypothesis. It does NOT by
itself control the more complicated canonical signed *centered
resolvent* correction, nor the high-frequency tail or global
continuation. Those are the precise remaining A2/A3 consumers.

**Concrete nontrivial witness:** committed
`scripts/ns_a_schwartz_fourier_same_object.py` and
`tests/test_ns_a_schwartz_fourier_same_object.py` calculate the
R³ Schwartz divergence-free datum
`u=(-2y,2x,0)exp(-|x|²)`, its transform
`uhat=i*pi^(3/2)(xi_y,-xi_x,0)exp(-|xi|²/4)`,
and both a spatial-derivative and centered Gaussian-convolution
derivation of
`F[(u·grad)u]=i*(pi/2)^(3/2)*(xi_x,xi_y,0)exp(-|xi|²/8)`.
The actual Leray projection is nonzero at `xi=(1,0,1)`;
`||u||²_L²=2*(pi/2)^(3/2)`,
`||grad u||²_L²=10*(pi/2)^(3/2)`.
The exact symbolic spatial/convolution and finite-energy calculations
were independently checked locally. This is a one-datum A1
calibration, not unrestricted NS regularity.

**Immediate real remaining acceptance cut:** instantiate the
Fourier/Plancherel distribution identity on the SAME canonical
`EuclideanFourierTrajectory` without `FourierTransformVelocity:Set`
being freely chosen; then attach actual A2 signed kernel and
low/high majorants. Do not create any new RNNN modules.

---

## 2026-10-24 P0 B4 adversarial discovery and A prior-art recut

**SOURCE CORRECTION:** The official R63 scale classification uses the STRICT
shell gap `j_low+3 < j_high` and `j_output+3 < j_p,j_q`. An initial
non-strict local enumeration was superseded; only the corrected N9-N40
receipts below are admissible.

**STOP treating the original full-output-fibre B4 estimate as merely an
unpaid Young inequality.** An exact physical finite-mode negative control now
exists. Its status is **executed finite arithmetic plus analytic unboundedness
argument**; no Agda/Lean kernel proof or Clay theorem promotion.

### Literal B4 zero-padding counterexample (physical, real, transverse)

Source owner:
`NSTriadKNPhysicalCriticalTouchingDefectR44020261007Exact.agda`
(fixed mixed helical amplitudes and R440 input-rate vector) together with
`NSTriadKNPhysicalCriticalTouchingDefectNoncoreCore20261007Exact.agda`
(negative bipartite covariance) and
`NSTriadKNPhysicalCriticalTouchingLiteralCompanion20261007Exact.agda`
(literal Core-Core Young companion).

Fix viscosity `nu=1`, output `k=(1,1,0)`, and a zero-mean real,
divergence-free physical field

```text
u_hat(+e_x)=u_hat(-e_x)=u_hat(+e_y)=u_hat(-e_y)=e_z
u_hat(other k)=0.
```

Equivalently on the 2*pi-periodic torus
`u_0(x,y,z)=2(cos(x)+cos(y)) e_z`. This is even an **exact globally
smooth shear solution** `u(t)=exp(-t)*u_0`: since `partial_z u=0` and
`u` has only a z component, `u.dot.grad u=0`; with `-Delta u_0=u_0`,
the PDE is the heat equation (constant pressure). Thus the adversary is
not an inadmissible arbitrary packet.

At `k=e_x+e_y` there are exactly TWO active ordered mixed-helicity
cells `(e_x,e_y),(e_y,e_x)`, both Core, with literal rate
`r=|p|^2+|q|^2=2`. Genuine norm-one helical projectors give

```text
A=(-i/4,-i/4,+1/4), B=(-i/4,-i/4,-1/4)
M=A+B=(-i/2,-i/2,0), ||M||^2=1/2
w_A=w_B=2Re<M,A>=1/2
```

All other incidences in the FULL cutoff output fibre have zero mixed
amplitude, but continue contributing to `n_N` and
`r_N=sum_(tau in Noncore) (|p_tau|^2+|q_tau|^2)`. The EXACT B4 signed
noncore/core defect therefore is

```text
defect_N = r_N - 2 n_N
         = sum_(tau in Noncore_N) (|p_tau|^2+|q_tau|^2-2).
```

For each integer `m>=10`, the incidence
`p=(m,0,0),q=(1-m,1,0)` is a deep high-high Noncore row with *zero*
amplitude but strictly positive contribution `2m(m-1)`, provided
`N>=m`. For all integer p with p+q=k the individual excess is
nonnegative. Hence
`defect_N >= 2 sum_(m=6)^N m(m-1) -> +infinity`.

By contrast all Core input indices at this fixed output are already
present by cutoff 9: any new incidence beyond that has both input
shells at least 4 and is deep high-high. The Core-Core Young companion, including
ALL zero-zero pairs, is constant at `M_core=1345859672` for `N>=9`.

Executed exact receipt from
`scripts/ns_b4_literal_padding_adversary.py` (all integers/Fractions):

| cutoff N | zero-amplitude Noncore rows | signed defect | literal M_core |
| ---: | ---: | ---: | ---: |
| 4 | 0 | 0 | 3306048 |
| 8 | 0 | 0 | 735927680 |
| 9 | 682 | 185520 | 1345859672 |
| 16 | 28318 | 16776416 | 1345859672 |
| 36 | 372958 | 988633056 | 1345859672 |
| 40 | 512926 | 1671172320 | 1345859672 |

**No-go scope:** For this fixed global smooth state, any legitimate
physical `ED_N(u)` bounded uniformly in cutoff N and finite constants
`theta_D<1/2,c_D` cannot make
`defect_N<=theta_D*M_core+c_D*ED_N` hold for every N. Allowing the
opaque analytic interface's `localED` field to grow artificially like
the zero-padding rate sum does NOT constitute a cutoff-uniform physical
payment. The #1234 analytic record itself does not fix `ED`;
discharge its actual physical source meaning **before** promoting this
as a formal counterexample to a *fully specified* proposed inequality.

**High-alpha next physical theorem, NOT another RNNN:** retire or
redefine the full-fibre `n_N W(M,D)+(sum r)W(M,M)` covariance as a
uniform-control target; use original same-source modal heat work
`W(M,sum r_tau A_tau)` or a zero-padding-invariant amplitude-weighted
centering. Both are unchanged by extra zero cells. However one must
prove the replacement is the actual *unforced NS critical-production
quantity* via the pre-existing R406/R440 same-object chain; do not
rename a different expression as the B4 theorem. An active-support
index filter by `A_tau!=0` may be discontinuous at zeros; prefer
polynomial amplitude weighting or direct uncentered modal work.

Regression: `tests/test_ns_b4_literal_padding_adversary.py`.
Do not rerun general R579 Young, rebuild the R236 region classifier,
or mint more Round files. If source ED is cutoff bounded, the
**specific old B4 payment target is falsified**, and the positive B
programme must switch to a corrected estimator; the Navier–Stokes Clay
problem itself is unaffected.

### A same-object and majorant already-paid layers

The local Euclidean Fourier divergence-form cell and genuine canonical
Leray projection are ALREADY constructed in
`NSTriadKNEuclideanCanonicalProjectedInteractionExact.agda`:
`canonicalProjectedInteraction` and
`canonicalProjectedInteractionFormulaWeld`. The projected-cell
`|xi|^2` estimate is in
`NSTriadKNEuclideanProjectedInteractionQWeldExact.agda`.
Do not reopen the *local algebra* or introduce another opaque
`RawInteractionMeaning : Set` receipt.

Actual unclosed A1a is narrower but more important: the continuum
`EuclideanFourierTrajectory` currently accepts freely specified
`FourierTransformVelocity : Set` and a term of that type; this is NOT
the analytic theorem that the chosen `velocityHat` is the spatial
Fourier transform of the SAME physical Navier--Stokes velocity.
Construct that concrete transform (initially Schwartz/smooth/finite
energy with justified integrability), the derivative/product
convolution identity and the physical-time attachment. Do not
promote only a Schwartz sample to arbitrary initial data.

For A2 the repo already found a hidden **measure-dimension no-go**:
`NSWholeSpaceConvolutionEnergyTonelliExact.agda` notes that a
nonnegative Gram-pair bound on the FULL independent
`(xi,eta_alpha,eta_beta)` carrier has a free `R3` variable and
generally infinite integral. Integrate coherent/signed pair first
or use the SINGLE genuine convolution fibre
`e(eta)e(xi-eta)`, whose `R6` integral factors as
`(int_R3 e)^2`. Finite translation quadrature and the convergence
of the convolution mass from the energy limit are already in
`NSWholeSpaceFiniteConvolutionSingleLimitExact.agda`. Remaining:
instantiate its energy quadratures from the real Fourier field and
bind to the actual low/high physical envelopes, with no fictitious
positive `R9` majorant. A3 whole-space continuation still remains.

**Revised priorities:** P0 B4 source-ED and zero-padding redesign;
P0 A Fourier-transform same-solution theorem; P1 A single-fibre energy
quadrature and low/high domination; P1 B1/2/3 and B7 physical
budgets; P2 unforced A/B continuation. Existing canonical owners only,
no new numbered proof files. No external paper authorship or kernel
verification is implied by this DASHI negative-control calculation.

---

## 2026-10-24 — Original unforced A+B proof archaeology and executable priorities

**Verdict after cross-PR/current-owner audit.** The user's recollection of extensive prior
art is correct: [merged #1091](https://github.com/chboishabba/dashi_agda/pull/1091)
already reduces A to five physical leaves and B4 to one literal R440 payment;
[merged #1234](https://github.com/chboishabba/dashi_agda/pull/1234) already
defines the exact source-attached B4 analytic payment **interface**;
[merged #1233](https://github.com/chboishabba/dashi_agda/pull/1233) already
defines the canonical A/B proof-obligation ledger. Do NOT recreate any of these.

**Proof versus interface.** A record taking arbitrary `Set`-valued
Fourier-transform meaning, signed payment, physical-majorant domination,
or continuation inputs is a conditional theorem *consumer*. A `refl`
receipt proving a Boolean is `true` is not evidence that such a field
was populated on every admissible physical Navier–Stokes solution.
The audited canonical source still marks all five A theorem leaves open,
and the B4 physical payment, B1/2/3 producer estimates, B7, and B
continuation inputs open. There is no observed exact-head kernel receipt
or unrestricted global A/B existence proof here. Keep Clay promotion false.

### Canonical owners and exact evidence (not historical RNNN)

| Obligation | Existing paid mathematics | Actual acceptance input | Owner |
| --- | --- | --- | --- |
| **A1a** | Physical Fourier trajectory types; canonical pair and signed off-diagonal Gram; origin saturation | Construct *the actual* Euclidean Fourier NS interaction and prove same-solution equality with canonical projected pair; no invented `Set` witness | `NSClayFacingAPureAnalysisFrontier20261007Exact.agda`, `NSTriadKNEuclideanPhysicalFourierNSExact.agda` |
| **A1b** | Positive heat rate and high-frequency scale-relative curvature | Actual output heat rate = nu*|xi|² and physical cutoff/envelope alignment for all required interactions | `NSClayFacingAPhysicalSameObjectCutExact.agda` |
| **A2-low** | Signed origin bound and convolution integration compiler | From finite energy, physical low majorant <= real low convolution envelope, including near xi=0 | `NSWholeSpacePhysicalMajorantDominationProducerExact.agda` |
| **A2-high** | High-frequency curvature and inverse-sixth envelope algebra | Physical high majorant <= weighted high envelope; integrability of the actual source-state envelope | same |
| **A3** | Compensated field and signed Lebesgue continuation compiler | A globally admissible physical continuation criterion for arbitrary smooth finite-energy datum; pressure/initial trace/smoothness verified | `NSCanonicalA3ContinuationResidualExact.agda` |
| **B4** | Exact principal half bound, noncore/core covariance and literal R440 work reduction | For all physical states, cutoffs and outputs, `-W(M,n_C R440_N+n_N R440_C-r_N M_C-r_C M_N) <= thetaD*M_core+cD*ED` with `thetaD>=0`, `1/2+thetaD<1`, cutoff-independent constants; inhabit existing #1234 socket | `NSTriadKNPhysicalCriticalTouchingDefectR44020261007Exact.agda`, `NSCanonicalB4PhysicalR440AnalyticInterfaceExact.agda` |
| **B1/B2/B3** | Row extraction, shell folds, gap/component infrastructure | Actual DFL/DHH shell populations, signed Bernstein/L2 estimates, uniform local ED allocation | `NSClayFacingBPureAnalysisFrontier20261005Exact.agda` |
| **B7** | Q4 pointwise-to-spacetime and E+ aggregation compilers | Literal Q4 Gram payment and E+ global amplitude sum with cutoff-independent bound, or genuine Q5 fallback | `NSCanonicalB7IntegratedControlResidualExact.agda` |
| **B continuation** | Generic BKM/compactness and mean restoration compilers | Uniform bounds, Galerkin limit/pressure and global smooth continuation for arbitrary periodic initial data | `NSCanonicalBContinuationResidualExact.agda` |

### Actual mathematical research programme, ordered by information gain

**P0 — B4 physical no-go or constructive certificate.** Work ONLY on the
literal live R440 noncore/core residual; retain the sign rather than
taking |work|. First compute exact small-mode rational adversarial families
(phases, amplitude rescalings, shell separation, increasing cutoff)
against any proposed `thetaD<1/2` estimate. A raw pair-rate Young bound
has an amplitude-independent term and therefore cannot be absorbed by
homogeneous local ED; use amplitude-weighted R440 terms and exact physical
shell geometry. A failed candidate is valuable negative evidence; do not
relabel it as a conditional theorem closure. If a uniform producer is found,
instantiate the PR #1234 **existing** analytic record and bridge to B4.

**P0 parallel — A1a concrete Euclidean Fourier population.** The
canonical pair-resolvents and signed Gram are ALREADY paid. The missing
object is an actual Fourier transform/projection of the same continuum
solution, including transformation of the nonlinearity and its signed
integrand. Start with a Schwartz/smooth solution test family but do not
promote a restricted solution class to the universal Clay A statement.
Construct a proof of the literal carrier equality, not a new abstract
resolvent field. Use the existing Bishop complex/Leray carrier.

**P1 — A1b and A2.** With A1a fixed, prove low-frequency cancellation
or integrable majorant (the scalar resolvent bound alone has
`a^{-1}~|xi|^{-2}` and its stability estimate has
`a^{-2}~|xi|^{-4}` singularities). Prove separately the high inverse-sixth
weighted convolution estimate. Consume the already-present
`PhysicalEnvelopeInputs`; do not rebuild Fubini/Young.

**P1 parallel — B1/B2/B3 producer estimates.** Real signed
shell-local physical estimates and cutoff-uniform local ED budgets;
generic fold and cardinality-free compilers are already installed.

**P2 — integrated B7 and full A/B continuation.** Pay Q4/E-positive
or verified Q5, then apply the existing physical Galerkin/compactness
compiler. For A, apply the actual finite-energy majorants and the
whole-space continuation criterion. Arbitrary initial-data quantifiers
and absence of circular Serrin/BKM inputs are mandatory.

### Stop / attribution / proof acceptance

- Main result should be a source-exact theorem at an existing *physical*
  owner, not a ninth RNNN module or a new selected source predicate.
- Distinguish mathematical theorem, source-written Agda/Lean term,
  checked kernel output, and unbounded A/B Clay target. State only
  evidence actually observed.
- If a proposed B4 estimate fails on a physical rational witness,
  preserve the exact negative-control receipt; do not force it through
  Young's bound as a positive proof.
- The real R823 counterexample is an **auxiliary reserve route**
  (existing Lean R760/R823 decision), not B4 and not Clay B.
- The selected Lean `NSUnforcedAnalyticCuts.lean` contributes scalar
  saturation stability and finite pairwise Young bounds, but neither
  pays A2 nor uniform B4. Its new declarations have NOT been kernel
  typechecked in this session.

**Default navigation:**

```sh
python scripts/ns_canonical_focus.py --route A
python scripts/ns_canonical_focus.py --route B
python scripts/ns_canonical_focus.py --route B4
```

The three commands now resolve to the *physical* frontier/defect
source files, not the abstract canonical-record schedulers. Historical
RNNN packages remain bounded evidence only. No CI requested or run.

---
## 2026-10-24 original unforced A/B direct analytical cut

**Theorem source:** `dashi_lean4/NSUnforcedAnalyticCuts.lean`, optional
`lake build NSUnforcedAnalyticCuts`. This source contains eight source-written
finite analytical lemmas and creates **zero numbered Round modules**.
Lean was not run on this source, so treat these as source-written terms.

**A actual next step (whole-space Fourier physical owner):**
`NSWholeSpaceCanonicalPairSaturationOriginExact` already constructs
the actual scalar saturation coefficient from positive viscous heat
`a = nu*|xi|^2` and centered residual `s >= 0`, with signed
off-diagonal Gram treated correctly. New analytic equations:

```text
K_a(s) = s/(a(a+s)) = 1/a - 1/(a+s)
0 <= K_a(s) <= 1/a
K_a(s)-K_a(t) = (s-t)/((a+s)(a+t))
|K_a(s)-K_a(t)| <= |s-t|/a^2
```

The stability estimate is a **local** quantitative bound; it blows
up as |xi| -> 0, since a=nu*|xi|^2. It does not manufacture the
physical near-zero same-object realization or finite-energy majorant.
The two genuine A proof producers remain:

1. Identify the literal Fourier-velocity / Leray-projected
   Euclidean physical kernel with the canonical signed Gram and
   canonical pair/output resolvents on the SAME continuum solution.
2. Derive physical low and high source-state convolution envelopes
   with actual domination and integrability from finite energy;
   then discharge the whole-space continuation criterion.

Do not treat a user-chosen `Set`-valued `FourierTransformVelocity` or
`PointwiseBelow` in an abstract record as a physical analytical proof.

**B actual next step (signed noncore/core R440):**
`NSTriadKNPhysicalCriticalTouchingDefectR44020261007Exact` already
identifies the literal residual and its coherent-work payment.
`NSTriadKNFiniteBipartiteCovarianceExact` already shows the defect
is a signed sum of pairwise input-rate and work differences.
The new theorem proves the exact finite signed oscillation Young
bound and cancellation when cross-partition input rates agree.
A tunable `eps>0` bound permits a formal strict-subhalf
`eps/2` coefficient on pairwise work oscillations.

CRITICAL: **This alone does not pay B4.** The raw squared rate-gap
term has a positive, velocity-amplitude-independent floor. It
cannot be bounded by homogeneous local enstrophy dissipation under
small-amplitude scaling. The real next theorem must exploit the
literal R440 mixed-product amplitudes and input-frequency geometry
to produce an **amplitude-weighted** cutoff-uniform rate defect
estimate without a shell-count/cardinality loss. No sign or
pointwise-absolute-value shortcut is allowed. Continue B1/B2/B3
physical producer estimates and B7/Q4/E-positive summation separately.

Neither A nor B is mathematically closed. Do not change the canonical
`clayPromotion = false`, and do not interpret this as Clay certification.

---
## 2026-10-24 canonical max-cut navigation — no RNNN grep loop

The September chronology below is historical. Merged PR #1232 already
classified Round packages and defined non-Round canonical Clay residuals.
The later Lean `NSBControl/Rational345R823DecisionFreeze.lean` holds the
literal real R760/R823 auxiliary reserve decision, source-written but
not independently kernel-certified in this handoff.

**Start from the mathematical route, not a numbered Round module:**

```sh
python scripts/ns_canonical_focus.py --route R823
python scripts/ns_canonical_focus.py --route B
python scripts/ns_canonical_focus.py --route B4
python scripts/ns_canonical_focus.py --list --validate
```

The six registered routes resolve to one primary theorem owner and at most
three supporting owners. This registry lives inside the existing
`config/ns-round-extraction-targets.json`; it is navigation metadata, not
new mathematical authority. Unmapped R numbers fail closed.

If an exact old declaration must be inspected, query the existing classified
receipt, returning at most three examples instead of 30,885 packages:

```sh
python scripts/ns_canonical_focus.py --route B --historical-symbol exactTheoremName
```

Historical classifications and the 19,312 unresolved baseline entries
are evidence only; never inflate them into independent open Clay tasks.

**No-growth guard** against newly added numbered modules, using the
post-reconciliation baseline (prior R851/R852 remain historical evidence):

```sh
python scripts/ns_canonical_focus.py --guard-new-rounds 4f9d7d517e60b7607c85b41d3b58e7bb88041d39
```

This checks only files newly added after that baseline; existing theorem
owners may be edited. Do not delete theorem-bearing history, or replace
source equalities with aliases lacking exact same-object proofs.

**Authority boundary:** auxiliary R823 failure is not positive Clay B;
source-written is not Lean/Agda kernel-certified, and forced C/D are
not unforced A/B. Keep the canonical Clay promotion flag fail-closed.

---
# Navier–Stokes proof-control record — live A/B/C/D coordinator

Status: authoritative live routing/control document; non-promoting.

Current-state date: `2026-09-23 AEST`.

This is the default answer source for current NS proof-search state. Historical
round/PR detail remains append-only in `CrossLaneProofArchaeologyLedgerExact`.
Inspect exact owners only for a named unpaid theorem or field.

## Operating hierarchy

```text
1. this current control / producer summary
2. canonical archaeology ledger / PR chronology
3. exact owner only for the named unpaid theorem/field
```

Always keep `MathematicalStatus`, `StatementStatus`, and `CertificationStatus`
separate. Source code, a conditional compiler, another prover receipt, or a
Boolean status field cannot manufacture a theorem or kernel receipt.

## Coordinator ownership

```text
merged #937   canonical A/B/C/D baseline + S0/S1/S2a state
open   #948   completed S2b finite/same-object packet representation
open   #957   live S2b2 quantitative analytic successor
#920          R571 -> Aug-5 paired-second-moment representation transplant
#945          Gate-A cross-prover receipt/status surface
#947          local Hermitian G0' splice
#890          retained comparable/P3 route + negative controls
#883 branch   append-only proof-archaeology/bookkeeping surface
```

## Four lane meanings — frozen

```text
A — unforced whole-space R^3 regularity       independent theorem obligation
B — unforced periodic T^3 regularity          active proof-discovery lane
C — forced whole-space R^3 breakdown          released-proof integration lane
D — forced periodic T^3 breakdown             released-proof integration lane
```

This control plane tracks all four lanes.  The active internal proof-discovery
lane remains B, A is audited bidirectionally against B, and C/D are
released-proof integration lanes with their own source-alignment and
same-object adapter residuals.

Firewalls:

```text
B does not imply A;
A does not imply B;
forced C/D do not settle A/B;
source-proof presence is not DASHI same-object payment.
```

Typed all-four mission owner:

`DASHI/Physics/Closure/NSGlobalFourAlternativeMissionExact.agda`

Canonical literal Clay proposition endpoint:

`DASHI/Physics/Closure/NSClayLiteralABCDExact.agda`

This is now the theorem-facing A/B/C/D surface.  It replaces the old practice
of treating `PaymentA/B/C/D` scheduler tokens as if they were the Clay
propositions themselves.  The legacy tokens remain only for compatibility;
new terminal consumers should use `LiteralFourAlternativeCompletion` or
`AnyOneClayResolution`.

Typed current control-plane receipt:

`DASHI/Physics/Closure/NSProofControlABCD20260916ReceiptExact.agda`
`DASHI/Physics/Closure/NSProofControlABCD20260916ReceiptRegression.agda`

Typed released-proof/source-alignment owners for C/D:

```text
NSTriadKNClayForcedBreakdownFormulationRound523Exact
NSClayFourAlternativeReleasedProofBidiExact
NSOpenAI2026ComparatorClayCDSourceExactAlignment
NSOpenAI2026ReleasedClayCDTorus369BidiExact
```

Current all-four ledger:

```text
four-alternative mission implemented          true
official any-one criterion separated          true
C external released proof present             true
D external released proof present             true
C/D source alignment to Clay coordinates      closed
DASHI independent Agda reconstruction of C/D  false
C/D released-field -> DASHI Fourier/R406 weld false
CMI prize / DASHI discovery claim             false
all four internally paid                      false
```

# A — whole-space unforced: proof discovery deferred, portability BIDI ACTIVE

A is no longer scheduler-idle. Fresh whole-space PDE proof search remains
deferred while B exposes a sharper theorem spine, but every material B advance
is now audited bidirectionally for A portability.

Typed owner:

`DASHI/Physics/Closure/NSABPortabilityBidiStatusExact.agda`

Current firewall/status:

```text
B -> A implication allowed                 false
A -> B implication allowed                 false
A portability audit active                 true
whole-space same-object transport observed false
```

The audit classifies each B theorem family as one of:

```text
domainIndependentCandidate
torusSpecificRealization
mixedNeedsFactorization
unresolvedWholeSpaceTransport
```

Current coordinates include:

```text
R104 signed Abel/layer-cake algebra        domain-independent candidate
R98 packet-boundary cancellation           mixed; selector algebra vs finite Fourier realization
#957 low/collar/remote shell split         torus-specific realization
R291/R573 signed Hermitian linearization   domain-independent candidate
S2b2d0 output-local fixed-output reduction domain-independent candidate
S2b2d1a damped-tangent residual identity   domain-independent analytic candidate
S2b2d1b0 coherent-work scalar split        domain-independent analytic candidate
S2b2d1b1 endpoint compiler                 domain-independent modulo ordinary calculus/FTC
S2b2d1b2 coherent-covariance payment       unresolved whole-space transport
#920 paired-second-moment compiler         mixed; generic centered algebra vs periodic realization
R568/R572/R503 commutator chain            mixed; analytic core vs output-fibre/lattice plumbing
R541/R573/R584/R503 ordered-kernel cone    mixed; signed consumer core vs periodic realization
```

The `S2b2d0` result is important for BIDI: once an output is selected, the
periodic exact-shell 0/1 weight disappears completely on that fixed-output
fibre. The hard local analytic object is therefore the ordinary unweighted
fixed-output mixed commutator; `shellIndex` only decides which outputs are
active.

`S2b2d1a` sharpens this again without proving A from B: the unweighted
commutator is exactly the forcing residual in the generic damped mixed-product
tangent identity. Its algebra does not mention the periodic shell selector.

`S2b2d1b0` then pushes that exact vector identity through the same real-Hermitian
consumer and isolates, for any common rate, an endpoint/tangent term plus one
signed coherent-covariance residual. `S2b2d1b1` constructs the actual fixed-
output derivative on the R408 trajectory and compiles the endpoint term to a
self-energy endpoint difference given ordinary derivative-of-zero and scalar
FTC authority. Therefore the only genuinely nonlinear local d1b theorem left
is the coherent-covariance payment `S2b2d1b2`. None of these classifications
promotes B to A.

BIDI questions:

```text
B -> A:
  quotient paid B objects into domain-independent analytic core
  + torus/lattice/cutoff realization
  + explicit whole-space transport obligations.

A -> B:
  use the whole-space formulation to detect where a B lemma is accidentally
  over-specialized to a finite lattice rather than structurally necessary.
```

No portability classification is a theorem transport. A changes from
"portability audit" to active proof construction only when a named R^3 transport
obligation is concrete enough to attack without pretending B already proves A.

# B — periodic unforced: ACTIVE

## B_comm

Working routing assumption:

```text
recent L0-L6 obligations recoverable          true
commit-specific Agda receipt                  false / not observed
```

Under that assumption the signed nested compiler chain

```text
R573 nested spacetime budget -> R568 -> R572 -> R503
```

is reconstruction/certification debt. An owner merely accepting R568 is not a
producer. Do not reopen broad commutator archaeology unless an exact recovery
field fails.

## B_phase — current strict state

```text
R104 abstract signed-critical compiler                       DONE
R414 literal-R406 remainder chosen definitionally            DONE
R516/R517 critical radial/norm realization                   DONE
S0 literal finite X_N,D_N,N_N fold                           DONE source
S1a finite pointwise critical-energy algebra                 DONE source
fixed nonzero cutoff mode carrier without S4                 DONE source
S1b integrated-energy compiler given calculus                DONE conditional source
concrete scalar FTC                                          OPEN infrastructure
concrete integrateTo linearity                               OPEN infrastructure
S2a literal N_N -> R39/R98 projected pairing                 DONE source
S2b0 projected pairing -> R104 BandTransfer                  DONE source
S2b1 full R104 layer-cake -> physical upper-shell flux       DONE source
S2b2a packet-complement antisymmetry                         DONE source
adjacent shellIndex -> Euclidean gap                         REFUTED source negative control
S2b2b upper packet = exact-shell collar + remote             DONE source
S2b2c0 low + collar + remote physical flux identity          DONE source
S2b2c1 two-shell low/remote integer Euclidean gap            DONE source
S2b2c2a integer gap -> live rational C3.normSquared          DONE source
S2b2c2b literal low/remote R98 spectral datum                SOURCE-WRITTEN / certification pending
S2b2d0 output-local collar weight -> active unweighted fibre DONE source
S2b2d1a fixed-output damped tangent = decay + commutator      SOURCE-WRITTEN / certification pending
S2b2d1b0 exact coherent-work/covariance scalar split          DONE source
S2b2d1b1 literal fixed-output endpoint compiler               DONE conditional source
concrete endpoint zero-derivative + scalar FTC               OPEN infrastructure
S2b2d1b2 quantitative signed coherent covariance payment      OPEN PRIMARY
S2b2d2 cutoff-uniform sum of fixed-output budgets             OPEN after d1b2
S3 cutoff-uniform initial critical ceiling                   OPEN
S4 positive retained viscosity 0 < 2*nu-a                   OPEN
```

No unconditional physical R104 slice or Clay promotion is claimed.

## S0 / S1 — already reduced to standard-analysis infrastructure

On the live R240 finite trajectory:

```text
X_N(t) = sum_k w(k)|u_N(k,t)|^2
D_N(T) = int sum_k w(k)|k|^2|u_N(k,t)|^2 dt
N_N(T) = int 2 sum_k w(k) Re<N_k(u_N),u_N(k)> dt
w(k)   = 2^(shellIndex k).
```

S1a source-writes

```text
X'_N = N'_N - (2 nu)D'_N.
```

S1b source-writes the compiler

```text
X_N(T) + (2 nu)D_N(T) = X_N(0) + N_N(T)
```

given ordinary scalar FTC and integration congruence/additivity/scaling.
Concrete authorities remain infrastructure/certification leaves, not nonlinear
NS proof-search targets.

# S2 — signed critical production

## S2a/S2b1 representation — CLOSED SOURCE

The selected same-object route is complete:

```text
literal N_N
 -> R39/R98 projected pairing
 -> R104 BandTransfer
 -> literal shell sort/permutation
 -> reject-zero full/nonzero cutoff bridge
 -> upper-shell selector
 -> canonical suffix / strict-jump tail
 -> recursive-prefix weld
 -> normalized physical R98 upper-shell boundary-flux layer-cake.
```

No Schur/Wiener/positive-part majorant, cardinality tax, or quantitative R406
bound enters this representation chain.

## S2b2 — PRIMARY nonlinear theorem

Integrated target:

```text
N_N(T)
  <= a D_N(T)
     + literalR406RemainderIntegral(N,T).
```

#957 establishes the exact physical decomposition

```text
low    : shellIndex < j
collar : shellIndex = j
remote : shellIndex >= j+1

F_low + F_collar + F_remote = 0.
```

The tempting adjacent-shell spectral-gap shortcut is permanently rejected by

```text
(2,2,2): shellIndex=1, |k|_2^2=12
(3,0,0): shellIndex=2, |k|_2^2=9.
```

For `j=suc K`, the two-shell low/remote geometry instead gives

```text
shell(low) < j       -> |low|_2^2 <= 3*(2^K)^2
j+1 <= shell(remote) -> 4*(2^K)^2 <= |remote|_2^2.
```

### S2b2c2a — DONE SOURCE: live rational norm transport

`NSTriadKNRationalIntegerEmbeddingModeNormScaleExact` proves that for an
arbitrary additive rational `IntegerEmbedding`, with `c = E(1)`,

```text
C3.normSquared I k
  = c^2 * natAsRational(modeNatNormSquared k).
```

Because `c^2 >= 0`, the concrete `3 < 4` low/remote ordering transports to the
same live `C3.normSquared` used by R407 viscosity. No separate calibration
receipt is introduced.

### S2b2c2b — REMOTE packet datum: SOURCE-WRITTEN, certification pending

`NSTriadKNLowRemoteSpectralDatumRound98Exact` constructs the literal
`R98.SpectralCrossDissipationDatum` on the same low/remote packets with

```text
E_P = (1/2) sum_P |u_k|^2
D_P = nu sum_P |k|^2 |u_k|^2

lambda_low    = 2*nu*omega_low
lambda_remote = 2*nu*omega_remote.
```

It uses only ordinary physical `0 <= nu`, not S4's later `0 < 2*nu-a`.
Existing R98 spectral-cross coercivity is therefore the remote compiler once
this source surface is actually certified.

### S2b2d0 — DONE SOURCE: periodic collar weight disappears on fixed output

`NSTriadKNOutputLocalSelectorFixedOutputReductionExact` first proves the generic
output-local theorem. For any Boolean selector depending only on the final
output:

```text
selected(output)=true
  -> weighted fixed-output commutator = ordinary unweighted fixed-output commutator

selected(output)=false
  -> weighted fixed-output commutator = 0.
```

The exact-shell collar is only a corollary. This removes `shellIndex` from the
hard local analytic theorem and strengthens the A/B portability cut.

### S2b2d1a — DONE SOURCE: exact damped-tangent residual identity

`NSTriadKNFixedOutputMixedCommutatorDampedTangentExact` combines R231 and R230:

```text
sum_{p+q=k} dampedMixedTangent(p,q)
  = sum_{p+q=k} variableViscousDecay(p,q)
    + sum_{p+q=k} unweightedMixedCommutator(p,q).
```

This is an exact finite identity before norms. It removes the ambiguity about
what the d1 commutator is dynamically: it is the forcing residual in the
mixed-product tangent equation.

R229 is the controlling no-go. Cellwise lower bounds on the viscous rates do
not imply favorable damping of the coherent fixed-output sum; an explicit
finite witness gives adverse signed covariance. Therefore d1a does not close
the payment merely by inserting viscosity.

The retained P3/raw-curl partner route is not silently identified with d1a:
P3's compressed cells are quadratic velocity blocks, while the R230 commutator
is cubic after inserting physical NS forcing. Any useful bridge must be a typed
same-object theorem, not analogy.

### S2b2d1b0 — DONE SOURCE: exact coherent-work decomposition

`NSTriadKNFixedOutputCoherentCovarianceWorkExact` pushes d1a through the same
real-Hermitian scalar consumer. For any common rate `lambda` it proves exactly

```text
W(M,C)
  = W(M,T)
    + lambda W(M,M)
    - W(M, D + lambda M),
```

where `M` is the coherent fixed-output mixed-product sum, `T` its damped
tangent, `D` the variable viscous-decay sum, and `C` the fixed-output
commutator. The final term is the signed coherent covariance residual. No sign
or inequality is assumed.

### S2b2d1b1 — DONE CONDITIONAL SOURCE: endpoint term is ordinary calculus

`NSTriadKNFixedOutputMixedEndpointCompilerExact` constructs the actual R408
mixed-cell derivatives, folds them on the literal fixed-output fibre, and uses
R94/R381/R292 to identify that tangent with the same physical damped tangent
used in d1a. It then proves, given ordinary derivative-of-zero and scalar FTC
authorities,

```text
integral W(M,T) dt
  = Re<M(T),M(T)> - Re<M(0),M(0)>.
```

Thus the endpoint term is infrastructure/certification debt, not a new NS
estimate. Concrete zero-derivative and FTC inhabitants remain explicitly open.

### 2026-09-23 H2 weighted-carrier correction

The endpoint-aware A3 audit has now separated two carriers that earlier
bookkeeping risked conflating.

The literal R406/R557 route is resolvent weighted.  The exact live temporal identity, **given the scalar FTC authority already isolated by R564/R565**, is now composed theorem-by-theorem in
`NSTriadKNR406ExactEndpointNormalFormExact`:

```text
2 * integral R406
  = integral FactoredFull
    - integral SelfGram
    - (SelfFlux(T) - SelfFlux(0)).
```

This uses R557 plus the same-object R570 self-flux tangent/FTC weld and
introduces no new Navier--Stokes estimate.

Separately, `NSTriadKNA3D1bDivisionFreeTransportExact` composes d1b0 with the
existing covariance-centering identity.  On one fixed-output fibre it proves
the division-free normalization

```text
n * W(M,commutator) + A3SignedPairDifference
  = n * W(M,tangent) + (sum rates) * W(M,M).
```

Thus the current unweighted A3 pair-difference scalar is NOT definitionally
the literal weighted R406/factored-full scalar.  The mean-rate self-work term
and fibre-cardinality normalization are real algebraic coordinates, and R406
also carries the nonseparable spectator resolvent
`1 / (rate_alpha + rate_beta)`.

The canonical weighted boundary owner
`NSTriadKNA3WeightedR406EndpointCutExact` therefore keeps

```text
a3PairDifferenceIsLiteralFactoredFullSameObjectClosed = false
unweightedD1b0DirectlyPaysWeightedR406Pointwise       = false
```

while recording the endpoint side as closed modulo ordinary scalar FTC.

Consequently, do NOT classify

```text
integral R406 = endpoint + integral (4 * unweighted A3)
```

as representation plumbing.  The generic endpoint-aware compiler remains a
valid conditional consumer, but the unit-coefficient A3/R406 equality is not
derived by d1b0+d1b1.

The actual weighted live producer remains R568:

```text
4 * integral GlobalForcingFull_resolvent <= B(T),
```

with R570/R572 compiling it to the existing R406/R503 consumer.  The unweighted
A3/separation theorem is therefore a candidate donor to that weighted theorem,
not already its same-object representation.

This correction does not add a new theorem claim; it sharpens where any new
analytic bridge would have to land.

### S2b2d1b2 — PRIMARY analytic leaf: signed coherent covariance payment

The only genuinely nonlinear fixed-output theorem remaining in d1b is now

```text
signed coherent covariance W(M, D + lambda M)
  -> theorem-bearing fixed-output budget B_k
  -> R432/R487 FixedOutputSignedCrossPayment.
```

The common rate may be chosen to optimize the later budget, but R229 forbids
inferring a favorable coherent sign merely from cellwise nonnegative excess
rates. R232 separately rules out a generic pointwise half-derivative gain.
R432/R487 already own the cardinality-free downstream compiler once theorem-
bearing local budgets exist.

Same-object audit on 2026-09-16: the new
`NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact` owner already closes
the division-free finite algebra

```text
n * W(M, variableDecay) + (sum rates) * W(M,M)
  = - sum_{i<j} (r_i-r_j)(w_i-w_j)
```

on the literal fixed-output mixed-helicity fibre. Thus the live local payment
is no longer an unspecified covariance residual; it is the theorem-bearing
signed pair-difference budget for that exact family. R472/R480 remain useful
older R432 producers, but their own status lines still keep the physical
snapshot/same-object weld false, so they do not currently close d1b2 by alias.
The next search should be for a same-carrier pair-difference payment or a proof
that the existing physical snapshot weld is exactly this d1b2 family.

Recovered pair-difference archaeology: `NSTriadKNFixedOutputPairDifferenceDebtExact`
and `NSTriadKNFixedOutputPairDifferenceAggregateExact` already close the finite
Complex3 complete-graph identity and the literal R574 norm-sum aggregate:

```text
||sum_i B_i||^2 + PairDiffMass(B) = n * sum_i ||B_i||^2
PairDiffMass(fixed output) = literal R574 pair-norm mass.
```

These are exactly the right vocabulary for the d1b2 pair-difference side, but
their status lines keep the physical lower-bound/payment leaf false. So the
follow-up is not new finite algebra.

The P3 compiler `NSTriadKNFixedOutputPairDifferencePaymentExact` is also already
present: an R574 lower-separation premise for the same fixed-output aggregate
implies the same-output Gram-debt payment. Its status line keeps
`fixedOutputPhysicalLowerSeparationClosed = false`, so the remaining leaf is the
physical lower-separation/payment input and its attachment to d1b2's
rate-weighted signed pair-difference carrier.

The literal geometric donor immediately upstream is
`NSTriadKNCenteredPartnerDifferenceAdapterExact`: it proves the R205 compressed
partner difference is the R574/R446 difference value and, on the fixed-output
carrier, rewrites each slot-kernel difference as two exact amplitude-increment
branches via `fixedOutputSlotKernelDifferenceTelescopesByAmplitudeIncrements`.
`NSTriadKNCenteredPartnerSlotDefectExact` then records the norm-level identity

```text
||B_alpha - B_beta||^2 = 4 ||K_alpha - K_beta||^2.
```

So the quotient/same-object/amplitude-telescope/slot-defect normalization is
already source-written. The named open field is now specifically the
radial/Pluecker lower weld for that slot defect:

```text
roundCenteredPartnerRadialPlueckerDefectWeldClosed = false
roundCenteredPartnerSlotDefectRadialPlueckerLowerBoundClosed = false.
```

That is the next literal search vocabulary for the lower-separation input; it
is not a request to rebuild the R205/R574 adapter or the norm-four identity.

Literal search also finds the older Luo `CenteredPairCell` compiler in
`NSTriadKNLuoPhysicalCenteredCommutatorAssemblyExact`; keep it as a structural
donor, not a live splice. The current same-object adapter still records

```text
roundCenteredPartnerCenteredPairCellConstructed = false
roundCenteredPartnerCutoffUniformAggregateClosed = false.
```

So any promotion through the old centered compiler still needs the live
centered-partner cell weld, not merely the existence of the historical
`CenteredPairCell` record.

Guardrail donors around the radial/Pluecker weld are already in-repo.
`NSTriadKNExternalHHSquareGapGramRound128Exact` closes the exact polynomial
square-gap/Pluecker identity, but keeps the ordered drop/payment false:

```text
round128LowOutputTimesHighInputPolynomialIdentityClosed = true
round128OrderedDropPluckerRemainderClosed = false.
```

And `NSTriadKNFixedOutputConcreteSlotCollisionWitnessExact` closes the concrete
distinct-incidence same-slot collision witness. Therefore the live lower weld
cannot be an incidence-label-only radial/Pluecker coercivity claim:

```text
roundFixedOutputConcreteDistinctCCCollisionWitnessConstructed = true
roundFixedOutputIncidenceOnlyRadialPlueckerCoercivityRefuted = false.
```

The lower weld must see the actual quotient slot defect / amplitude-increment
data, not merely raw fixed-output incidence separation.

#### Recovered historical donor: R571 -> Aug-5 paired second moment

Do not search for a missing centered scalarization adapter. PR #920 already
source-wrote the representation chain

```text
R571 physical multiplier difference
 -> R571/R311/R27 radial same-object weld
 -> paired Taylor identity
 -> paired second-order defect
 -> absolute-magnitude PairedSecondMomentSample
 -> finite family-scoped paired-second-moment compiler.
```

`NSTriadKNR571PhysicalSecondMomentEnvelopeSplitExact` shows that the remaining
physical leaves of that donor route are only

```text
radial Taylor:
  |L| <= |y| A1
  |R+|,|R-| <= |y|^2 A2

state side:
  |g+ - g-| <= |y| G2
  |g+|,|g-| <= G1.
```

PR #945 records theorem-bearing Lean receipts for the periodic-B A1/A2 radial
mathematics. It keeps the Agda sample/same-object transport distinct, and it
identifies the existing finite-path difference theorem as G2 donor and the
Waleffe amplitude-energy theorem as an older G1 magnitude donor. The G0'
local Hermitian vector->scalar splice is source-written, and the R579 local
Hermitian Young owner now pays the same-carrier scalar G1 magnitude step
without square roots or a fibre-cardinality factor. The remaining state-side
work on this donor lane is therefore not a generic `|g_\pm| <= G1` search:
it is the G2 physical-gradient crosswalk plus any cutoff-uniform
shifted-coefficient/family transport needed to attach the local G1 envelope to
the live physical family.

For S2b2d1b2 this route remains a candidate donor only. Any attachment must land
on the same coherent-covariance carrier without losing the signed cancellation.
Otherwise retain #920/#945 as provenance donors and prove d1b2 directly. Do not
reopen their representation/scalarization chain.

#### Current signed consumer / ordered-kernel min-cut

The later R541/R573/R584/R503 cone has already pushed the live nested
four-sign carrier through the signed Hermitian consumer before norm. The
canonical status owner is
`NSTriadKNLiteralR406SpectatorWeightedClassNormEverythingExact`, with the
local exact producers
`NSTriadKNWeightedNestedSignedCrossThreeOrbitBidiExact`,
`NSTriadKNDirectCompanionThreeOrbitSignedRowBidiExact`,
`NSTriadKNNestedFactoredFullToOrderedOrientedForceBidiExact`, and
`NSTriadKNOrderedOrientedForceToR503BidiExact`.

The recorded same-object facts are:

```text
R329 -> R572 single-cell same-slot weld                 closed
signed Hermitian consumer three-orbit reduction          closed
live R503 direct companion rewritten as ordered kernel   closed
OrderedOrientedSpacetimeBudget -> R503                  closed
outer forcing Gram route mandatory for R503              false
independent amplitude budget required                    false
```

Thus the narrowest current analytic field on the direct R503 route is:

```text
cutoff-uniform bound for
  2 * integratedOrderedOrientedForce,
where H(alpha,beta) = w(alpha,beta) Re <G_alpha,D_beta>.
```

This is the signed-consumer version of the same operating rule:

```text
pair / cancel -> scalarize -> envelope -> majorize.
```

Do not take the nested forcing norm-square as the primary route before this
consumer: the homogeneity audit records that doing so changes the quintic
signed cross into a sextic object and opens a degree-seven derivative
remainder. The Gram/class-norm surfaces remain optional diagnostics or
producer routes only if they descend to the signed ordered-kernel budget.

# C/D — forced breakdown: RELEASED-PROOF INTEGRATION LANES

C and D are not proof-discovery blockers for A/B.  They are separate
Fefferman/Clay alternatives and now have released external theorem sources
recorded in-repo.  The current task is accounting and same-object integration,
not re-proving C/D by analogy and not using them to pay A/B.

`NSTriadKNClayForcedBreakdownFormulationRound523Exact` records the exact source
coordinates for:

```text
C: R^3 smooth forced breakdown with rapid spatial/space-time decay and
   bounded-energy no-global-smooth-solution consumer.
D: T^3 smooth periodic forced breakdown with rapid time-decay of all forcing
   derivatives and no-global-periodic-smooth-solution consumer.
```

`NSOpenAI2026ComparatorClayCDSourceExactAlignment` records:

```text
released C exactly matches Clay C                  true
released D exactly matches Clay D                  true
released C/D source alignment closed               true
released concrete field -> DASHI Fourier closed    false
released forcing -> literal R406 comparison closed false
independent Agda reconstruction of released proof   false
CMI award / DASHI prize claim                       false
```

`NSClayFourAlternativeReleasedProofBidiExact` records the all-four firewall:

```text
A internally paid                                  false
B internally paid                                  false
C external released proof present                  true
D external released proof present                  true
forced breakdown pays unforced A/B                 impossible / rejected
public theorem creates DASHI same-object payment   false
first released-integration residual                released field -> DASHI Fourier
```

Therefore the narrow C/D integration route is:

```text
external released C/D theorem/source receipt
  -> exact Clay C/D coordinate alignment        closed
  -> concrete released field/forcing extraction open
  -> DASHI Fourier/369/R406 same-object weld    open
  -> optional internal Agda reconstruction       open
  -> CMI/prize adjudication                      external, not a repo flag.
```

This released-proof lane should be kept synchronized with the A/B control
plane, but it must not be used to infer unforced global regularity or to
overwrite the B ordered-kernel frontier.

### S2b2d2 — global aggregation after local payments

Once d1b2 exists, the next residual is exactly R488's second node:

```text
4 * sum_k B_k <= B(T)
```

with no output-count factor. Do not search this global theorem before the local
fixed-output family exists.

# S3 / S4

S3: S0 already supplies the literal initial functional; remaining payment is a
cutoff-uniform initial-critical ceiling.

S4: prove `0 < 2*nu-a` only after S2b2 produces `a`. Do not close S4 ahead of
S2b2 except conditionally.

# Historical/provenance routes — append-only

```text
A1-A9 / ESS / Abel-defect manuscript route     historicalAlternativeRoute
R179-R214 comparable / P3 route                retainedComparator + negativeControls
R303/R353/R372 signed-resolvent route          serious precursor; production identity stayed input
#890 incidence/P3 work                         retained theorem-bearing comparator
P1/P2/P3 fixed-output pair-difference chain    finite/R574/payment compiler donor; lower separation open
Luo centered pair compiler                     structural donor; live centered-partner cell weld open
#920 R571/Aug-5 paired-second-moment transplant theorem-bearing representation donor
#945/#947 Gate-A/G0' work                      cross-prover + same-object donor surfaces
R579 local Hermitian G1 envelope               same-carrier scalar magnitude donor
R541/R573/R584/R503 ordered-kernel cone        selected signed-consumer same-object cone
Round523 forced C/D source formulation         exact Clay C/D coordinate owner
OpenAI2026 C/D released source alignment       external theorem/source receipt + firewall
OpenAI2026 D torus/369 seam                    released D -> DASHI Fourier/R406 residual owner
R576/R577 positive Gram/Schur route            fallbackProducerRoute
constant shell-localization payment            refuted as sufficient by R214
adjacent max-shell -> Euclidean gap             refuted by #957 explicit witness
R229 cellwise damping -> coherent damping       refuted by exact signed covariance witness
modern signed/nested commutator route           selected B_comm producer family
```

# Current Pareto allocation — A/B/C/D, B primary

```text
P0  keep this tracker + #957 + #883 archaeology summary synchronized
P1  B_phase S2b2d1b2: quantitative signed coherent-covariance fixed-output payment
P2  standard-analysis/certification: endpoint zero derivative + scalar FTC + S1b calculus
P3  static/certification validation of d1a/d1b0/d1b1 + S2b2c2b remote datum + d0 reduction
P4  A/B portability BIDI audit on each paid B theorem family (non-promoting)
P5  C/D released-proof accounting: released field/forcing -> DASHI Fourier/R406 weld
P6  B_phase S3/S4
P7  B_comm reconstruction/certification
P8  certify recovered S0/S1/S2/#957 source surfaces
```

Operating rule:

```text
track A/B/C/D in this control plane;
A/B remain independent from C/D;
A proof discovery deferred, A portability BIDI active;
never restart broad NS archaeology;
start every search from a named unpaid theorem/field;
preserve failed/superseded routes as append-only provenance;
B new mathematics starts at S2b2d1b2 coherent covariance only;
C/D source alignment is closed but representation/reconstruction/adjudication remain distinct;
preserve signed/local components before norms;
only after d1b2 search the cutoff-uniform sum d2;
never infer B -> A or A -> B without explicit same-object transport.
```

# Certification boundary

```text
source-written theorem
  != validation source/root
  != workflow target
  != observed successful commit-specific Agda receipt.
```

Merged #937 is the coordinator baseline. Draft #948 owns the completed S2b
representation. Draft #957 owns the live S2b2 analytic delta plus the current
A/B portability audit.

No unconditional Clay Navier–Stokes promotion is made here.
