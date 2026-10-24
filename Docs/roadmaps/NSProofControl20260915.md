# 2026-10-25 CURRENT MAX-CUT — A1 CONSTRUCTIVE SHELL RATE / B R735 FIXED-TIME NO-GO

**Continue original A/B, reuse actual proof owners.** This supersedes any
older roadmap wording claiming the A1 generic rational heat-rate
*equality* or R735 W1 *energy-only* payment follows from prior algebra.
Original attribution: Murray/Bishop rational density; Navier/Stokes,
Leray heat-energy, helical spectral decomposition, M. Riesz periodic
operator bounds. The finite test witnesses and integrations are
independent DASHI work. A mathematical derivation, symbolic fixture,
source-written Agda term and kernel-verified proof are distinct.

**A1 genuine SOURCE-WRITTEN code in original
`NSClayFacingAPhysicalSameObjectCutExact.agda`:**
`physicalViscousHeatAdmitsPositiveRationalFloor` and
`physicalShellHeatAdmitsPositiveRationalFloor` use the pinned
`RealProperties.fast-density-of-ℚ` to construct embedded rational
strict positive lower floors for respectively
the actual `Heat.viscousHeatRate fluid xi` and the single SHELL
rate `Heat.viscosity fluid * radiusSquared`.
The latter q is INDEPENDENT of xi on a fixed high-frequency shell
|xi|²≥radiusSquared>0. In particular this works for irrational
positive viscosity: the old
`PhysicalHighFrequencyEnvelopeData.physicalOutputHeatRateMeaning`
cannot be inhabited for generic real ξ/ν since it insists that an
embedded rational equal ν|xi|². The correct next theorem is a
**real** monotone inverse/curvature bound from the shell-wide rational
floor, then a new same-object producer/attachment; DO NOT substitute
an arbitrary rational a in the old source record. Bishop positive
reciprocal and ratio donors ALREADY EXIST in
`BishopPositiveCrossReciprocalUpperExact`,
`BishopStrictRatioInterpolationExact`. Low-frequency signed A2
and A3 noncircular continuation are still open.
`tests/test_ns_a_bishop_real_rational_heat_floor.py` provides
4 exact local SymPy checks at ν=sqrt(2), actual a=sqrt(2),
and q=7/5, including cubic reciprocal dominance and a uniform
frequency-shell sample. Agda kernel **not run**.

**B R735 W1 FINITE-TIME physical negative control:**
`tests/test_ns_r735_w1_energy_only_heat_shear_no_go.py`
(4 exact locally passing Fraction-based tests) constructs true
smooth unforced heat solutions
`u_N(0)=2/sqrt(2N) * sum_{j=1}^N cos(jx) e_z`.
For every N, E0=1 and ∫_0∞ D(t)dt=1/2. In the literal same-N
H+×H- mixed-output definition, initially
`E_M,N(0)=((N-1)(2N-1))/(48N)`.
At the FIXED physical time T=log(2),
`E_M,N(T)≤2/(3N²)` by Fourier heat decay + Young.
Since the true nonlinear commutator is identically ZERO,
the *existing* R691 identity yields
`W_N(T)+E_M,N(T)=E_M,N(0)`, so
`W_N(log(2))≥((N-1)(2N-1))/(48N)-2/(3N²)`,
unbounded across the family. Therefore any R735 W1 payment
with finite bound depending ONLY on E0, integrated enstrophy and T
and uniform across arbitrary smooth initial data is FALSE.
Important quantifiers: each fixed datum u_N has a perfectly finite
cutoff uniform bound depending on its H^(3/4) norm, so the
H^(3/4) R699 theorem and local/global *data-dependent* W1 are
NOT refuted. This is not Clay B blowup and cannot refute a
state-sensitive signed W1/W2 compensation theorem.

**B positive work remaining:** R699 initial mass has a standard
`H^(3/4)` data-dependent cutoff-independent ANALYTICAL estimate,
but physical normalized-real helical multiplier/Young/Plancherel
Agda attachment is NOT kernel inhabited. R735 general W1 still
requires a genuine globally signed nonlinear commutator bound
not reducible to E0. R735 W2 needs positive-margin augmented
critical weighted estimate with exact R406 same-object physics.
R823 reserve and R236 padding-dependent B4 shortcuts remain
excluded by existing physical counterexamples. No number of
conditional compilers replaces these estimates.

**Tests/verification:** 8 new exact local checks pass (4 physical W1
heat-shear, 4 rational/Bishop numerical-floor) with independent
scripts; committed test files match the modeled formulas, but
no exact-branch pytest run or Agda/Lean kernel check occurred.
No universal A/B regularity theorem proved. Preserve priority
on genuine W1/W2 analytics and continuum A1/A2/A3.

---

# 2026-10-25 IMPORTANT R699 SHARPENING — H^(3/4), NOT H^s>3/2, IS SUFFICIENT

The s>3/2 ell1/ell2 theorem in the previous current-turn
amendment below remains correct, but is NOT the minimal classical
regularity input. On the exact periodic rectangular sharp cube,
uniform L4 boundedness of P_N follows from M. Riesz's 1D
interval-partial-sum operator (difference of modulated Riesz
projections), tensorized across the three axes. True physical
helical H± are uniformly bounded L4 zero-order periodic Riesz
operators. Hölder/cross-product inequality plus H^(3/4)->L4
thus gives, for ALL N and real divergence-free u0∈H^(3/4)(T³),
  E_M,N(0)
    = Σ_(k∈original nonzero cutoff)|M_(N,k)|²
    ≤ C ||u0||_(H^(3/4))⁴.
For H¹ initial data, interpolation immediately gives
  E_M,N(0) ≤ C sqrt(E0)(E0+D0)^(3/2).
The bound is cutoff-independent and does NOT depend on a
periodic unit spectral gap. This is a mathematical proof via
classical Fourier multiplier/Sobolev theorems, not yet an inhabited
Agda record. Source and provenance:
`Docs/research/ns_r699_initial_mass_cutoff_young_20261025.md`.
The two exact physical L4/Parseval tests
`tests/test_ns_r699_h34_l4_physical_endpoint.py` passed locally.

**Do not confuse this successful L4 initial PRODUCT bound with the
historical failed L4×L4 BERSTEIN shortcut for the *derivative-bearing*
A2 triadic shell inequality in
`NSTriadicShellBernsteinHolderBoundary.agda`. That latter target
requires a sharp 2^min(j,k) commutator factor and is NOT proved
by generic L4 Holder. Similarly,
`NSTriadKNPeriodicUniformHarmonicAnalysis.agda` records a
`youngConstantSq` and `integerLatticeYoungConvolution` as
UNINHABITED RECORD FIELDS, not source-exact analytic theorem terms.
Reuse its interface only after a genuine normed physical
instantiation and independent kernel checking.

The physical heat-shear energy-only initial-mass no-go remains
valid: fixed kinetic E=1, E_M,N(0)~N/24 when u0 itself varies
with N. Its H^(3/4) norm increases accordingly.
All universal nonlinear R735 W1/W2 inequalities and
whole-space A continuation remain OPEN.

---

# 2026-10-25 A/B MAX-CUT: R699 INITIAL MASS PAID ANALYTICALLY, ENERGY-ONLY ROUTE EXCLUDED

**Research source:** `Docs/research/ns_r699_initial_mass_cutoff_young_20261025.md`.
Original helical decomposition (Lei--Lin--Zhou, 2015), discrete Young,
Sobolev and Cauchy--Schwarz attribution retained. New physical data
calculations/tests are DASHI contributions, not original analytic
theorems or an unrestricted Clay A/B solution.

**B / rigorously established MATHEMATICAL initial-data ceiling:**
For genuine norm-one helical projectors H± and any fixed divergence-free
u0∈H^s(T³), s>3/2, the literal original mixed field
M_N(k)=Σ_(p+q=k)(H+u0_N(p))×(H-u0_N(q))
satisfies the cutoff UNIFORM bound
  sup_N Σ_(k≠0,|k|∞≤N)|M_N(k)|²
     ≤ [Σ_p(1+|p|²)^(-s)] ||u0||_(H^s)² ||u0||_2².
Proof: projector norm ≤1, cross-product norm ≤product,
discrete Young ell1*ell2→ell2, weighted Cauchy--Schwarz.
This directly provides the analytical standard-data bound requested by
R699's `CutoffUniformInitialMixedMassCeiling`. For unforced
z-direction x/y heat shears, R691's nonlinear commutator vanishes and
W_N(T)+E_M,N(T)=E_M,N(0), so the R735 **W1 inequality is settled on
this restricted exact-solution class**, uniformly in cutoff and T.

**ANALYTIC VS KERNEL boundary:** R699's Agda record is still UNINHABITED
in source for the general physical NS system. The unconstrained
`HelicalModeScalars` rational record does NOT itself entail
orthogonal norm-one projectors on every real Fourier mode. Requires
physically normalized real/complex helical law, literal initial
trajectory tracing, cutoff extension, ell1/ell2 inequality, and a
rational ceiling value for the resulting real constant before R699
can be marked kernel-proved. Do NOT flip the false status boolean.

**Exact negative control:** Smooth real UNFORCED heat shears
  u_N=2/sqrt(2N) Σ_(n=1)^N cos(nx)e_z,
have normalized kinetic energy E=1, but the SAME-N canonical
helical mixed initial mass is
  E_M,N(0)=((N-1)(2N-1))/(48N) ~N/24.
Full generated-output mass=N/12+1/(24N). Therefore a bound on
initial mixed mass in terms of E0 ALONE with data-independent
constant is FALSE; the H^s datum-dependence cannot be silently
removed. This varies initial data with N; it does not violate
uniformity in cutoff for a FIXED smooth datum, nor Clay B.
`tests/test_ns_r699_initial_mixed_mass_young.py` and
`tests/test_ns_r699_energy_only_initial_mass_no_go.py`:
**6 locally passed exact tests** (SymPy 1.14.0; matching independent
local calculations). No exact-GitHub-head pytest or Agda/Lean kernel
run witnessed.

**Actual remaining B critical leaves:** R735 W1 for arbitrary
physical trajectories still needs a cutoff-uniform bound on the
globally SIGNED nonlinear coherent commutator. R735 W2 still
needs a noncircular positive-margin augmented critical weighted
payment; the auxiliary R823 universal reserve shortcut is
source-written-refuted on an exact real Galerkin trajectory in
`dashi_lean4`, pending independent kernel verification. Reuse R691,
R699, R735, R817 and later Lean proof owners; NEVER reintroduce
padding-dependent R236 B4 or outputwise positive R690.

**Actual remaining A interfaces:** `NSClayFacingAPhysicalSameObjectCutExact`
and `NSClayFacingATwoPhysicalSeamCompilerExact` still require
source-exact canonical continuum pair population, high-frequency
same-object physical heat rate, and low/high majorant domination.
The high-frequency source record stores a rational `outputHeatRate`
and demands exact Bishop-real equality with ν|xi|²; this equality
cannot simply be assumed at GENERIC real frequencies with
irrational rates. The correct real-continuum producer must either
use a genuine Bishop-real rate/curvature bound or justified rational
brackets (and show their effect on the existing theorem). The
physical H¹→dot-H½/Duhamel estimate is good but no A3 continuation.

**Phase:** one standard-data hypothesis paid mathematically; direct
formal instantiation and BOTH universal W1/W2 positive inequalities
open; original A1/A2/A3 research open; no unrestricted Clay A/B
theorem, typecheck receipt or proof-complete status.

---

# 2026-10-25 A/B MAX-CUT — CURRENT OWNER RECONCILIATION

**READ FIRST / supersedes earlier R690-first claims below.** The user-selected
target is unforced A/B. Prior algebra should be REUSED, never redone as a
new RNNN. Mathematicians/source authorship preserved; a repo theorem name,
a source-written Lean/Agda proof, independent kernel typecheck, accepted
external result and unrestricted Clay theorem are DIFFERENT claims.

## B: existing later owners dominate our R690 work

- **R691** `NSTriadKNR650GlobalMixedEnergyBalanceRound691Exact` already
  proves original weighted work = global coherent commutator integral -
  terminal-minus-initial mixed energy. Do not rediscover this as new
  nonlinear coercivity.
- **R699** `NSTriadKNR650GlobalMixedEnergyEndpointUpperRound699Exact`
  already isolates the initial mixed mass using terminal nonnegativity,
  with the cutoff-uniform commutator and initial-mass ceilings still
  typed as **uninhabited inputs**.
- **R735** `NSTriadKNR650SharedWeightedQuarticCutRound735Exact` already
  defines the preferred TWO shared-weighted analytical leaves: W1
  (weighted plus terminal mixed endpoint payment) and W2
  (augmented critical weighted growth/payment). These are conditional
  proof compilers, NOT automatically supplied estimates.
- **R817/R823/R828–R853** explore the signed-orbit/reserve route.
  Importantly the newer real-time literal Lean owner
  `chboishabba/dashi_lean4/NSBControl/Rational345R823DecisionFreeze.lean`
  already includes `literalPhysicalReserveIntegralCounterexample`
  with the real R760 original-multiplicity physical reserve/demand
  semantics and the actual radius-4 Galerkin ODE. This is SOURCE-WRITTEN,
  its exact-head independent kernel receipt is STILL unwitnessed here;
  it refutes an **auxiliary universal reserve claim**, not Clay B.
  Do not revisit the historical Agda R832 'real ODE outstanding'
  ledger as authority over later Lean source. Do not revive the R823
  universal reserve shortcut in a supposed positive B argument.
- `NSClayFacingBPostReserveMaxCut20261002Exact` independently records
  six positive-route leaves: B1, B2, B3, B4 strict critical signed
  operator, B7 actual R406 equality, and B continuum continuation.
  Check the REAL interfaces/quantifiers before reducing this to 'one
  remaining estimate'. The older full-fibre count-centered B4 payment
  is falsified under zero-amplitude padding; its source-written
  corrected R236/R685 equality is algebra, not a rescue.

## NEW realizable physical signed R690 discriminator

`tests/test_ns_r690_realizable_helical_signed_output.py`
(4 independently executed exact SymPy tests; original fixture). Take
Fourier modes p1=(1,1,0), q1=(1,-1,0), p2=(0,2,0),
q2=(2,-2,0), their conjugate negatives; modal velocities
u_p1=u_q1=u_p2=e_z, u_q2=-e_z. All have real-valued
trigonometric u pointing along z, independent of z, so the
UNFORCED Navier–Stokes convection vanishes, and each mode follows
the exact heat trajectory exp(-|p|²t). The physical helical source
is LITERALLY the existing canonical projector
`H±=(P ± i p×/|p|)/2` and mixed product H+u_p×H-u_q.
For output k=(2,0,0), the four ordered active incidences give
rτ={4,4,12,12}, and at t=0:
  K_k=Σ rτ W(M,Aτ)=8-6 sqrt(2) <0,
  physical output-heat self-work=2-sqrt(2)>0,
  signed difference-frequency work=6-5 sqrt(2)<0.
Thus **the difference term can dominate even on an actual smooth
unforced NS solution**: outputwise R690 rate-work positivity is FALSE.
At this output the mixed norm initially grows since
`d||M_k||²/dt=-K_k>0`, and for sufficiently small positive T,
`int_0^T K_k<0`; as T→∞ the same integral equals the initial
mixed norm, which is positive. Crucially the FULL global signed
sum over all 26 nonzero output modes for this particular seed is
`192-16 sqrt(2)>0` at t=0. **Do NOT claim a global R690 sign
counterexample from this single output.**
 The same exact heat
trajectory gives the stronger COMPLETE 26-output integral
`∫_0^∞ Σ_(k≠0) K_k(t)dt = 12-sqrt(2)` and R690's
eightfold value `96-8sqrt(2)`, confirming R691's original
mixed-energy endpoint. This is checked in the fourth local test,
not inferred from a static single output. This is a source-realizable
gate against careless positivity or per-output absolute-value
arguments, and supports the existing R691/R735 sum/endpoint-first route.

## External 2026 flux claim negative control (conditional on its meaning)

Luca Eliseo Pavesi, `Global Regularity for the Three-Dimensional
Incompressible Navier–Stokes Equations via Geometric Frustration and
Helical Quasi-Trapping`, Zenodo 21194906 (2026-07-04 v3),
https://zenodo.org/records/21194906 , claims in its abstract an
unconditional spectral flux inequality
`|Pi(K)| <= C sqrt(E_>K) sqrt(E)/K` with ABSOLUTE C.
Our independently evaluated physical real/transverse six-mode triad
has conventional standard nonlinear kinetic spectral flux
`Pi(1)=4`, E=10, E_(>1)=6. Scaling velocity u→a u:
left side=4a³, asserted right side=C sqrt(60) a².
No fixed absolute C can satisfy this for all a>0.
`tests/test_ns_pavesi_unconditional_flux_scaling_audit.py`
(1 independent local SymPy test). Thus its ABSTRACT'S stated
unconditional bound is incompatible with conventional flux if
universal over unnormalized smooth data; this is not a blanket
refutation of different flux definitions or the author's distinct
helicity-dominance CONDITIONAL results. Original attribution remains
Pavesi; the scaling discriminator is DASHI's independent calculation.
Neither preprint is imported as proven global regularity.

## Remaining concrete positive A/B max-cut

- **A:** physical H¹→dot-H½ stationary Stokes and L²_t Duhamel
  estimates ALREADY known from prior cut; they are supercritical
  in spacetime. Audit the REAL Bishop two-seam owners and prove an
  unconditional same-solution critical continuation bound before
  marking A3 closed. Do not translate a static scalar inequality into
  a finished Clay A.
- **B:** prioritize the ORIGINAL R735 W1 and W2 analytic inputs
  and B-post-reserve B1/B2/B3/B4/B7/continuation requirements;
  use R690's no-cardinality normal form as a convenient exact
  coordinate, NOT a sufficient uniform bound. Test proposed signed
  payments against (i) the exact zero-padding shear, (ii) the new
  REALIZABLE negative output-rate heat shear, and (iii) the already
  source-written R823 rational-345 integrated physical reserve
  counterexample. Avoid another proof 'by finite algebra alone'.
- **Verification:** 5 local exact SymPy tests passed on the new
  physical negative-output and external-flux witness modules. These
  sources are committed to PR #1240. No Agda/Lean kernel toolchain or
  exact-PR-head test run in this runtime. No direct unrestricted
  A/B theorem or rigorous uniform signed global estimate is claimed.

---

# 2026-10-25 priority gate: B NO-CARDINALITY RATE ALREADY PROVED — R690 FIRST

**User objective:** unforced NS A/B; no detour to C/D publication.
Original authorship of the Navier–Stokes PDE, Fourier/heat semigroup,
Littlewood–Paley/Bony classification, Sobolev embeddings, and the
pre-existing DASHI R685/R690/OutputRate theorem terms is preserved.
This cut's original contribution is an independent theorem-owner
**specialization, scalar padding-cocycle proof and adversarial test**.
No original Clay regularity theorem is claimed.

## B true minimal route (supersedes six-block covariance as analytic target)

The pre-existing source
`NSTriadKNFixedOutputPhysicalOutputRateNormalFormExact.agda`
ALREADY proves a genuinely padding-invariant same-output identity:
  r_(p,q)=ν(|p|²+|q|²)=ν|k|²/2+ν|p-q|²/2.
For M_k=Σ A_(p,q), work W=2 Re Hermitian pairing,
  K_k=Σ r_(p,q) W(M_k,A_(p,q))
     =ν|k|²/2 W(M_k,M_k)
       +ν/2 W(M_k,Σ|p-q|² A_(p,q)).
The full R685 commutator/tangent rate identity also supplies
  K_k=W(M_k,commutator_k)-W(M_k,tangent_k).
**Reuse, do not rebuild, these existing exact source owners.**

New actual R685 specialization (same physical Galerkin system,
velocity, projected nonlinear forcing, literal output fibre):
`r685PhysicalModalRateIsOutputRate`,
`r685PhysicalNoCardinalityRateNormalForm`,
`r685PhysicalRateKernelIsOutputHeatPlusDifference`,
`r685InputLaplacianIsOutputHeatPlusDifference`.
They apply the pre-existing `OutputRate` proof to R685/R684's
actual input-Laplacian work, which is the quantity later summed in
R690. The resulting exact global signed **candidate integrand**
(for the existing R690 factor 8) is
  4ν Σ_k [ |k|² W(M_k,M_k)
            + W(M_k,Σ_(p+q=k)|p-q|² A_(p,q)) ].
The FIRST summand is nonnegative for ν>0; the SECOND work can be
negative on arbitrary complex mixed-cell data. Hence no sign/payment
can be inferred by inspecting multiplier positivity alone. R690
already performs output SUM BEFORE integration/estimation; reuse it.

**Historical R236 firewall:** The previous source-written six-block
identity
  ν criticalTouching = R W(M,M)-nK-ν deepOnly
is algebraically correct as a conditional source compilation, but
the source-defined n and R depend on ZERO-amplitude fibre padding.
It is NOT a uniform physical energy estimate. No changes to its
valid algebra or historical attribution. New general scalar-list
proofs in `NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact`:
`pairAgainstHeadAppendZero`, `pairDifferenceAppendZero`,
`centeredPairCovarianceAppendZero`, exhibiting exactly
  C_padded-C = r_new W(M,M)-Σ r_i W(M,A_i).
On the already existing physical shear k=(1,1,0) with two core
cells, this equals r_new-2 even when every added velocity amplitude
vanishes. For a high-high-to-low row
p=(N,0,0), q=(1-N,1,0), r_new=2N²-2N+2,
the single-row core-touching increment is 2N²-2N; the
actual full literal cube grows even faster (already fully proved by
`scripts/ns_b4_literal_padding_adversary.py`).
Physical energy/dissipation remain E=D=4. Auxiliary bound falsified,
**NOT** NS regularity. Crucial distinction: adding one incidence is a
partial-fibre algebra test; the existing all-cutoff cube computation
is the actual cutoff theorem.

**Nonnegativity firewall:** with abstract complex cells one can have
W(M,Σ|p-q|² A)<0 while |p-q|²>=0; see
`tests/test_ns_b_output_rate_signed_frequency_negative_control.py`.
That test is NOT yet a helical physical-realizability theorem and
cannot establish a physical sign failure by itself.

**Next B theorem with actual effect:** prove for ALL literal Galerkin
trajectories, cutoffs and physical selected helical modes an integrated
cutoff-uniform **signed** estimate on the R690 no-cardinality global
input-Laplacian/commutator integrand sufficient to discharge B's
continuation criterion. Positivity of a subterm or finite algebra
alone is not it. Avoid another n-weighted R236 B4 attempt.
`NSTriadKNR650GlobalSignedRateLiftInputLaplacianRound690Exact`
already defines/sums/integrates the precise signed object; there is
no mathematical reason to duplicate the aggregator.

## B direct R689/R690 source owner continuation, not just fixed-output

The existing `NSTriadKNR650RateLiftedInputLaplacianCancellationRound689Exact`
now exposes `outputHeatSelfWork`, `centeredDifferenceWork`, and the
source-written identity
`inputLaplacianIsOutputHeatPlusCenteredDifference` on the actual
R689 physics owner.

The existing `NSTriadKNR650GlobalSignedRateLiftInputLaplacianRound690Exact`
now has the source-written SAME-TRAJECTORY consumer
`sameGlobalSignedObjectNoCardinality`: output-by-output
 `8 nu W(M,L_in) = 8*(outputHeatSelfWork+centeredDifferenceWork)`,
summed over the ORIGINAL literal nonzero cutoff outputs. Its
`integratedOriginalR690IsNoCardinality` transports the identical
global pointwise equality through the existing
`R495.integrateCongruent`. The decomposition is performed under the
same signed SUM before integration: it does not take outputwise
absolute values or invent an integrability/positivity lemma.
**No new signed B spacetime bound is proved.**

The new exact physical unforced shear time-trajectory test
`tests/test_ns_r690_integrated_physical_shear_no_cardinality.py`
at k=(1,1,0) has M(t)=e^(-2t) M(0), K(t)=2 e^(-4t),
R690 integrand 8K(t)=16 e^(-4t), hence
`integral_0^T 8K(t)dt=4(1-e^(-4T))`.
The same shear has pointwise nonlinear forcing zero. Adding zero
high-frequency mixed-cell rows does not alter K(t), while the
full-fibre count-centered covariance changes by
`(r_new-2)e^(-4t)`. This is a time-dependent same-PDE solution
rather than an arbitrary static polynomial witness.

The primary implementation and research delta is now exact:
**R690's physical source is fully expressed in padding-free rate
coordinates.** Remaining claim "complete B" requires actual
cutoff-UNIFORM physical signed estimate + B7 continuation, with
physically selected amplitudes and boundary/commutator corrections.
A strict relative payment inherited from the falsified R236
full-fibre B4 cannot be silently assumed.

**Updated local receipt:** seven independent matching Python/SymPy
checks passed in the current turn; the committed GitHub tests are
source-written without an exact-head pytest receipt, and the Agda
term insertions remain untypechecked in this runtime.

## A actual remaining continuation hinge

The previous cut's physical H¹ dual-Sobolev estimate is good:
  ||(-νΔ)^(-1)Pdiv(u⊗u)||²_(dot H½) <=K² E D/ν²,
and its causal Duhamel L²_t dot H½ bound is independent of T.
But under NS scaling the squared spacetime norm scales λ^-2,
so it cannot substitute for critical Serrin/BKM/global A3.
The already provided whole-space Schwartz/Fourier source owner and
Bishop canonical continuum carriers remain source targets.
The next theorem must CONTROL a same-solution continuation-critical
norm noncircularly, not merely improve an L² source majorant.

## Execution/verification boundary

Independent exact local Python/SymPy tests:
`/mnt/data/ns_ab_current_cut_checks.py`: **5 passed** (algebraic
padding cocycle, shear critical-fibre row, output-rate decomposition,
negative signed-frequency-work witness, scaling).
The additional GitHub regression files are source-written; an
independent exact-PR-head pytest was not available in this environment.
**No Agda/Lean kernel typecheck** of new source terms (toolchains
absent), and no universal cutoff-uniform B estimate or A3 proof.
This is a significantly narrower analytic roadmap, not
a completed unrestricted Clay A/B proof.

---

# 2026-10-24 A/B DECISIVE SAME-SOURCE RECUT — DO NOT REOPEN OLD LEAVES

**Research goal is original unforced Clay A/B**. This update supersedes
the older source notes below describing the H² logarithmic Fourier bound
as the primary A branch and the covariance↔R685 rate weld as missing
algebra. Original authorship of classical Sobolev, Leray and Bony
machinery remains with those sources; DASHI owns only these exact
compositions and source tests.

## B: NEW SOURCE-WRITTEN CORRECTED CRITICAL-TOUCHING THEOREM
In ORIGINAL owners
`NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact.agda` and
`NSTriadKNFixedOutputPhysicalCriticalRegionPaymentLiveExact.agda`,
the physical mixed-product fibre has M=Σ Aτ (bilinear in velocity),
D=-Σ rτ Aτ, n=length fibre, R=Σrτ. The R236 covariance:
  C=n W(M,D)+R W(M,M)
   = R W(M,M)-n K,
  K=Σ rτ W(M,Aτ)
   = W(M,commutator)-W(M,tangent)  [original R685 owner].
R236's six region-pair blocks already give
  C=ν(deepOnlySigned+criticalTouchingSigned).
The new actual theorem composition states, **without dividing by ν**,
  ν criticalTouchingSigned
   = R W(M,M)
     - n[W(M,commutator)-W(M,tangent)]
     - ν deepOnlySigned.
This includes the original deep complement, fibre-rate centering and
physical commutator/tangent endpoint. The previously falsified
padding-dependent B4 *inequality* has NOT been rehabilitated.

**Exact local numerical regression:** literal same-output triads
k=(64,1,0) with DFL, DHH and Core rates, ν=2:
covariance=780398656, signed deepOnly=162531800,
signed criticalTouching=227667528. Hence ν critical=455335056,
equal to covariance−ν deepOnly. Algebraic checks also confirm
the rate/kernel and complex-work same-object arithmetic.
`tests/test_ns_original_r236_r685_rate_bridge.py`.
Agda source-written theorem terms committed; **kernel unchecked**
(no Agda toolchain available). R690 provides the later global signed
sum but no estimate; original B1/B2/B3/B4/B7 quantitative obligations
are not thereby proved.

**Distinct cubic enstrophy firewall:** physical vortex stretching
is degree 3 in velocity. Mixed-helicity covariance C is degree 4.
An uncompensated universal C=stretching equality is impossible
on a nonzero-stretching datum by amplitude scaling. Abstract
no-go proof is source-written in
`dashi_lean4/NSUnforcedAnalyticCuts.lean` (kernel unchecked).
The exact classical curl identity is now source-written in
`NSTriadKNFourierBiotSavartExact.agda`: ordered curl defects
cancel under (p,q) input swap for transverse modes. For R236 this
occurs on the MERGED deep-far-low region, deep-high-high, and Core,
not on oriented LH and HL separately. Numerical regression corrected
the earlier overly strong oriented-region assertion.
`tests/test_ns_r236_swap_closed_production.py`.

## A: STRONGER GENUINE CRITICAL SPATIAL FOURIER ESTIMATE
The previously derived pointwise bound
`min(E r,sqrt(E D))` had a logarithmically divergent Hhalf radial
*majorant*. That does NOT obstruct the actual physical source. From
dual homogeneous Sobolev `L^(3/2) -> dot H^(-1/2)` and
`H1 -> L6`, with actual physical
`V=(-ν Δ)^(-1)P div(u⊗u)`, one has
  ||V||_{dot H^(1/2)}
    <= K/ν ||u||_L3²
    <= K/ν sqrt(E D).
This bound is invariant under 3D NS spatial scaling and requires
only divergence-free H¹, not H² or a frequency cutoff. The source
field is unchanged; no unrelated `FourierTransformVelocity : Set`.
Causal heat-kernel contraction further yields
  int_0^T ||W(t)||²_{dot H^(1/2)} dt
    <= K² E0²/(2ν³),
for the actual nonlinear Duhamel W under the energy inequality.
Derivation and exact exponent/scaling audits:
`scripts/ns_a_critical_h1_dual_sobolev.py`,
`tests/test_ns_a_critical_h1_dual_sobolev.py`.
The older conditional `scripts/ns_a_critical_h2_log_majorant.py`
is retained for comparison only; it is NOT the canonical A input.

**Still unpaid A3:** time-`L² dot Hhalf` scales as λ⁻², so its
uniform-in-T energy estimate is NOT a scale-critical spacetime
Serrin/Kato continuation norm. The energy interpolation gives
`L⁴_t L³_x`, where 2/4+3/3=3/2>1. Need actual
unconditional critical continuation control, not scalar-bound
repackaging. Bishop/Agda same-continuum-trajectory formal inhabitant
and direct A3 are still missing.

## Verification and phase
- New source-written B finite algebra proof terms and tests in
  current PR #1240. Local SymPy independently checked the all-vector
  swap polynomial identity, corrected three-region cancellations,
  exact B six-block corrected-rate identity, and A radial integrals/
  scaling. Exact current GitHub head pytest and Agda/Lean kernel are
  **NOT WITNESSED** in this cut.
- Proof phase: B **same-fibre equality source-written**; its strict
  cutoff-uniform global signed estimate and continuation remain OPEN.
  A **physical H1 critical-spatial bound analytically available**;
  same-trajectory Bishop theorem and A3 continuation remain OPEN.
- Never promote bool status fields or algebraic source strings to
  a completed unrestricted Clay A/B theorem.

---

# 2026-10-24 A/B physical source max-cut — read FIRST

**Primary objective remains original unforced A and B.** No Clay
promotion. This update reuses actual historical owners rather than
creating RNNN aliases. Executable source and mathematical arguments:
`Docs/research/ns_ab_ri_euler_no_go_and_physical_stretch_20261024.md`,
`scripts/ns_physical_vorticity_partition.py`,
`scripts/ns_a_physical_duhamel_maximal_l2.py`.

**B substantial same-field mathematical step:** a complex physical
Fourier calculation with the exact R63 strict LH/HL/HH/CC classifier
and nested R236 deep/critical decision proves, by vector-curl
identities and finite signed summation, that nonlinear enstrophy
production equals physical vortex stretching on arbitrary tested
finite real divergence-free trigonometric fields. It also exposes the
actual classwise curl/transport **compensation**, not just the total.
For p=(1,0,0), q=(0,1,64), the classwise triples
(P,T,S,residual=P-T-S) are:
LH=(4,0,0,4), HL=(-16392,-4,-16384,-4),
HH=(4,4,0,0), CC=0. Total P=S=-16384,
total T=residual=0. Naively demanding classwise P=S is false.
The script checks the vector curl identity at *all generated
outputs* before contracting, energy/transport cancellation, and
partition sum equalities, without zero-padding sensitivity.

**Important PRE-EXISTING reusable Agda phase proofs:**
`NSTriadKNComplex3RealityLawsRound35Exact` proves
conjugation-compatible Leray projection;
`NSTriadKNCurlRealityHelicalTransportRound93Exact` proves
Fourier curl/reality/helical transport;
`NSTriadKNExactComplexModalTransfer` contains a genuine complex
real/imag exact ring;
`NSTriadKNLuoGalerkinFourierVorticityConvolutionExact`
contains the rational factored-phase vorticity interaction;
`NSTriadKNLuoProjectedConvectionOfficialParsevalUpgradeExact`
already reuses physical hard-high projector, Parseval and derivative
commutation, with explicit incidence multiplicity and energy-flux
agreement fields STILL requiring inhabitants. Reuse all of these.
The remaining B task is the **exact same-source assembly** from
this physical curl/enstrophy function to R236's literal selected
consumer, including the distinct differentiated Com term, into
R685/R690's mixed-helical commutator with exact compensation,
then a positive signed cutoff-uniform B1/B2/B3/B7 estimate.
The new classifier test is not an Agda proof of that attachment.

**A full-time nonlinear source improvement:** From existing physical
H1 stationary Stokes `Vhat=Fhat/(nu|xi|²)` and energy estimate,
the actual causal heat response `What=h_a*Vhat`,
`h_a(t)=a e^{-at}1_{t>=0}`, `a=nu|xi|²`, is an L2 contraction
by Jensen+Tonelli. Hence for an unforced energy solution wherever
the distributional Duhamel identity is justified,
`||What||²_(L²[0,T] L²xi) <= 4 sqrt(2) pi E0² sqrt(T)/nu^(5/2)`.
Source `scripts/ns_a_physical_duhamel_maximal_l2.py` has exact
nonstationary and sign-changing kernel checks. This does NOT
close the signed centered double-resolvent A2 or scale-critical
continuation A3: spatial-temporal L2 remains supercritical under
concentration. Existing physical same-object and Bishop source
owners are unchanged.

**Local receipt:** standalone matching Python scripts: 15 passed (one local duplicate deselected),
including 6 physical complex-field checks, 5 source-classifier/curl
checks, 3 causal heat checks, 2 prior coarea checks. Exact-GitHub-head
pytest and Lean/Agda kernel not performed, so do not mark source
commits kernel-proved.

**Next max-cut acceptance tests:**
1. Construct the actual Agda phase-preserving nonlinear/curl
   and selected Bony+Com adapter by consuming Round35/Round93/
   OfficialParseval and the original R236/R685/R690 theorem terms.
   Pin the +8, -16384, classwise +4/-4 and old shear projection
   negative-control witnesses; the target must express every
   compensation, not merely numerical agreement.
2. Instantiate A's same-physical-continuum Fourier/Plancherel
   transformation and causal Duhamel semigroup in existing Bishop
   carriers. Do NOT rederive scalar kernels.
3. Close a genuinely cutoff-uniform, viscosity-dependent, scale-critical
   signed physical estimate sufficient for A3/B7, without assuming
   the desired continuation. Ri's stronger viscosity-uniform headline
   estimate remains excluded conditionally by the released Euler
   blowup and inviscid limit.
4. Only actual kernel builds and direct unrestricted continuation
   proofs authorize an A/B theorem-complete status.

---

## 2026-10-24 completed local physical PHASE-preserving realification check

The fifth test `test_exact_real_imag_six_vector_bridge_preserves_work`
in `tests/test_ns_physical_vorticity_production_exact.py` performs the
ENTIRE six-mode Leray/curl/production computation a second way, using
explicit rational pairs `(Re,Im)` and multiplication
`(a,b)*(c,d)=(ac-bd,ad+bc)`, with `i` represented by `(-b,a)`.
It reproduces +8 nonlinear enstrophy and +8 vorticity stretching
independently of SymPy's native complex arithmetic.

**Local Python receipt:** 5 passed in 0.56 s on a matching standalone
test (SymPy 1.14.0). This proves exact arithmetic correctness of the
specific finite witness and rejects naive real-part projection; it
does NOT yet give an Agda theorem transporting the full complex
physical Galerkin field into Round42's rational real carrier or R236.
The concrete phase-preserving adapter is the B representation cut
that should precede the actual quantitative analytic payment.

---
## 2026-10-24 exact PHASE discriminator: real-only Round42 input is insufficient

`NSTriadKNLuoGalerkinFourierVorticityConvolutionExact` explicitly
uses a rational **real** vector carrier and states that the common
complex phase `i` is factored out; full reality pairing is not
provided there. The already-proved Round42/43 scaling theorems remain
valid in their stated rational carrier, but source equality to actual
complex Fourier production cannot be achieved by simply taking real
parts of coefficients.

**New exact test** `test_real_part_only_map_loses_helical_phase_and_stretching`
in `tests/test_ns_physical_vorticity_production_exact.py`:
the original six-mode physical complex u has nonlinear enstrophy
production +8; replacing each Fourier coefficient by its componentwise
real part yields production 0 on the same modes. The other tests
check transverse reality, energy 0, sign reversal, zero padding,
cubic amplitude scaling and direct vorticity-stretching equality.
Locally **4 pytest passed** on a matching standalone copy.

**Bridge acceptance** before Round42/43→Round39/R236/R685/R690
consumer: map complex coefficients via exact `(Re,Im)` doubling or
conjugate-pair realification, prove preservation of all i factors,
Fourier signs, physical Leray/curl, work pairing and Bony selector;
then identify the signed selected critical production and actual
residual. This is a narrower genuine same-object weld, NOT a
reconstruction of the already-proved rational algebra.

---
## 2026-10-24 important B PRE-EXISTING PROOF OWNER reconciliation

The newly committed positive-vortex-stretching six-mode witness is an
**independent exact physical calibration**, NOT the origin of the amplitude
scaling theorem. The repository ALREADY contains:

- `NSTriadKNLuoVorticityStretchingSignExact`: source-written
  symmetric-strain/antisymmetric cancellation and enstrophy sign laws;
  original literature Constantin–Fefferman and Evan Miller.
- `NSTriadKNHHBadLiteralProductionDissipationScalingRound42Exact`:
  genuine Agda terms for the inverse-SQUARE frequency scaling of
  physical literal vorticity production versus dissipation, with
  explicit source-owned semantic caveats.
- `NSTriadKNHHBadAmplitudeHomogeneityRound43Exact`:
  genuine source-written Agda terms for amplitude-trilinear
  production versus amplitude-quadratic viscous charge.
- `NSTriadKNHHBadRestrictedGainDensityRound39Exact` and
  `NSTriadKNHHBadLiteralPositiveGainRound43Exact`: prior original
  `rawGain`/positive-gain consumers. Their source-exact weld to
  the physical vorticity production is explicitly NOT automatic.
- `NSVorticityStretchingExactReceipt` is ledger-only, NOT a
  verified general Euler/NS field identity.

**Revised cut:** reuse these originals first and require an exact
`physical NS curl/Leray production → Round42/43 vorticity interaction
→ Round39 rawGain → R236 selected critical production/R685/R690`
same-object diagram, recording each leftover compensation. The
nontrivial six-mode witness (+8 enstrophy) and zero-shear witness (0
physical production despite -4 unprojected R681) are complementary
adversarial gates. Do not reconstruct the already-proved homogeneous
algebra or confuse a static receipt with a proof.

---
# 2026-10-24 decisive A/B max-cut — DO NOT IMPORT RI AS A3

**Read first.** Full source/argument/provenance:
`Docs/research/ns_ab_ri_euler_no_go_and_physical_stretch_20261024.md`.

**A RESEARCH DECISION:** Ri arXiv:2601.15685v1 Theorem 1.1 (1.3)
claims a global H^s estimate with a bound depending only on s, not
viscosity. For the smooth compact-support datum of OpenAI's released
unforced Euler singularity (existing source owner
`NSOpenAI2026EulerToClayFourAlternativeBidiExact`), choose s>5/2.
Pre-singularity inviscid convergence + weak lower semicontinuity would
give the same global-in-time-on-[0,T*) H^s bound on Euler, hence a
uniform C¹ bound via Sobolev embedding. This contradicts the released
Euler blowup. **The claimed viscosity-uniform estimate is incompatible
with the released Euler theorem and standard inviscid convergence.**
Do NOT import Ri's Theorem 1.1 as A3. This does NOT refute
positive-viscosity NS regularity at fixed ν. Distinguish all source
statuses. The new `dashi_lean4/NSEulerRiUniformViscosityNoGo.lean`
proves only an abstract conditional upper-bound transfer; actual
Sobolev and inviscid-limit welds are not kernel checked.

**B EXACT NONVANISHING PHYSICAL REGRESSION:**
`tests/test_ns_physical_vorticity_production_exact.py` (locally 3
passed, exact SymPy). Six real/transverse Fourier coefficients
±(1,0,0), ±(0,1,2), ±(1,1,2) give zero nonlinear kinetic energy
production, +8 nonlinear enstrophy production, and +8 from twice
physical vortex stretching. Flip a phase → -8, zero-pad → unchanged.
State has E=10, enstrophy=38 and palinstrophy=198. Under u→a u,
stretching ∝a³, viscous dissipation ∝a²; at a=50, ν=1,
instantaneous enstrophy derivative=10000. So fixed constant
dissipation-only payment fails even on smooth physical initial data.
This is NOT a blowup example.

**LIVE B TARGET:** prove actual source-equality/compensation between
Leray-projected physical spectral production and R236's selected
critical production through R685/R690 with original carrier
definitions and all complementary regions. R685 proves mixed
commutator-minus-tangent, not this u/omega identification; R690 is
finite signed sum, NOT a physical analytic estimate. The old full
fibre B4 payment is false. The nonzero enstrophy witness is a
mandatory acceptance test for any purported same-object bridge.

**LIVE A TARGET:** same physical continuum Fourier transform and
scale-critical continuation for fixed positive ν. Ri's purported
uniform-ν shortcut is excluded, but his *local* frequency identities
may still be useful after independent checking. Never promote
conditional pre-blowup estimates to uniform global bounds without a
noncircular continuation argument.

**Verification:** local SymPy/pytest passed (3 tests); GitHub
commits are source-written; no independent exact-head Lean/Agda
kernel check this cut. A/B universal regularity NOT established.
---
## 2026-10-24 next max-cut — exact coarea calibration and Ri proof entry

**Executed local Python:** `python -m pytest -q` on the new
`tests/test_ns_threshold_coarea_gaussian_exact.py` calculations:
2 passed (SymPy). The radial Gaussian f=exp(-|x|²) has
level |x|=sqrt(-log a); the coarea integrand is
8*pi*a*(-log a)^(3/2). With t=-log a its integral is
3*sqrt(2)*pi^(3/2)/4, exactly the bulk integral
of |grad f|². The critical-root gradient split is likewise checked,
`|grad(f^(3/4)xi)|²=(9/16)f^(-1/2)|grad f|²+
 f^(3/2)|grad xi|²` for orthogonal polar derivatives.
**Scope:** exact calibration, NOT a general measure-theoretic coarea
proof or physical R236/R685/R690 same-object proof.

**Ri critical A source check:** Myong-Hwan Ri, arXiv:2601.15685v1,
Theorem 1.1 (equation 1.3) claims a global inhomogeneous H^s
estimate for d>=3, s>=d/2-1, constant C(s) independent of viscosity
and dimension; Section 3 starts from a maximal local regularity
interval and high-frequency identity (3.6). The manuscript's Fourier
convention is unitary with +i phase, unlike our earlier Gaussian
source script using an unnormalized -i convention. Any import must
account for phase and (2pi) normalization, and audit the transition
from high-frequency bounds to global time-uniform H^s with no
circular dependence on the unknown maximal regularity interval.
No result of Ri promoted to an independently proven A3 theorem.

**Single decisive B continuation:** formalize the full threshold
identity under coarea/trace assumptions, then prove precise identity
of physical vortex-stretching production with the R236 consumer
AFTER the actual helical/physical operator conversion. This is the
same-source bridge, not another amplitude-independent counting
covariance. Physical shell payment and universal continuation still
open.

---
## 2026-10-24 implementation receipts — 4-paper primary text and threshold B donor

Current canonical reference inventory: `Docs/research/ns_ab_four_primary_papers_20261024.md`, whose links resolve to the **full arXiv HTML** v1/v3/v1/v2 manuscripts, not merely abstracts. Do not repeat the erroneous Shahmurov 'Large-Data Global Regularity Part II' title attached to arXiv:2605.01873; its current source expressly disclaims unrestricted 3D regularity.

Source-attributed new executable tests:
`tests/test_ns_shahmurov_vorticity_primary_calibration.py`
tests a nonzero-vorticity region of the *physical* smooth shear against Shahmurov's Lemma 2.1 and checks the exact p=3/2 root.
`tests/test_ns_shahmurov_enstrophy_layer_cake.py` checks p=2 threshold layer-cake coefficients for vortex stretching, endpoint mass, and directional dissipation. This provides an explicit intermediate path to the standard enstrophy balance. The coarea measure-theoretic passage and exact R236/R685/R690 **same-object** connection are NOT proved by these finite/symbolic tests.

Phase: **P0 primary corpus/version/author disambiguation achieved**; **P1 full analytical validation of Ri and Shahmurov open**; **P2 same-carrier formal theorem open**; **P3 physical signed A2/B7 and global continuation open**. Local SymPy checks cover only the stated elementary calibration, no exact-head pytest/Lean/Agda kernel receipt.

Priority remains A/B. Ri: independently audit Lemma 2.1 and high-frequency energy proof before importing Theorem 1.1; its viscosity-independent theorem has strong consequences and requires line-by-line verification. Shahmurov: formalize the full threshold balance on the physical vorticity carrier, then prove link to R236; do not assume it bounds vortex stretching. Cheskidov–Hou: initial-trace negative control. Constantin–Ignatova–Vicol: strictly conditional exclusion given all hypotheses.

---
# 2026-10-24 A/B-FIRST CORRECTION — literature and C/D cross-pollination

**Override the prior C/D-first priority statement below.** User-selected
research goal is original **unforced A/B**. OpenAI's released forced C/D
proofs are existing cross-pollination donors, *not* the next publication
task and not a formal implication of unforced global regularity.

## New primary-source literature audit (authorship preserved)
- Myong-Hwan Ri, "Global regularity for the Navier-Stokes equations
  with application to global solvability for the Euler equations",
  arXiv:2601.15685 (2026-01-22): explicitly claims unrestricted
  large-data global regularity on R^d, d>=3 via sparse
  inverse-logarithmic frequency weights and rescaled frequency tails.
  **Unverified preprint claim, not a confirmed theorem.** High-priority
  candidate for direct comparison with A2 scaling and B signed shell
  control; check the critical norm bound for circular use of regularity.
- Rishad Shahmurov, "Large-Data Global Regularity for Three-Dimensional
  Navier--Stokes II: A Direct First-Threshold Continuation Proof for the
  Full System", arXiv:2605.01873 (2026-05-03): claims a first-threshold
  critical-packet continuation theorem using angular Littlewood--Paley
  triads, rigidity, phase control and leakage accounting. This is a
  **claimed complete proof, not verified here**. Compare B1/B2/B3/B7
  source-weight and compensated signed identity against its threshold
  envelope; verify Part I hypotheses and data generality.
- Alexey Cheskidov and Hedong Hou, "Global existence of smooth solutions
  to the Navier-Stokes equations for initial data with infinite energy",
  arXiv:2610.18797 (2026-10-13): constructs global solutions smooth for
  t>0, with only H^{-s} continuity at t=0 in the leading theorem.
  Distinguish weak/very-weak continuity from official A/B requirements,
  which include smoothness through t=0 and energy/boundedness clauses.
  It is not automatically Clay B.
- Peter Constantin, Mihaela Ignatova and Vlad Vicol,
  "Regularity of asymptotically axisymmetric solutions to the 3D
  Navier-Stokes equations with analytic forcing", arXiv:2609.20803:
  proves rigidity excluding OpenAI-type singular profiles when the
  forcing is analytic/zero under its precise axisymmetry/Type-II
  hypotheses. Import as an **adversarial profile discriminator**, not
  arbitrary-data A/B regularity.

## C/D donor integration — two-way negative control
- OpenAI, "Finite time blowup for Navier–Stokes" (2026-09-08),
  https://github.com/openai/NavierStokesAndEuler : source is smooth
  forced PDE, not unforced; the constructed forcing is essential to the
  exhibited singular dynamics. Its proof tools (anisotropic rescaling,
  profile/core/tail separation, Leray pressure, uniqueness and
  finite-slab comparison) should be reused in A/B only after proving
  same-source f=0 identities. Never set f=0 syntactically in a
  constructed forced solution.
- Compare the unforced vorticity equation and critical norms with the
  released unforced Euler blowup, noting that missing viscous damping
  prevents direct transplantation.
- First actual B discriminator is already in
  `tests/test_ns_b_projection_same_shear_discriminator.py`:
  raw unprojected R681 has global relative work -4 while projected
  helical amplitudes vanish on the same shear; require an exact R685/R690
  compensated physical R236 identity before estimating shell terms.

## Acceptance order (no more numbered aliases)
1. Audit Ri critical norm and Shahmurov first-threshold proof against
   literal unconstrained initial-data A/B statements; identify a
   concrete importable lemma or a failed quantifier.
2. Trace the literal R236 physical production through R685/R690 and
   Leray projection, including residuals, to a signed cutoff-uniform
   inequality. No count-centered B4 revival.
3. Transport the existing Schwartz/H1 same-object Fourier extension
   to the actual Bishop continuum trajectory; produce scale-critical
   A2 and noncircular A3 continuation.
4. Reuse formalized C/D analytic components as lemma donors with
   attribution, not proof of an unrelated unforced implication.
Status: literature sources inspected; no independent verification of
new preprint proof claims or kernel check of A/B complete result.
---
# 2026-10-24 GOAL-1 PHASE GATE — C/D released theorem, A/B independent research

**Read this before the A/B frontier entries below.** Primary external
source: OpenAI, "On the Navier-Stokes Millennium Prize Problem",
2026-09-08, https://openai.com/index/navier-stokes-solution/ and
https://github.com/openai/NavierStokesAndEuler (released Lean code).
OpenAI explicitly reports a forced whole-space blowup (Clay C) and a
forced periodic blowup (Clay D) for every positive viscosity.
Attribute the original construction and Lean certificate to OpenAI;
DASHI's source-coordinate audits and independent-specification bridges
are derivative verification/integration contributions, not independent
discovery of the released blowup.

**Milestone distinction:**
- M0 official C/D source statement and coordinates: **DONE in the
  existing source audit** (`NSClayFacingCDMaxCut20261002Exact`,
  `NSClayFacingCDReleasedAuditFrontier20261007Exact`).
- M1 released Lean theorem/artifact available: **DONE upstream**;
  the upstream README exposes both C/D and build instructions.
  Independent exact-head build by this session: **NOT WITNESSED**.
- M2 independent spec/bridge/submission spine: **EXISTING OWNERS**
  `ExternalClayNS/ClaySpec.lean`, `Gap.lean`,
  `ClauseAudit.lean`, `SubmissionAudit.lean`, and
  `Docs/papers/live/NavierStokesABCDClaySubmissionSpine.md`.
  Source-written existence does not equal current kernel receipt.
- M3 conventional mathematical exposition plus fresh independently
  reproducible kernel/audit receipt: **PUBLICATION/AUDIT WORK**,
  not another C/D theorem-discovery programme.
- M4 independent refereeing, Clay adjudication: **EXTERNAL**;
  do not conflate announced result, proof certificate, referee acceptance
  and prize decision.

**Critical-path decision:** For the primary Clay-facing deliverable,
FREEZE original A/B research as NON-BLOCKING. Publish/audit D first
(shorter periodic route via periodisation), then C; both are already
available in released upstream proof. Do not require DASHI independent
Fourier/369/R406 construction for M2/M3.

**Parallel optional research:** A remains same-physical-solution
Fourier/Plancherel plus scale-critical A2/A3; B remains genuine
compensated R236/R685/R690 physical signed production and estimates.
The falsified count-centered B4 estimate must never be a gate.
C/D success is not evidence of A/B universal unforced regularity.

**Next bounded actions:** Pin upstream commit and theorem namespace,
run upstream `lake exe cache get && lake build` and the independent
`ExternalClayNS` certificate build, record stdout/toolchain/hash;
produce one conventional D candidate/admissibility/uniqueness/breakdown
proof and C counterpart with numbered lemma-to-Lean links. Keep
remaining questions strictly limited to missing proof receipts or
exposition, rather than spawning more RNNN layers.

---
## 2026-10-24 projection gate on physical B recombination (new exact discriminator)

**New exact finite check:** `tests/test_ns_b_projection_same_shear_discriminator.py`
committed on the existing PR #1240 branch. The four Fourier modes
`uhat(±e_x)=uhat(±e_y)=e_z` yield nine possible supported output
frequencies under H+×H−, including the zero output. The eight nonzero
mixed-output vectors are all longitudinal: for EVERY k≠0,
`P_k M_k = M_k-k(k·M_k)/|k|²=0`.
Nevertheless, the unprojected literal R681 physical output-relative
work summed over those outputs is **−4**, not zero.

This is a **necessary projection/representation discriminator**, not
proof that projected H+×H− is automatically the physical convection
operator. For the same real shear, `u·∇u=0` pointwise and
`∂_t u=Δu` for viscosity one. Thus any source-equal representation
of the genuine *projected* NS nonlinear forcing or energy-production
functional must vanish on this witness; the unprojected R681 signed
work fails that calibration.

**Next proof cut:** open the actual R685 commutator/tangent and R690
global compensated consumers; write the exact same-source equality
between their final Leray-projected physical functional and the
original R236 selected Bony critical-production functional, including
all class boundaries and any residual. Only after proving this identity
may one attempt a cutoff-uniform signed estimate. Do not infer
cancellation from a raw sum and do not insert Leray projection into
R681 as an unproved equivalence.

Receipt: independent local SymPy output enumeration verified all
eight projected vectors exactly zero and global raw relative value
−4; source-written regression committed. No checked-out PR-head pytest,
Agda or Lean kernel check has occurred in this cut. No Clay promotion.

---

# Navier–Stokes A/B canonical mathematical roadmap
**Current: 24 October 2026 · source-first / fail-closed**

This is the LIVE owner and acceptance plan, not a list of historical RNNN files. The complete chronological research record has been preserved verbatim in [NS proof-control historical archive](archive/NSProofControlHistoricalThrough20261024.md). Revisit old theorems only by exact-declaration lookup or an explicitly identified missing source lemma.

Run `python scripts/ns_canonical_focus.py --route A`, `--route B` or `--route B4`. No new `RoundNNN`/numbered Lean proof wrappers without mathematical necessity.

## Current results and actual obligations

| Mathematical track | Established mathematics / source receipts | Open deliverable that changes the theorem |
|---|---|---|
| **Original B4 full-fibre uniform payment** | **Falsified as an auxiliary inequality** against actual R109/R219/R469 physical ED by one globally smooth divergence-free shear. The exact literal defect for cutoff N≥9 is `(8/3)N²(2N+1)(3N²+N−2)−840480`, growing as 16N⁵. Core companion = 1,345,859,672 (fixed); output local ED ≤ 4. The theorem is **ordinary exact calculation**, not kernel-verified Agda. | **Retire the proposed bound.** Do not attempt a sharper Young inequality or hide a cutoff-growing scalar as physical ED. |
| **B existing source algebra** | Real fixed-output physical-heat normal form plus original R681 cross-gradient, R684 input Laplacian, R685 forcing-commutator minus tangent and R690 global sum-before-time-integral identities; all source-written prior art. | A source-exact **compensated global identity** from the original selected R236 critical-production functional to the usable R685/R690 quantity, retaining every missing Bony class and tangent term. **Naive R681=old B4 is false.** |
| **B analysis after compensation** | Principal half-bound and shell/Galerkin/compactness compilers exist. | A truly homogeneous, cutoff-uniform **signed** global cross-gradient/commutator spacetime payment, plus actual B1–B3/B7 source estimates and continuation. These are open. |
| **A continuum source** | Actual local Leray-projected divergence cell; standard L² product Fourier identity, exact Schwartz vortex calibration and strong H¹-density stability of the stationary Stokes response. | Kernel-verified **same-physical-solution** Fourier/Plancherel distribution map in the existing Bishop/Agda Euclidean trajectory, not a free `Set`-valued meaning. |
| **A physical direct response bound** | For `E=||u||²₂, D=||∇u||²₂`, `|F[Pdiv(u⊗u)]|≤min(E|ξ|,sqrt(ED))`; direct stationary heat-inverse squared Fourier L² bound `8π E^(3/2)sqrt(D)/ν²`. Strong H¹ variation squared ≤ `8πAB/ν²` for actual tensor/convection L¹ differences A,B. The unforced energy inequality gives a finite-horizon source-response bound. | Transfer to the **canonical signed centered A2 double-resolvent** on one actual NS solution, and prove a *scale-critical* sufficient spacetime estimate. |
| **A3 / B continuum regularity** | Classical continuation / compactness interfaces already formalized conditionally. | Uniform noncircular critical control for **all** qualifying data and a complete global smooth continuation theorem. **Neither Clay A nor B is proved.** |

## Exact falsification / anti-promotion receipts

1. **B4 same physical datum:** on the `2π` torus, `u(t)=2e^{-t}(cos x+cos y)e_z` is an exact smooth unforced solution. Original mixed-helicity source has zero-amplitude padding rows even though the underlying velocity remains fixed. `scripts/ns_b4_literal_padding_adversary.py` implements strict R63 classification and the all-cutoff degree-five formula. Corresponding `tests/test_ns_b4_literal_padding_adversary.py` checks power sums, ED provenance and zero-row increments. The original Agda primitive output fibre includes zero-input incidences; `NonZeroPhysicalTriad` is a separate predicate.
2. **B physical global discriminator:** R681 uncentered weighted work is zero-padding invariant, **not equal** to the old B4 defect. Exact H± calculation for the same shear has eight nonzero mixed outputs: four `k=(±1,±1,0)` with `W(M,M)=1` and output-relative rate work zero, and four `k=(±2,0,0),(0,±2,0)` with `W(M,M)=1/2` and output-relative work `−1` each. The **global output-relative R681 work sums to −4, not zero**. Those latter mixed amplitudes are longitudinal; do not silently replace unprojected R681 mixed amplitudes by physical Leray-forcing terms. The R685 forcing/tangent compensation is therefore a real proof obligation, not automatic summation cancellation.
3. **A critical-scaling discriminator:** under `u_λ(x,t)=λu(λx,λ²t)`, `E_λ=E/λ`, `D_λ=λD`, and direct stationary Stokes Fourier response squared L² scales as `1/λ`. It is *supercritical* and cannot alone produce a global A3 continuation criterion.

### Pointwise W2 sign gate (physical R850 snapshot; separate from B4)

The existing R741 and R815/R853 identities on one literal rational
physical packet give `signedRate = 6*(Combined - PacketSurplus)`.
R850's actual radius-four 3-4-5 finite snapshot, at `nu=delta=1`,
has `C=-557627/125`, `P=0`, `D=15834`. Therefore

```text
Combined - PacketSurplus = 12 C - P + D = -4712274/125 < 0
signedRate = 6*(Combined-PacketSurplus) = -28273644/125.
```

This disproves **unrestricted pointwise W2 nonnegativity** on that
physical rational snapshot. To claim a short-time **real integrated**
W2 counterexample, cross-check the Lean R823 physical trajectory and
the EXACT real R815/R853 same-object identification; Agda's
`round853RealTrajectoryCarrierWeldClosed=false` remains a gate.
Do not create another W2 proof record or attempt a universal
pointwise inequality invalidated by this datum. This is a
research-route discriminator, not an unforced Clay proof.

### Time and critical-regularity authority boundaries

R690/R691 prove rational-valued identities for abstract `Time:Set`,
`integrateTo:(Time→ℚ)→Time→ℚ` and supplied integration laws.
They are not *by themselves* real-time Lebesgue/Bochner estimates.
Existing pointwise mass bounds `≤36ED` are quartic positive
mass estimates, not the signed quintic commutator needed by the
compensated global B theorem.

For A the current scalar `H¹` direct Fourier majorant controls
`L²_xi`, but its **critical** `Ḣ^{1/2}` high-frequency envelope has
the unresolved logarithmic tail
`(4π E D/ν²) ∫_{sqrt(D/E)}^∞ dr/r`.
That is a deficiency of the *majorant*, not a counterexample to
any sharper cancellation estimate. No scale-critical A3 control follows.
## Smallest meaningful next cuts

**Cut 1 — B exact compensation owner.** Start at `NSTriadKNR650RateKernelCommutatorEndpointRound685Exact.agda` and `NSTriadKNR650GlobalSignedRateLiftInputLaplacianRound690Exact.agda`. Audit original critical-production source against total forcing, tangent, output-rate and Bony-class correction terms, using the eight-output smooth-shear discriminator. Establish an **actual same-object global identity**, or record a decisive mismatch. Neither file supplies its marked-open spacetime inequality.

**Cut 2 — A actual Fourier owner.** Use `NSTriadKNEuclideanCanonicalProjectedInteractionExact.agda`, `NSWholeSpaceFiniteConvolutionSingleLimitExact.agda` and `NSWholeSpacePhysicalMajorantDominationProducerExact.agda` to transport the classical `L²·L²→L¹` tensor/Fourier identity and quantified strong-H¹ Stokes response continuity into the existing Bishop spatial Fourier source. Avoid another local Leray derivation or arbitrary `Set` record.

**Cut 3 — hard analytic continuation frontier.** For B obtain the missing signed, homogeneous and cutoff-uniform global payment on the *corrected* source, with B1–B3 and B7. For A pay the **signed** A2 centered resolvent and a critical spacetime regularity criterion without assuming a uniform H¹ bound. These are major open Navier–Stokes problems, not bookkeeping tasks with a guaranteed small round count.

## Verification, attribution and scope

- Executed finite checks and standard analytical derivations are not Lean/Agda kernel certificates. New committed source tests and proof declarations still need exact-head validation.
- The earlier R823 real Galerkin counterexample addresses an **auxiliary reserve shortcut**, not positive periodic B.
- Forced C/D official theorem alternatives and their imported Lean axioms are a separate audit.
- No source/author credit is supplied by filename alone. Retain original theorem owners and track mathematical origin when reusing external prior art.
- Never mark A/B globally closed, or change canonical `clayPromotion=false`, without an unrestricted theorem checked against the official quantifiers.
