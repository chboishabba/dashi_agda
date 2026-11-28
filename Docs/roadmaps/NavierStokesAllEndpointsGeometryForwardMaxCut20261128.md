# Navier–Stokes — original-source all-endpoint geometry-forward max-cut
**28 November 2026 · controlling NS correction and implementation roadmap.**

Branch Agda #1551 (master-based). Companion Lean #123 (main-based).
The original Clay A/B positive options, original unforced A/B breakdown-to-negative
options, and the independently released *forced* C/D routes are not a conjunction.
Do not impose independent alternative routes as serial proof prerequisites.
The objective is a valid theorem against literal Clay quantifiers, not a status
flag, symbolic comparison or a new RNNN name.

## 0. Exact source audit and trust

Inspected actual master:
- Euclidean A objects: NSTriadKNEuclideanPhysicalFourierNSExact,
  NSTriadKNEuclideanCanonicalProjectedInteractionExact,
  NSWholeSpacePhysicalKernelSaturationOriginExact,
  NSClayFacingAPhysicalSameObjectCutExact,
  NSClayFacingATwoPhysicalSeamCompilerExact,
  NSWholeSpacePhysicalMajorantDominationProducerExact,
  NSWholeSpaceFiniteConvolutionSingleLimitExact.
- Periodic B actual: R225/R388/R405/R408, R540–R570,
  NSTriadKNR567CauchyGramFluxNormalFormRound596Exact,
  NSTriadKNFullGramCoherentFoldRound597Exact,
  R598/R600/R601/R602, R645, R648, R652/R653/R654,
  R681–R695 and R722–R727, canonical dyadic critical fold,
  literal R98 boundary flux, low/collar/remote packet and R571/R579
  physical compiler.
- Donor PRs Agda #1543, #1551 and #1291, Lean #123, merged
  Miller provenance Agda #1255/Lean #87.
- Upstream original Levent Alpöge / Tristan Buckmaster unforced project,
  tristanbuckmaster/navier-stokes main, README blob
  1297e1e8515c94a08c4bb4ec56ff609cee98ef51, and the actual
  CellLayerSystem.CellSystemCondition owner in
  lean/Breakdown/CertCell/StatementDefs.lean blob
  3fbf0039a716014d23812f4b8cc71f43c293a818.

No native Agda/Lean/Lake kernel is available in this execution environment;
source-written != independently typechecked. SymPy exact regression does not
prove a PDE existence/continuation theorem. Do not run GitHub CI.
The trust/attribution trail must identify theorem author and model carrier,
not infer novelty/priority from a repository label.

## 1. Correct the fundamental theorem/type claim before building on it

**R596 is a pointwise finite same-output algebraic theorem**:
  4 F_unlifted = fullSquare(gram) + fullSquare(weightedFluxTangent).
**R597 is finite coherent-fold algebra**, not a time derivative.
Do NOT cite R596 alone as a native proof of Q'_C=4F_C-2H_C.
The N2c/N2e physical Cauchy-heat trace and real-time derivative/FTC are
classically derived in Agda #1543/#1551 roadmap text, with corresponding
finite source operators, but native proof still needs the **actual real
Galerkin trajectory**, Cauchy heat kernel, differentiability,
and a genuine real-time FTC and limit transfer. Preserve exact normalizations
and zero mode; a rational Time->Q integration interface is not a physical
real-time FTC by itself.

When these original compatible physical inputs are *actually supplied*,
the endpoint identity is
  4 int_0^T F_unlifted = Q_C(T)-Q_C(0)+2 int_0^T H_C.
Lean #123 now has its explicit conditional weld and R652 coupling in
Synthesis/NavierStokesFractionalR568EndpointWeldExact.lean and
Synthesis/NavierStokesOriginalC1C2R652TraceWeldExact.lean.
No record holding a fake arbitrary scalar function is equivalent to
original heat-kernel proof admission.

## 2. A: whole-space R3 unforced — what exists, what is real missing

A0 ALREADY:
- canonical time/space semantics, the actual continuous xi,eta,zeta=xi-eta
  interaction, Fourier velocity history and Bishop complex 3-vector;
- actual projected raw interaction and Euclidean Leray semantics on the
  punctured physical output; R3 same xi and independent zero-output;
- the near-origin saturation/Gram bound and high-frequency scale-relative
  resolvent curvature (both original owner flags true);
- genuine Bishop positive rational heat floor (not a rational equality
  to arbitrary Bishop ν|xi|²);
- finite translation-reindexed convolution factorization and ONE
  energy-quadrature limit to force the convolution square limit
  (NSWholeSpaceFiniteConvolutionSingleLimitExact).
- NSClayFacingATwoPhysicalSeamCompilerExact already consumes the two
  physical witness records and returns the majorant integrability,
  so do NOT invent additional scalar integration schemas.

A1 UNPAID ORIGINAL SAME-OBJECT KERNEL:
  Construct the actual EuclideanPhysicalResolventKernel from a Fourier
  transform of the original unforced velocity, not arbitrary
  FourierTransformVelocity/Pressure opaque Set inhabitants.
  Weld output xi, projected off-diagonal Gram on TWO original interactions,
  centered residual s>=0, physical heat a=ν|xi|², and equality
    pairResolvent*outputResolvent*centeredResidual
      = s/[a(a+s)].
  Supply PhysicalNearOriginSameObjectData and
  PhysicalHighFrequencyEnvelopeData on those *same* cells.
  Original owner NSClayFacingAPhysicalSameObjectCutExact explicitly marks
  actual kernel instantiation false. Bishop positivity/reciprocal proofs are
  already available; DO NOT rebuild them.

A2 UNPAID ORIGINAL PHYSICAL MAJORANT:
  Identify actual centered signed low/high convolution majorants,
  including near xi=0 with separate zero-mode handling, with source
  physical energy quadratures and constructive R3 integration.
  Strong local physical forcing prior art:
    |F[P div(u⊗u)](xi)|<=min(E|xi|,sqrt(E D)),
    inverse heat L2 envelope squared ≤ (8 pi/nu²) E^(3/2) sqrt(D).
  This does not identify the original centered double-resolvent
  signed pair, and a generic pointwise bound is not an unconditional
  spacetime regularity/finite-horizon producer.
  The A2-midpoint already derives
    r_eta+r_zeta = ν|xi|²/2+2ν|eta-xi/2|²,
  and source-specific incompressibility pays the inner sector
    |eta-xi/2|<=M|xi|^(3/4).
  The signed OUTER sector, measured Fourier/FTC weld and arbitrary-data
  continuation remain. R3 X^4≤K E D yields existence of a good
  time in any *already existing* long smooth interval, NOT survival.

A3 REAL COMPLETION OPTION:
  Supply cutoff/reference- and time-uniform critical continuation in
  an original whole-space function space, preserving pressure and
  smooth compact datum, or an actual independently accepted
  **unforced whole-space breakdown** with no global positive solution.
  No local heat floor/finite convolution alone implies Clay A.

## 3. B: periodic unforced — exact original algebra ALREADY constructed

R225/R388 exact physical double-mixed cell, R596 Gram/forcing finite
normal form and R597 coherent full square, R405/R408 same trajectory,
R652 original same R406 and UNLIFTED forcing:
  4 F = 2 R406 + G_self + H_selfTangent.
R653 exact BIDI C2/R406 sandwich; R645 constructs strict retained
margin and R639/R414 slice from a **supplied** phase-sensitive C2 payment.
R654 already has literal low+collar+remote=0, a proper two-shell
low/remote spectral cross-coercivity and a refuted naive adjacent
spectral gap. What remains is *physical boundary flux* control, not
another R98 spectral datum. R681–R695 rate/live/vector/nested
commutator identities are already source-written; R690 sums before
absolute values and R691 is global mixed-energy balance. Do NOT
duplicate R598/R601/R602: those identify one residual rather than
independent estimates.

The original Agda #1543 N2c classical physical **negative-output-order**
payment for mean-zero real Galerkin:
  Q_-1(T)+2 int H_-1 <= 8 K ||u0||2^4 /ν
is ALREADY derived. N2e has for a in [0,1/4]:
  Q_a(T)+2 int H_a <= (8 K_a/ν)
   [E_a(0)^2+2 int E_a T_a],
  E_a=||Λ^a u||2², T_a=E_a'+2νD_a.
At a=0, unweighted energy transfer zero; at a=1/4 the OUTPUT
weight is one, exactly the original R568 integrand. N2f already
pairs the low-advector transfer and bounds high-high by
C_a||u_{>R}||3 D_a, conditional on genuine cutoff-uniform critical
high-tail smallness. Do NOT declare N2e/N2f algebra or N2c negative
weight as outstanding; the true all-data bound on the SIGNED
  sup_(C,T) int_0^T E_(1/4) T_(1/4)
is absent. A smooth C=1 phase-flip witness disproves pointwise
universal sign, not an integrated compensated bound.

### 3.1 DECISIVE ORIGINAL PHYSICAL R645 C2 COUNTEREXAMPLE (new)

Source:
 scripts/check_ns_r645_c2_original_physical_counterexample_20261128.py
 reuses the original 316-incidence cutoff-one exact source in
 scripts/check_ns_r726_signed_defect_physical_source_exact_20261128.py.
On the original *physical-real*, conjugate-real, divergence-free,
mean-zero initial Fourier velocity B, with cutoff C=1, ν=1:
- ALL 26 nonzero output modes have infinity norm exactly one, hence
  exact Shell.shellIndex(k)=0 and R645/R639/Fold critical w(k)=1.
- The original Leray-projected unforced quadratic forcing is
  N_k=-i P_k sum_(p+q=k)(u_p·q)u_q.
- The *literal* nonlinear critical energy production is P'_C(0)=0
  (classical conservation, also EXACTLY recalculated by SymPy).
- Literal weighted viscous dissipation at the same initial time is
  D'_C(0)=108.
- Literal source R406_C(0), with all ordered pair rates ν(|p|²+|q|²),
  zero-input incidences retained, is EXACTLY
    R_B = -1216/9 -317 sqrt3/9 -77 sqrt6/4 +815 sqrt2/12
        < -69/2 <0.
Under scaling the SAME divergence-free velocity by A=2:
  P'_C=0, D'_C=432, R406_C=32R_B<-1104,
so for EVERY δ>=0
  P'_C -[(2ν-δ)D'_C+R406_C] >240>0.
R645 demands the opposite inequality for some positive δ. On the
actual finite-dimensional Galerkin ODE its source functions are
continuous, so this strict gap persists on a sufficiently small
positive real interval; integration contradicts the UNRESTRICTED
R645 strict-margin condition. This is a mathematical physical-real
finite-model refutation of a would-be ALL-SMOOTH-DATA ESTIMATE, NOT
a counterexample to 3D NS regularity and NOT an Agda rational-kernel
false inhabitant. Native Agda rational helical scalars still need an
ordered real algebraic/Bishop value extension to internalise sqrt2,
sqrt3 and zero modes.

New Lean #123 original exact radical sign arithmetic in
Synthesis/NavierStokesR726PhysicalRadicalSignCertificatesExact.lean:
  witnessB_R406_strict_negative,
  original_R645_scaled_witness_strict_failure,
  original_R645_every_positive_margin_fails,
  original_R645_scaling_identity.
The Lean source is PENDING_KERNEL; SymPy actual physical Fourier
source checker PASSED locally (two original real states, amplified
B and symbolic rate identities).

**Status change:** R645/R653/R727 conditional compiler theorems remain
valid *if somebody supplies their original C2 hypotheses*. But an
unrestricted proof route demanding this precise R645/C2 receipt on
EVERY original datum is now physically untenable. Do NOT label the
unrestricted R645 strict margin open-and-expected; mark it
REFUTED_AS_UNIVERSAL_PHYSICAL_REAL. Do NOT conclude B itself false.

### 3.2 R726 physical no-go and its corrected compensation

R722/R723 integrated combined self/external=12 R691 commutator;
R726 historical condition R406_integral <= combined_integral
is refuted as a universal source sign in the same exact 316-incidence
physical-real model (both signs and viscosity reversal on fixed u).
New original typed Agda R726 theorem
  actualSignedDefectNumeratorIdentity:
  2*(R406_int - Combined_int)
   = 4*F_unlifted_int - G_self_int
     - H_selfTangent_int - 2*Combined_int.
New R726 signedDefectCeiling and R727 CompensatedC1C2Inputs
compile physical conditional hypotheses into the original R410/R414
critical consumer.

**Another essential redundancy correction:** The separate estimates
  Combined <= B1, Defect <= B2
imply R406 <= B1+B2, but the *SAME signed source* obeys the identity
  Combined+Defect=R406.
A JOINT cutoff-uniform bound on the actual combined + defect is
therefore exactly an R406 upper; it is NOT a distinct new PDE payment.
Separate absolute B1/B2 bounds may be strictly harder and may destroy
cancellation. Lean #123
Synthesis/NavierStokesOriginalC1C2R652TraceWeldExact.lean proves this
bidirectional reduction alongside the R652-to-positive-trace identity
(with the real-time heat trace explicitly assumed). **Do not count
R723 + compensated R726 as two mandatory independent analytic
leaves** and do not sell a tautological joint signed bound as
regularity progress.

### 3.3 What can still prove the literal original B endpoint?

B-POS1: An actually valid cutoff-uniform scale-critical regularity
criterion, for example a genuinely independently proved uniform
critical L3/critical Sobolev bound or Serrin/BKM continuation,
with ALL original data, common lifespan and correct viscosity,
coupled to 3D PDE compactness. Existing N2f gives a conditional
high-L3-tail entry, not all-data production. A signed R568 C1 upper
alone cannot recover the false unrestricted R645 C2.
B-POS2: A DIFFERENT compensating signed nonlinear inequality with
a real physical remainder whose uniform integral is independently
paid and which actually establishes a positive continuation margin.
Such a theorem must survive the C=1 amplitude and phase controls,
and cannot simply re-use the false R645 right-hand side. Weld into
existing R414/R639 only after validating the real physical condition.
B-NEG: A complete *unforced* periodic NS finite-time breakdown
certificate on the original equations and original pressure/period
semantics; this refutes the positive periodic-B alternative and can
produce the corresponding Clay D terminal with zero force once
the actual statement transport is proved. This is logically
distinct from universal positive B regularity.

## 4. Independent original unforced profile/certificate lane

The newest inspected upstream tristanbuckmaster/navier-stokes main
README (blob 1297e1e8515c94a08c4bb4ec56ff609cee98ef51) says the
Alpöge–Buckmaster November 20, 2026 numerical interval certificate
and 128-bit Arb/FLINT checker are NOT provided, and the patched
Lean package was NOT rebuilt. Existing Lean #123
proofs/alpoge-ns-lean433/UnforcedAdmission.lean and
ClayUnforcedTransport.lean already contain conditional original
from_profile, from_original_cell_condition and literal Clay transport.
They are NOT an inhabited proof of the original fifteen top-level
CellSystemCondition obligations.

Actual original 15 top-level fields (from
Breakdown/CertCell/StatementDefs.lean) are:
 cell; shape_valueSets; entry_conditions; enclosure_numbers;
 coerciveL2_ge; coercivePin_ge; certificate; instantiation;
 offset_expansion; shift_numbers; frozen_form; adjoint_quadratic;
 adjoint_links; potential_entries; adjoint_defect.

The original CertificateClauses **inside** that record also require
physical bounds, small_first/second/third, nontriviality, pressure
gauge, adjoint and stiffness fields. In particular a valid
CellSystemCondition needs the exact seven source data objects
D,X,R,T,Y,N,B and their original native type relationships, NOT
just a field count or generic positive real matrix.

Already implemented in our branches: H19 signed harmonic lattice and
reflection/zero grades, source-shaped Fourier profile exploration,
finite exact rational cell-node/Schur witness builder, exact
smallness-cap reverse solve, 3D weighted Hilbert inverse/adjoint and
rank-one bordered actuator *conditional* constructs, local candidate
physical residual and a selected simple-profile no-go. No original
nonzero continuum profile, proven global inverse/form bound,
real pressure/adjoint/actuator cancellation, complete original
unbounded tail enclosure or actual fifteen-field witness exists.
The original source has unknown certificate bytes and a patched
unrebuilt toolchain. This is genuine *proof discovery and source
verification*, not merely a missing GitHub CI receipt.

Next concrete native proof targets, in one lane:
1. original nonzero periodic-in-similarity profile/pressure with H19
   reflection and signed modes; prove the actual PDE curl residual,
   source pressure Poisson, correct exterior r^-1 tail and smooth origin.
2. original source weighted continuous form and full derivative/pressure
   Hilbert space, original coercive gap including singular axis/outer
   tail and model-form perturbation, not an arbitrary assumed B.
3. global source-shape adjoint, pin normalization and nonzero actuator
   pairing with exact signed cancellation, preserving gauge/period.
4. instantiate all fifteen original fields and CertificateClauses
   with actual interval enclosures and verify the pinned native build;
   independent mathematical fidelity review to paper and original
   physical PDE.
Do NOT substitute synthetic certificate data for the original source.

## 5. Independent forced C/D routes (NOT gated on A/B estimates)

Agda main and Lean main already have pinned original OpenAI forced
C/D transports, theorem statement adapters and literal Clay terminal
consumers. The new original unforced source would yield additional
zero-force C/D options **if actually certified**, but is not needed
to audit the separate forced route. Remaining for credible local
accepted source: exact pinned full dependency/source theorem,
compatible Lean 4.34.0-rc2 build, independent transitive axiom/
sorry audit, exact Fefferman solution/force/pressure/energy/period
semantics and independent mathematical source-paper fidelity scrutiny.
The OpenAI proof's formal/paper correspondence has been publicly
contested; do not equate source presence with settled independent
acceptance, or assume the published result is a Clay award.
One proven valid official A, B, C OR D alternative suffices; not all.

## 6. Concrete verification/implementation queue (big-bite order)

Priority P0 / Mathematical validity (before incremental theorem flags):
  (1) Exact physical R645 no-go regression on original R225/R388
      source and finite B Galerkin ODE; carry source into its own
      value-compatible native real/ordered-algebraic owner.
  (2) Replace unqualified periodic-B C2 proof search with a VALID
      physical continuation criterion; honor amplitude-2, ±phase,
      viscosity-reversal, cutoff/zero-input and high-shell tests.
  (3) Reuse A existing physical kernel/measure and quadrature, implement
      actual Fourier same-object identification and signed exterior.
  (4) Recover or independently certify original nonzero unforced
      profile/certificate (15 fields); reuse already coded generic
      inverse/adjoint/Schur machinery only with original bounds.
  (5) Complete pinned original forced C/D build/statement/fidelity
      acceptance locally; preserve authorship, no new false terminal.

Priority P1 / native weld and source completeness:
  - Make original N2e real-time heat trace from finite R596/R597
    mathematical source actually inhabited at original real time,
    no arbitrary Time->Q shortcut.
  - Exact projected Fourier source-to-R406/R653 comparison at
    real algebraic helical norms; construct a genuine original
    real coefficient carrier if desired, not fictitious rational sqrt2.
  - Attach corrected C2 or alternative conditional regularity proof
    to R414/R639 and full 3D limit with original physical time.
  - Preserve all original source indices, signed phases, zero modes,
    rate denominators, output membership and positive viscosity.

Local exact acceptance:
  python scripts/check_ns_r726_signed_defect_physical_source_exact_20261128.py
  python scripts/check_ns_r645_c2_original_physical_counterexample_20261128.py
Use 90s shell timeout per bounded invocation; if needed checkpoint
independent cases. Exact SymPy is a stand-in for *testing algebra*;
it does not replace Agda/Lean kernel typechecking.
No GitHub CI. New source bodies PENDING_KERNEL.

## 7. Files actually written on the current branches

Agda #1551:
- NSTriadKNR650CombinedToLiteralR406Round726Exact.agda:
  exact original physical signed defect numerator and compensated
  R406->R410 source compiler.
- NSTriadKNR650CombinedC1C2CriticalBarrierRound727Exact.agda:
  compensated conditional family/barrier, explicitly scoped.
- NSTriadKNStrictMarginProductionToPhysicalCriticalGapRound645Exact.agda
  and R653: document/refuse unrestricted physical real C2 shortcut.
- scripts/check_ns_r726_signed_defect_physical_source_exact_20261128.py
  exact original finite C=1 physical no-go; and
  scripts/check_ns_r645_c2_original_physical_counterexample_20261128.py
  exact *amplified same-source* stronger strict-margin no-go.
- this consolidated roadmap, NSProofControl20260915.md and
  Clay369PhaseCompleteEndpointMaxCut20261128.md status reconciliation.

Lean #123:
- Synthesis/NavierStokesFractionalR568EndpointWeldExact.lean
  original R596/N2e endpoint C1 and separate R653 conditional BIDI.
- Synthesis/NavierStokesR726SignedDefectViscosityNoGoExact.lean
  real viscosity threshold proof and source scaling.
- Synthesis/NavierStokesR726PhysicalRadicalSignCertificatesExact.lean
  exact sqrt2/sqrt3/sqrt6 signs, original witness B physical R406
  and scaled unrestricted R645 strict-margin no-go.
- Synthesis/NavierStokesOriginalC1C2R652TraceWeldExact.lean
  R652 same coherent trace and R723/R726 no-double-budget BIDI.
- Synthesis/NavierStokesABFiniteHorizonExact.lean import-weld.
All new native bodies are source-written and unchecked by compiler
in this environment. Any future native errors must be fixed
against the exact checked-in source rather than substituting a
truthy status Bool, postulate, sorry or ad hoc source-shaped axiom.

## 8. Theorem/proof/status firewall

TRUE mathematics already on source: finite Gram/shell/rate identities,
literal nonlinear ODE polynomial formula, N2c/N2e classical
fractional *conditional* derivations, finite 3D rational/radical
countercontrols and classical short-time ODE continuity.

FALSE proposed universal shortcut in physical-real original model:
uncompensated R726 signed order, and R645 strictly positive C2
payment for all smooth periodic unforced data (new C=1 amplitude
counterexample). The R723 plus compensated defect split is
an exact identity, not by itself two new mathematical payments.

OPEN: both original positive A/B global regularity and original
unforced breakdown certificate; independent forced C/D acceptance
audit; original A physical Euclidean/measure and global horizon;
valid unrestricted B critical continuation or another faithful
C/D physical endpoint. NO source-WRITTEN bool or finite checker
promotes one of these endpoints. Work forward in large blocks,
not serial recomputation of already-owned geometry.


## 9. Completed execution pass, byte-identical acceptance and original A geometry

On 28 November the original source no-go was executed **against exact Git blobs**;
later script changes added fail-closed Python -O guards and the same final source
was rerun. The separate stages are:
- R726 physical signed defect source: blob
  `682ad3452a90322111bb8179bbbc68c7a4966aa4`,
  PASS exact SymPy in under the 90s per-stage limit.
- R645 stronger physical strict-margin source: blob
  `4a35e38940c756adf5e0b36212605bdc97db694b`,
  PASS exact SymPy under separate 90s limit. Original initial
  critical production P=0, D=108; amplified P=0,D=432,
  R406 amplified<-1104, margin-zero violation >240. Independent
  inverted velocity has same energy/D and reversed R406 sign.
- Both script hashes match source bytes read from GitHub connector;
  Python -O is deliberately REFUSED because it drops assert-gates.
  These PASS receipts are not kernel acceptance.

Pinned, fail-closed, stage-checkpointed local runner committed:
`scripts/check_ns_original_physical_maxcut_local_20261128.sh`.
It checks each current Git SHA and runs each physical source at a hard
90-second shell limit. Use `r726` and `r645` independently as checkpoints;
`all` runs them in order and does not claim a native Agda/Lean pass.
When source scripts evolve, update the SHA manifest after inspecting the
exact difference, not by deleting the hash verification.

**Actual Euclidean A geometry now source-written in native Lean #123:**
`Synthesis/NavierStokesEuclideanOriginalMidpointLerayWeldExact.lean`.
Rather than a new scalar record, it uses the SAME three Cartesian
physical coordinates and complex divergence-free Fourier velocity.
It proves both the exact physical midpoint identity
  |eta|²+|xi-eta|² = |xi|²/2 +2|eta-xi/2|²
and, from original eta·u_eta=0, the phase-preserving complex identity
  xi·u_eta = -2(eta-xi/2)·u_eta.
It also proves nonnegativity of the centered input rate at ν≥0 and
zero divergence-form interaction at the exact midpoint. This is
a **second-language proof representation of existing original R290/R541
geometry**, not a new PDE/continuum existence result. The original
Bishop Fourier/measure and signed exterior remain unpaid. A local
independent SymPy exact test of these 3-vector equations passed
512/512 input/output/compex-phase fixtures. Lean source PENDING_KERNEL.

**Native R596 attribution repair:** Lean #123
`Synthesis/NavierStokesFractionalR568EndpointWeldExact.lean`
renames the supplied physical trace hypothesis to
`hRealTimeTrace` throughout; R596/R597 only provide source finite
Gram/forcing algebra, so an actual Q'(t), real time heat and FTC
remain proof-bearing and cannot be claimed just from the filename.

### Active branch receipts and next max-cut order

1. **Mathematical validity first:** keep the two failed universal
   R645/R726 physics shortcuts excluded in all future budgets; do not
   construct arbitrary-time positive strict-margin certificates over
   the full C=1 physical source, since explicit counterstates exist.
2. **Positive A and B:** implement actual SAME Euclidean/periodic
   PDE and continuation analytic inequalities on their original
   physical spaces (or a completely different valid conditional
   criterion with an independently proved ALL-data hypothesis).
3. **Unforced negative A/B:** original Alpöge–Buckmaster seven data
   objects/fifteen conditions require a real nonzero source profile
   and the missing interval certificate; no available public bytes
   currently satisfy them. The rigorous checker also remains absent
   upstream in the inspected revision.
4. **Forced C/D:** compatible nested source build, true statement/
   pressure/force/solution comparison and independent scientific
   review. Treat valid acceptance of ONE Clay option as terminal,
   never a conjunction of all four.
5. Run exact-head Agda/Lean kernel checks locally when toolchains
   exist; repair actual compile errors without `sorry`,
   `postulate`, opaque synthetic physical inputs or status Boolean
   promotions. Keep all changes on the corresponding active PR
   branches with attribution and native tests together.
