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
