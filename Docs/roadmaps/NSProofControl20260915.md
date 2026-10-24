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
