# Three-paper formal integration: Pareto / snowball / Ibrahim max-cut
Date: 2026-10-25 (Australia/Brisbane). Status: implementation/source audit; no new Clay or phenomenology promotion.

## Original source objects (not interchangeable)

| Root | Publication/locator | Original claim | Our reconstruction |
|---|---|---|---|
| Evan Miller | *A Locally Anisotropic Regularity Criterion for the Navier–Stokes Equation in Terms of Vorticity*, Proc. AMS Series B **8** (2021), pp. 60–74, DOI: [10.1090/bproc/74](https://doi.org/10.1090/bproc/74), Theorem 1.6, Section 2 | Conditional **unforced**, whole-space, 3D mild-solution continuation with bounded direction gradient and finite scale-critical projected-vorticity norm | Lean algebraic 3-component identity and critical exponent arithmetic; Agda same-source A3 contract. The source theorem is **not** re-proved in Lean, and its hypotheses are not established by generic energy. |
| Weiping Yan and Vicenţiu D. Rădulescu | *Sobolev regular solutions for the incompressible Navier–Stokes equations in higher dimensions: asymptotics and representation formulae*, Rend. Circ. Mat. Palermo II. Ser. **70** (2021), pp. 995–1021, online 2020-07-25, DOI: [10.1007/s12215-020-00540-3](https://doi.org/10.1007/s12215-020-00540-3), Eqs. (1.1)/(1.3), Theorem 1.1, Cor. 1.1 | **Steady forced**, bounded-domain solutions under small forcing and additional hypotheses; Nash–Moser scheme and explicit cube family | Lean exact scalar divergence-balance and cyclic-derivative cancellation; Agda forcing-divergence preservation with explicit source attachment. The full Nash–Moser/elliptic/PDE proof is **not** formalised. |
| Jeremy Rodgers | *Experienced Temporal Passage: Enacted Scaffolding and the Organization of Succession*, independent research manuscript **2026-10-23**, DOI **as printed on uploaded PDF**: [10.5281/zenodo.23591626](https://doi.org/10.5281/zenodo.23591626), Proposition 1, Proposition 5, Appendix C | Given constitutive premises, a qualifying enacted temporal structure has experienced succession without an additional constitutive advancing-present variable; finite order and prefix invariants | Reuses original DASHI nonfactorability machinery for a finite CE/EC counterexample and 0/50ms source versus 80/60ms reversed arrivals; proves local-prefix fold law and retrieval-independent *stipulated* admission. NOT a proof that the constitutive premises are empirically true or a consciousness detector. |

The two Navier–Stokes sources are **not** independent confirmations of the same regularity statement. The third paper's finite propositions do **not** empirically certify experienced character.

## Existing authoritative owners and what was reused

- [NS canonical residual scheduler](../DASHI/Physics/Closure/NSCanonicalClayResidualExact.agda): A1/A2/A3, periodic B, C/D, all with nonpromotion gates. A3 is the only consumer of the new Miller adapter; do not create a replacement Clay theorem owner.
- [NS canonical A3](../DASHI/Physics/Closure/NSCanonicalA3ContinuationResidualExact.agda): requires a literal continuation predicate on the original selected physical source.
- [NS exact strain eigenbundle](../DASHI/Physics/Closure/NSExactStrainEigenbundleHarnessBoundary.agda): Biot–Savart / Leray / finite-symbol harness; this is not a proof of a cutoff-uniform physical direction field.
- [NS banded vorticity](../DASHI/Physics/Fluid/BandedVorticityCrossPollination.agda): signed finite atoms, not continuum vorticity.
- [History-conditioned choice](../DASHI/Core/HistoryConditionedChoiceExact.agda) and [intersectional nonfactorability](../DASHI/Core/IntersectionalNonFactorability.agda): the latter is the actual proof dependency for Rodgers's order-erasure witness.
- [Temporal restriction before quotient](../DASHI/Cognition/PNF/DemandLocalWildcardTemporalOrderExact.agda): the source-order / arrival-order distinction must not be erased by a coarse history quotient.
- [Consciousness instantiation boundary](../DASHI/Governance/ConsciousnessAbstractionInstantiationBoundaryExact.agda): code equivalence, physical implementation, actual uptake and phenomenology are different claims.
- Lean's existing `NSAWholeSpace`, `NSCanonicalLeaves`, `NSBQuantitative` and `NSCutset` libraries remain the quantitative PDE owners. This tranche introduces `NSPaperBridges` as an **opt-in leaf**, not a parallel physical-analysis spine.

## Pareto, ranked by missing bridge / expected downstream use

1. **Miller exact 3D strain/mixed-norm operator** — finite algebra is now a candidate leaf; next research payment is the *same-solution, cutoff-uniform* L⁴_t L²_x vorticity projection and spatially Lipschitz unit direction, followed by the actual whole-space A3 continuation semantics. Neither follows from finite support trits or total kinetic energy.
2. **Rodgers order information** — finite deterministic nonfactorability and retrieval-independent stipulated admission are constructed; stochastic decoder information inequalities, realised interpretation in a person, calibrated signal delays, and experiment intervention remain unproved / empirical. The order-information core can be used independently of the constitutive theory.
3. **Yan–Rădulescu stationary witness** — next check the explicit Corollary 1.1 product family in an actual differential algebra, then boundary vanishing and Sobolev smallness, then smoothing operators/linearized invertibility/Nash–Moser with all constants. Its stationary small-forcing scope does not supply global 3D unforced smoothness.
4. **External whole-space/periodic C/D comparison** — OpenAI's [2026-09-08 release](https://openai.com/index/navier-stokes-solution/) and [source formalisation](https://github.com/openai/NavierStokesAndEuler) concern **smooth forcing** in Clay alternatives C/D. The upstream self-reported Lean proof is a separate object from DASHI's canonical A/B programme. No claim of unforced blowup, automatic proof adoption, or ownership transfer.
5. **Proof-engine infrastructure** — [Weinan Wang, *Formalization of the Galerkin Construction for the Two-Dimensional Navier–Stokes Equations in Lean*, arXiv:2609.33033 (2026-09-27)](https://arxiv.org/abs/2609.33033) is a potential reference for generic weak Galerkin machinery, but a 2D unforced result cannot discharge 3D continuation, and its source must not be silently vendored.

## Snowball genealogy / original roots (acquisition edges, not proof)

- Miller's own cited predecessors: [Dongho Chae and Hi-Jun Choe, *Regularity of solutions to the Navier–Stokes equation*, EJDE 1999 No. 05](https://ejde.math.txstate.edu/Volumes/1999/05/abstr.html) for two-component vorticity; [Peter Constantin and Charles Fefferman, *Direction of Vorticity and the Problem of Global Regularity for the Navier–Stokes Equations*, Indiana U. Math. J. 42 (1993), 775–789](https://iumj.org/article/3627/) for geometric depletion; Hugo Beirão da Veiga and Luigi C. Berselli, *On the regularizing effect of the vorticity direction in incompressible viscous flows*, Differential and Integral Equations 15(3) (2002), 345–356, DOI [10.57262/die/1356060864](https://doi.org/10.57262/die/1356060864). They are different source theorems, not duplicates of Miller.
- Yan–Rădulescu cite Nash, Moser, Hörmander and the Calderón–Zygmund framework. Reuse these only for their specific estimates after checking parameter ranges, smooth versus polyhedral domains, force divergence and boundaries. A paper's references are not an instantiated theorem.
- Rodgers cites differentiated temporal-order and perceptual studies (e.g. Saija et al. 2014, Stetson et al. 2006, Wacongne et al. 2011, Zuo et al. 2020) and a finite circuit primitive. The studies have different populations, stimuli and outcome measures. They do not independently validate constitutive identity or fundamental temporal ontology.
- One uploaded PDF, a publisher version, a preprint and an author mirror of the **same work** form one source lineage, not four independently corroborating results.

## Ibrahim / attribution integrity and stop rules

Use existing `DASHI.Core.AttributedSourceCore`, `SnowballAttributionProvenanceInvariantExact` and `DASHI.Wikimedia.IbrahimSnowballParetoFrontierExact`, not a new provenance ontology. Stable DOI/URL/author/theorem locators must accompany claims; unknown QID or Dewey values remain unknown and should not be nearest-label guessed. Source mentions and adjacency route inspection only: no proof, authority, influence, independent corroboration, or causal transmission is inferred. Source authors own published results; DASHI owns the newly constructed finite witnesses and adapters; Lean kernel status is separate from Python arithmetic checks.

Stop a snowball branch when another reprint or derivative adds no new primary theorem, measurement, physical object, or discriminator. Reopen it only for a specific missing dependency (e.g. an actual directional gradient estimate, a source-correct pressure equation, or an experimentally calibrated uptake intervention).

## Verification and acceptance

- Agda module surfaces: `DASHI/Cognition/PNF/EnactedTemporalOrderExact.agda`, `DASHI/Physics/Closure/NSMillerAnisotropicA3BridgeExact.agda`, `DASHI/Physics/Closure/NSYanRadulescuStationaryPressureExact.agda`, and typed `DASHI/Papers/ThreePaperSourceAtlas20261025Exact.agda`.
- Lean opt-in leaves: `RequestProject/NavierStokes/MillerAnisotropicAlgebra.lean` and `RequestProject/NavierStokes/YanRadulescuPressure.lean`.
- Static/numerical regression: `pytest -q tests/test_three_paper_bridge_contracts.py` in Agda and `pytest -q tests/test_ns_paper_bridges_contract.py` in Lean.
- Intended kernel checks (not claimed executed without a compiler): `agda -i . -l standard-library DASHI/Cognition/PNF/EnactedTemporalOrderExact.agda`, analogous checks for the other three Agda files, and `lake build NSPaperBridges` in the Lean repo.
- **Safe-mode compatibility**: the two Agda modules that reuse legacy `IntersectionalNonFactorability` and `AttributedSourceCore` omit the `--safe` pragma because those imported owners do not declare themselves safe. This avoids falsely claiming transitive Safe Agda certification. They introduce no postulates, holes, or unsafe options. The Miller A3 and Yan pressure modules retain `--safe` where their dependencies permit it.
- **Fail closed**: Agda typechecks and Lean kernel checks have not been observed in the GitHub connector; the static tests are not substitutes. Neither paper supplies an unconditional global-unforced 3D regularity result or an empirical consciousness proof.


## 25 October follow-on: exact cube seed, shared-prefix masking and fresh PR inspiration

### Yan/Rădulescu primary-source correction and stronger structural reuse

Reinspection of the *original printed page 998*, not a paraphrase, shows:
- Let `a(y)=y(y-T)`, `h(y)=a(y)^q`, and `rho(y)=a(y)^(2(p+1))`.
- Source `g(y)=a(y)^(q-1)(2y-T)[q - 2(p+1) a(y)^(2(p+1))]`.
- By formal product and chain rules, `g=h'-h rho'`. Consequently `F=h exp(-rho)` has derivative `D=g exp(-rho)`.
- The three nonzero coordinates of the paper's `U^(0)` are `eps*(F1 D2 D3, D1 F2 D3, -2 D1 D2 F3)`, where the notation `F1=F(x1)` etc. The common exponential has not been omitted or counted twice.
- For `p>1, q>2`, both `F` and `D` vanish at `0,T`, so each coordinate vanishes on all six cube faces. The three coordinate partial derivatives have coefficients `1+1-2`, cancelling divergence.

The new **Lean source-written** `RequestProject/NavierStokes/YanRadulescuCubeSeed.lean` implements the separable model with three `HasDerivAt` hypotheses, zero-divergence and six-face boundary lemmas, plus a universal derivative-factor algebra lemma. It **does not yet** instantiate `F,D` with the exact exponential-polynomial expressions in the Lean kernel; that is the next concrete analytic bridge, followed by norms and the actual small-force steady PDE.

A source-replay `scripts/check_yan_radulescu_polynomial_seed.py` uses only integer polynomial arithmetic, not floats or OCR. A local execution of equivalent code checked `p=2..6`, `q=3..9`, `T in {1,2,3}`: **105/105 parameter triples passed** for exact `g=h'-h rho'` and endpoint zeros. This is finite reproducibility, **not a universal proof, and not a run of a GitHub Actions workflow**.

The source's equation (1.3) still omits `div(f)` although source equation (1.1) allows general `f`; the new canonical pressure owners retain `div(f)` until explicitly discharged. Neither the successful cube-seed calculation nor stationary existence establishes 3D unforced global regularity.

### Rodgers prefix noninterference / other current PR donors

- Already-existing **master** owner `DASHI.Core.IntersectionalNonFactorability` still proves the order-erasure obstruction. The appended `sameKernelResponseUnderOrderErasure` proves that **any** fixed map from the unordered observation to response-law codes gives equal codes for CE and EC; it does not prove equality of independently sampled random results.
- A genuinely new finite theorem states that truncation to the length of a received prefix commutes with appending **any** future suffix, and hence current deterministic state and readout are unchanged if the unseen future is changed. `EnactedTemporalOrderRegression` provides a source-written model with future sequences `[42]` versus `[99]`. It is not a biological prediction or future-data decoder.
- **Lean PR #83**, TimesFM-3 masked-future/noninterference, is a conceptual donor, **not an imported source theorem**. No unmerged Lean change was copied into Agda or treated as kernel-verified.
- **Agda PR #1243** source-world empirical nonidentifiability and separate real-world access constraints are a governance pattern, not an assertion that Rodgers's constitutive theory is true. **Agda PR #1259** sperm-whale phonology shows a relevant original-authorship, semantic-conflation and candidate-observation gate pattern. Neither unmerged branch was made a dependency of this PR.
- **Lean PR #78** OpenAI math corpus provenance separates manuscript claims, source declarations and kernel/cross-prover authority. It is a research genealogy donor only. The 2026 Weinan Wang arXiv:2609.33033 source concerns 2D Galerkin/Leray–Hopf solutions; it cannot inhabit a 3D scale-critical Miller hypothesis.

### Updated Pareto and current live max-cut

1. **P0 source/kernel validation**: `lake build NSPaperBridges` and Agda focused module/rollup typechecks. No package was falsely labelled kernel-green in the connector.
2. **P1 exact Yan seed expression**: Lean proof `HasDerivAt F (g exp(-rho))` using the exact source polynomials, `p>1,q>2,T>0`; combine with already-source-written six-face and divergence lemmas. Reject if source derivative factor fails.
3. **P1 Miller physical producer**: actual same-solution `v`, unit-length proof, spatial gradient bound through the same time interval, and `L^4_tL^2_x` projected-vorticity bound for the *same* unforced R³ solution. The new Agda gradient predicate now explicitly depends on both source and direction. Transfer to canonical A3 is **still conditional**.
4. **P2 Rodgers testable intervention**: specify source/arrival delay calibration, retained trace, fusion/uncertainty, current uptake and matched differential readouts. Compare competing predictions on held-out observations; do not promote a finite code or subjective report to universal phenomenal ontology.
5. **P3 Yan full steady existence**: smoothing operators, uniform inverse estimates, Nash–Moser derivative losses, convergence, source pressure consistency, boundary problem, and fixed `n>=3` assumptions. Formalising the cube seed does not bypass these.
6. **P4 publishable cross-domain synthesis**: source-by-source theorem/import manifest, first Git commit versus kernel-success provenance, and a claim lattice that keeps original credit even after Lean-to-Agda porting.

Remaining claims stay gated. A new citation, preprint version, code commit, nonindependent descendant source, PR discussion, or static passing test is not proof or new experimental replication. Consumer-triggered source snowball stops at independent original roots and verified new physical/mathematical objects.


## First source-implementation receipts (not validation dates)

The following **GitHub commit object timestamps** establish the first observed
source-written implementation in these two branches. They do not establish
first successful typecheck, exact-head kernel check, independent mathematical
priority, or final publication. Brisbane = Australia/Brisbane (UTC+10).

| Source-written object | First Git commit | Git timestamp UTC | Brisbane date/time | Evidence grade |
|---|---|---|---|---|
| Rodgers finite Agda owner | `85a4e6121914396e9d106b0d3c0535892f1034ae` | 2026-10-24 18:00:21Z | 2026-10-25 04:00:21 | source file first committed; kernel unverified |
| Miller Agda canonical A3 adapter | `c77c27569603a8ca35eb76e8b61c79575221d2f2` | 2026-10-24 18:01:18Z | 2026-10-25 04:01:18 | same-source contract first committed; kernel unverified |
| Yan Agda pressure audit | `32c74ca3df59bdacc9909a4555d6033ea5b622e5` | 2026-10-24 18:01:38Z | 2026-10-25 04:01:38 | source-consistency contract first committed; kernel unverified |
| Miller Lean algebra | `4245a2e0d96a1095391f3d886062074083de2fce` | 2026-10-24 18:02:12Z | 2026-10-25 04:02:12 | elementary algebra first committed; kernel unverified |
| Yan Lean separable cube seed | `176679d666f8c8c2c20ad82c4c91d9fc9e5f4f02` | 2026-10-25 08:16:07Z | 2026-10-25 18:16:07 | divergence/boundary source code first committed; kernel unverified |
| Temporal mask Agda regression | `d5194d76b9493832913a4de3bd7800517d0f6c77` | 2026-10-25 08:20:42Z | 2026-10-25 18:20:42 | regression first committed; kernel unverified |

Original paper precedence is older and separately attributed (Miller 2021;
Yan–Rădulescu 2021 / online 2020; Rodgers 2026-10-23).
Existing generic DASHI proof owners have their own earlier source history;
these new commit receipts do not overwrite their priority.

### Executed *outside* GitHub source proof-checking environment

- Local standard-library integer-polynomial replay:
  `python /mnt/data/yan_polynomial_audit.py` -> **PASS 105/105**.
- Three selected SymPy checks `(p,q,T)=(2,3,1),(3,4,2),(4,5,3)`:
  `simplify(diff(F,y)-g*exp(-rho))==0` for each -> **PASS**.
- No `lake build`, Agda typecheck, pytest on a branch checkout, external
  empirical experiment, or deployed model run executed in this turn.


### Late repo-audit: Miller versus existing vorticity-control consumers

The actual master-branch sources `DASHI.Physics.Closure.NSCompactGammaBKMTimeIntegrability`,
`NSVorticityAlignmentObstructionReceipt`, `NSVorticityNoMechanismReceipt`,
and `NSStrainBMOBoundReceipt` were read. They expose an important
**non-circularity test**, not an already-paid Miller theorem:

- Compact-Gamma-to-BKM requires energy/dissipation, Bernstein weights,
  weighted shell summation and a `NoBKMSobolevBootstrap` witness **before**
  applying the established BKM continuation theorem.
- The vorticity-alignment module records a *misaligned compressive-zone*
  obstruction as still open. Its qualitative recorded sign is not a full
  Lipschitz unit-field estimate in Miller's actual R³ theorem.
- A periodic T³ strain BMO placeholder is not identical to the R³
  locally anisotropic (L^4_tL^2_x) projection bound; domain, norm,
  constants and source trajectories differ.
- Do **not** derive Miller's projected-vorticity bound from a full
  `L¹_t L∞_x` vorticity/BKM bound and then claim the result independently
  establishes that BKM condition. The physical evidence chain must be
  acyclic, source-matched and cutoff-uniform.

The correct new physical leaf remains a same-unforced-solution,
same-time-horizon direction field with uniform spatial derivative control
and finite projected critical expenditure, with a separate PDE theorem
identifying the limit/continuation. Earlier finite vortex trits and BMO
receipts are useful falsification and geometry candidates only.


## 26 October 2026: source-exact producer, adverse pressure case and observability cut

**Cross-PR source scan (newest):** #1266 already owns the generic revisable
consumer-collision/no-factorisation apparatus; #1268 owns its scoped
Follow-Through original-source-world/Pareto experiment; #1267 is a
source-first severe-inquiry *roadmap*, not experimental authority; #1265
explores finite Dust/LILA learner operators under source-written and empirical
limits. These PRs are **independent/unmerged** donor designs. This work
continues to import the master generic
`DASHI.Core.IntersectionalNonFactorability` and
`DASHI.Core.FirstImplementationTimestampExact`; no duplicate universal
framework was created and no collaborative Alice Brown/LOOM/ESD work was
changed or presumed authorized.

### Yan–Rădulescu: fully source-specific algebra and an adversarial equation

The primary published PDF (2021, printed pp. 996–998) specifies
`p>1, q>2, T>0` and
`g=a^(q-1)(2y-T)(q-2(p+1)a^(2(p+1)))`, with
`a=y(y-T)`, `h=a^q`, `rho=a^(2(p+1))`,
`F=h*exp(-rho)`, `D=g*exp(-rho)`.

The **new** `RequestProject/NavierStokes/YanRadulescuExactSeed.lean`
now defines these exact source expressions, encoding `p=pExtra+2`,
`q=qExtra+3`, so all required integer inequalities hold by type. It adds
the ordinary real polynomial and exponential `HasDerivAt` chain, an
identification `F'=D`, source-specific divergence cancellation and all
six Dirichlet cube-face equalities. This is real theorem **source code**,
not merely a symbolic finite example; kernel checks are **not observed**.
Higher-dimensional coordinates `4..n` are identically zero as in the
paper, but the general `Fin n` divergence/boundary integration is still
unimplemented. The paper's viscosity, forcing, linearization and
Nash–Moser existence theorem also remain unimplemented.

The additional `YanRadulescuPressureCountermodel.lean` carries a
concrete *one-coordinate analytic slice*:
`U=0`, `P(x)=eps*x1²/2`, `f=(eps*x1,0,0)`. Thus
`grad P=f` and `Delta P=div f=eps≠0`, while the unqualified
pressure formula (1.3) would demand `Delta P=0` because `U=0`.
This shows why the printed generic-forcing and pressure assertions
must be reconciled or supplied with an extra solenoidal-forcing
assumption. The full vector calculus and regularity assumptions are
not themselves kernel-checked in this tranche; the Lean code proves
the one-coordinate polynomial derivative formulas and the
nonzero discrepancy. Do **not** promote this adverse test into a
claim that the authors' iteration proof is false under any possible
additional assumptions.

Local execution (SymPy exact symbolic algebra, not Lean) reproduced the
source polynomial derivative/endpoint identities for **105/105** p,q,T
choices and pressure/forcing symbolic derivatives. A separate exact
`Fraction` finite-difference test passed **60/60** fixtures, with
central differences exact on the selected degree-two and degree-one
polynomials. Neither is a kernel receipt.

### Rodgers: fully labelled arrival timestamps can still underidentify source order

The initial source-world from Rodgers Section 5.2 is
`C@0ms + 80ms = C-arrival80ms`,
`E@50ms + 10ms = E-arrival60ms`, despite source `C<E`.
**DASHI extension**, not an event reported by Rodgers: a second world
takes `E@0ms +60ms=E-arrival60ms`,
`C@50ms +30ms=C-arrival80ms`, despite source `E<C`.
Both worlds yield the **same exact labelled arrival pair (C80,E60)**.
The additional typed Agda `arrivalCollisionWitness` reuses the original
nonfactorability proof owner, while
`exactCalibrationRecoversOrderForTheseWorlds` shows that externally
obtained *correct delay profiles* separate this specific pair.
This is a **consumer-relative refinement**: a decoder factoring only
through measured arrivals cannot succeed on both histories, whereas an
observer supplied with calibrated delays can. An uncalibrated receiver
has no legal access to the hidden source timestamps.

**Severe, held-out discriminator:** independently stamp source events,
precalibrate/randomize channel delays with calibration data kept separate
from source-order labels, synchronize receiver clocks, include a
nuisance-delay/noise model, mask held-out source-order labels and compare
paired receiver-only versus receiver-plus-calibration decoders on the
identical held-out events. Success must be an independently replicated
improvement on source-order recovery, not merely fitting the
recorded arrival timestamps. The test establishes order reconstruction,
**not** phenomenal passage or a neural account of conscious uptake.

### Reprioritised Ibrahim/Pareto frontier

| Rank | Next genuine producer | Acceptance / stop condition |
|---|---|---|
| P0 | Check the existing #1255/#87 declarations with actual Agda/Lean kernels | Record exact HEAD, toolchain, exit status; do not infer from static tests or CodeRabbit |
| P1 | Physically instantiate Miller's selected unforced R³ solution and direction gradients | Non-circular same-source interval, `L⁴_t L²_x` bound, exact analytic continuation proof |
| P1 | Resolve Yan source's forced divergence/pressure compatibility | Either prove `div(f)=0` from actual source assumptions, supply a corrected pressure constraint, or retain the discrepancy with its original locator; no hidden source rewrite |
| P1 | Execute independent arrival-delay calibration experiment in appropriate empirical setting | Distinguish history orders on held-out data; no consciousness promotion |
| P2 | Yan higher-dimensional/Sobolev/Nash–Moser analysis | Derivative-loss and smoothing estimates, linearized inverse, iteration/convergence, exact forcing and pressure |
| P3 | Merge and reusable theorem admission | First-commit author/date, exact-head kernel receipts, and consumer-source matching all present before proof promotion |

Source roots do not multiply when a single paper is copied into a
review/preprint/mirror or appears in sibling PRs. The new analytic
counterexample and finite two-world ambiguity are DASHI constructions
under Johl Brown's directed research with OpenAI ChatGPT assistance;
published results, older generic machinery and empirical data retain
their respective original creators. Bibliographic proximity and a
relevant PR are not evidence that a scientific hypothesis is true.


### Late latest-PR crosscheck: Agda #1271 is a separate **periodic B/R735** donor

The latest Agda PR [#1271](https://github.com/chboishabba/dashi_agda/pull/1271)
is an independently owned `T³` **periodic unforced Galerkin** local-H¹/
R735 W1 programme, with a classical **small-H¹-data** all-time
subclass. It explicitly points to Agda #1255 / Lean #87 as the existing
Miller A3 owners. Its source scope credits Leray/Temam and
Lei–Lin–Zhou, DOI 10.1007/s00205-015-0884-8, together with the
original DASHI helical mixed-output theorem owners.

Cross-pollination opportunity, **not automatic theorem import**:
a *same-periodic-source* local enstrophy ceiling X(t) bounds a
unit-direction cross-product projection by
`||v×omega||_2 <= ||omega||_2` and hence (where actual
`||omega||²_2 = X` is separately established)
`int_0^T ||v×omega||_2⁴ dt <= T sup_t X(t)²`.
This is a **finite-time** periodized input, not the R³ global
continuation result. A constant unit direction has vanishing
spatial gradient, but its finiteness through a bounded local
interval does not prove a solution extends past its maximal time.
Bridging periodic cutoffs to Miller's exact whole-space assumptions
requires explicit domain/scaling/source/limit transfers; deriving
the bound from a pre-established BKM/global-regularity theorem
would be circular. Do not import or duplicate #1271's still-open
sibling branch or imply its numerical tests kernel-certify R735.

This is the concrete Pareto decision: **reuse #1271's already
source-audited local enstrophy owner only if a future consumer pays
the same-source domain/limit transfer**. Until then #1255 remains
an exact conditional A3 interface, not a global Clay completion.


## 26 October follow-on: projected-vorticity algebra and source-translation fidelity

### New mathematical owner (Lean #87)

`RequestProject/NavierStokes/MillerProjectionGeometry.lean` is the
source-written exact finite 3-vector proof carrier. Its Lagrange identity
reads `|v×omega|²=|v|²|omega|²-(v·omega)²`.
For a *pointwise* unit `v`,
`|v×omega|²=|omega|²-(v·omega)²<=|omega|²`.
The constant z-normal gives `|v×omega|²=omega_x²+omega_y²`,
and a direction parallel to omega gives zero projection.
These are **classical vector identities** reproduced as DASHI
Lean statements, **not** a newly discovered 2026 physical theorem.

The new finite-sample fourth-power budget says
`0<=P_t<=E_t<=D` for every index in a finite sample set implies
`sum_t P_t² <= (#samples) D²`. Its mathematical role is to check
the exact exponent bookkeeping a same-source H¹/enstrophy bound
would use on a **finite horizon**, not to identify finite sums
with the physical `L⁴_tL²_x` quantity by fiat.
Locally executed exact integer/rational arithmetic passed
**15,625/15,625** six-coordinate Lagrange identities and
**225/225** finite expenditure tests. This is **NOT** a Lean
kernel receipt.

**Why not yet A3?** Miller's published criterion requires an
actual `v(x,t)` on a single unforced `R³` mild solution,
bounded `∇v` through the claimed maximal-time interval and
finite `∫ ||v×omega||_{L²_x}⁴ dt`. Pointwise domination by
`|omega|` does **not** prove that integral finite for arbitrary
large-data solutions, and setting `v=omega/|omega|` makes the
cross product identically zero without proving direction
regularity, particularly at zeros. The current R735 PR #1271
is a separate **periodic** local/small-data source:
any transfer to Miller's exact theorem must discharge the domain,
time, norm and limit interfaces instead of reusing its label.

### Recent source-faithfulness literature and native governance

Independent published source roots, distinct authority levels:

- **Evan Miller**, *A Locally Anisotropic Regularity Criterion for
  the Navier–Stokes Equation in Terms of Vorticity*,
  *Proc. AMS B* 8 (2021), 60–74, DOI
  [10.1090/bproc/74](https://doi.org/10.1090/bproc/74).
  Preprint arXiv:2002.02152 (2020) is the **same work lineage**,
  not an additional corroborating independent theorem.
- **Weiping Yan and Vicenţiu D. Rădulescu**, *Sobolev regular
  solutions for the incompressible Navier–Stokes equations in higher
  dimensions: asymptotics and representation formulae*,
  DOI [10.1007/s12215-020-00540-3](https://doi.org/10.1007/s12215-020-00540-3),
  online publication **2020-07-25**, print volume 2021.
  Its steady-forced case, full equation (1.1), displayed pressure
  equation (1.3), and Corollary 1.1 seed stay distinct objects.
- **Jeremy Rodgers**, *Experienced Temporal Passage: Enacted
  Scaffolding and the Organization of Succession*,
  manuscript dated 2026-10-23, DOI
  [10.5281/zenodo.23591626](https://doi.org/10.5281/zenodo.23591626)
  **as printed in supplied PDF**. Its constitutive theory is a
  proposal; exact observer collisions do not establish qualia.
- **Alexander Bastounis, Fabian Circelli, Anders C. Hansen**,
  *Navier-Stokes lost in translation: Why Lean verification of AI
  autoformalisation does not guarantee correct natural language proofs*,
  [arXiv:2610.08144](https://arxiv.org/abs/2610.08144), posted
  **2026-10-06**. Their authors **argue** that natural-language/formal
  correspondence fails in selected autoformalisation examples,
  including the 2026 OpenAI Navier–Stokes example. This is an
  independently identified *methodological challenge*, not a
  mathematical refutation adjudicated by DASHI, and not an
  allegation that Lean's kernel accepts false formal proofs.
- **OpenAI**, [NavierStokesAndEuler/formalization.yaml](https://github.com/openai/NavierStokesAndEuler/blob/main/formalization.yaml)
  distinguishes smooth **forced** Navier–Stokes and unforced Euler
  formal targets. Repository metadata, natural-language manuscript,
  theorem source, kernel checking and same-PDE semantics are separate.
- **Weinan Wang**, [arXiv:2609.33033](https://arxiv.org/abs/2609.33033),
  published as preprint **2026-09-27**: independent Lean Galerkin
  formalisation for **2D** unforced NS weak solutions and a forcing
  rectangle variant. Compactness/energy/theorem composition is a
  plausible donor, but no automatic 3D continuation authority.

**Repo-native reuse:** `DASHI.Core.InterpretiveFormalisationCoreExact`
already states that a source-to-formal translation need not imply
equivalence or empirical confirmation;
`DASHI.Foundations.ClaimScopeCertificateExact` already proves
that `notEstablishedHere` is not `Refutation Claim`;
`DASHI.Core.IntersectionalNonFactorability` already proves a
general consumer-collision obstruction. New
`DASHI.Papers.ThreePaperConsumerFidelity20261026Exact` simply
instantiates the *existing* generic theorem twice:

1. `eraseForceDivergence` identifies divergence-free and
   nonzero-divergence forced pressure worlds even though their
   required corrections differ. Therefore a consumer of only
   the displayed pressure equation cannot recover the missing
   source condition. The physical pressure discrepancy is separately
   demonstrated by Lean #87's polynomial derivative witness.
2. `erasePhysicalDomain` identifies whole-space `R³` and
   periodic `T³` estimate labels, even though physical source
   types differ. A proof attached to the erased label alone
   cannot establish which theorem's assumptions it satisfies.

These are **finite no-go proofs against specific lossy
projections**, not a general uncomputability result, nor an
empirical verdict on the published papers. Original source
authors retain credit; the finite witnesses and their application
are DASHI extensions. The specific source-status stage
must be tracked as `sourceCommittedOnly` until an exact-head
Agda/Lean build succeeds.

### Current Pareto/Ibrahim frontier after checking latest branches

| Priority | Actual remaining payment | Acceptance/anti-vacuity guard |
|---|---|---|
| P0 | Exact-head `lake build NSPaperBridges` and focused Agda modules, including the new fidelity regression | kernel exit status + identical commit SHA; Python arithmetic or CodeRabbit not sufficient |
| P0 | Semantic translation audit for each source-to-theorem edge | recorded DOI/page/theorem, hypotheses, domain, forcing, solution type, quantifiers, units, norms, endpoint/time interval and same-object correspondence |
| P1 | Miller genuine R³ (L⁴_tL²_x) projected-vorticity estimate | field *and* direction-derivative from same physical unforced source; no BKM circularity or periodic-to-R³ substitution |
| P1 | Yan p/q/T exponential seed to full stationary forcing/pressure PDE | exact derivative/face obligations already source-written, but remaining Sobolev, domain, `div f` compatibility, source pressure and Nash–Moser proof not silently paid |
| P1 | Rodgers held-out delay calibration and counterfactual receiver decoding | independent delay source, no source-order oracle, uncertainty/clock synchronization, adverse uncalibrated comparison; phenomenology not claimed |
| P2 | Independent external-source review | one root per original work, source publication chronology distinct from code-first SHA and kernel receipt, no derivative reprint vote counting |

**Stop rules:** Do not add another generic fidelity ontology,
bulk-copy #1271 or #1266, or repeat citation adjacency unless
a live consumer demonstrates a new unrepresented source condition.
Do not conflate **kernel trust** with **correct theorem statement**,
and do not promote a partial finite projection identity into the
unrestricted Millennium Prize conclusion.


### Executed complete 3D stationary pressure diagnostic (26 October)

Lean companion [#87](https://github.com/chboishabba/dashi_lean4/pull/87)
now owns an independently executable
`scripts/check_ns_pressure_divergence_exact.py`, original 3D
**DASHI source-consistency example** attributed to the Yan–Rădulescu
(2021) equation audit. With `U=0`,
`P=epsilon*x1²/2`, `f=(epsilon*x1,0,0)`,
and arbitrary `nu`, the script constructs the full 3-vector
steady momentum residual
`-nu*Delta(U)+(U·grad)U+grad(P)-f`
and verifies it vanishes identically. It also verifies
`div U=0`, `Delta P=div f=epsilon` and the failure of
the source's omitted-force term for `epsilon!=0`.
The original authors' general stationary theorem is not declared
invalid: the example identifies a **missing or unstated
divergence-of-forcing compatibility condition** in the displayed
equation. Check original theorem qualifiers rather than assuming
none exist.

**Executed locally using SymPy:** all symbolic 3D residual identities
passed, including `epsilon=1/1000,-1/10000,1/1000000`.
This supplements the previous **60** exact rational finite
difference tests; it is **not** a Lean kernel proof nor a
formal H^s/Nash–Moser existence result.

For exact chronology, the script's first Git source commit is
`620e35069f050018918ca8d6e38933cad5cda840`,
`2026-10-26T12:25:30Z`, Brisbane
`2026-10-26T22:25:30+10:00`; the finite sampled fourth-power
Lean lemma first appeared in commit
`10681b456753e354e10d77eec065270d7a1c3612`,
`2026-10-26T12:19:22Z`, Brisbane
`2026-10-26T22:19:22+10:00`.
The typed chronology stores `sourceCommittedOnly` rather than
conflating those events with a successful kernel check.
