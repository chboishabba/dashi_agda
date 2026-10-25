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
