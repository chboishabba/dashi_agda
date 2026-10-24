# Three-paper formal integration: Pareto / snowball / Ibrahim max-cut
Date: 2026-10-25 (Australia/Brisbane). Status: implementation/source audit; no new Clay or phenomenology promotion.

## Original source objects (not interchangeable)

| Root | Publication/locator | Original claim | Our reconstruction |
|---|---|---|---|
| Evan Miller | *A Locally Anisotropic Regularity Criterion for the Navier–Stokes Equation in Terms of Vorticity*, Proc. AMS Series B **8** (2021), pp. 60–74, DOI: [10.1090/bproc/74](https://doi.org/10.1090/bproc/74), Theorem 1.6, Section 2 | Conditional **unforced**, whole-space, 3D mild-solution continuation with bounded direction gradient and finite scale-critical projected-vorticity norm | Lean algebraic 3-component identity and critical exponent arithmetic; Agda same-source A3 contract. The source theorem is **not** re-proved in Lean, and its hypotheses are not established by generic energy. |
| Weiping Yan and Vicenţiu D. Rădulescu | *Sobolev regular solutions for the incompressible Navier–Stokes equations in higher dimensions: asymptotics and representation formulae*, Rend. Circ. Mat. Palermo II. Ser. **70** (2021), pp. 995–1021, online 2020-07-25, DOI: [10.1007/s12215-020-00540-3](https://doi.org/10.1007/s12215-020-00540-3), Eqs. (1.1)/(1.3), Theorem 1.1, Cor. 1.1 | **Steady forced**, bounded-domain solutions under small forcing and additional hypotheses; Nash–Moser scheme and explicit cube family | Lean exact scalar divergence-balance and cyclic-derivative cancellation; Agda forcing-divergence preservation with explicit source attachment. The full Nash–Moser/elliptic/PDE proof is **not** formalised. |
| Jeremy Rodgers | *Experienced Temporal Passage: Enacted Scaffolding and the Organization of Succession*, independent research manuscript **2026-10-23**, DOI **as printed on uploaded PDF**: [10.5281/zenodo.23591626](https://doi.org/10.5281/zenodo.23591626), Proposition 1, Proposition 5, Appendix C | Given constitutive premises, a qualifying enacted temporal structure has experienced succession without an additional constitutive advancing-present variable; finite order and prefix invariants | Reuses original DASHI nonfactorability machinery for a finite CE/EC counterexample; proves local-prefix fold law and retrieval-independent *stipulated* admission. NOT a proof that the constitutive premises are empirically true or a consciousness detector. |

The two Navier–Stokes sources are **not** independent confirmations of the same regularity statement. The third paper's finite propositions do **not** empirically certify experienced character.

## Existing authoritative owners and what was reused

- [NS canonical residual scheduler](../../DASHI/Physics/Closure/NSCanonicalClayResidualExact.agda): A1/A2/A3, periodic B, C/D, all with nonpromotion gates. A3 is the only consumer of the new Miller adapter; do not create a replacement Clay theorem owner.
- [NS canonical A3](../../DASHI/Physics/Closure/NSCanonicalA3ContinuationResidualExact.agda): requires a literal continuation predicate on the original selected physical source.
- [NS exact strain eigenbundle](../../DASHI/Physics/Closure/NSExactStrainEigenbundleHarnessBoundary.agda): Biot–Savart / Leray / finite-symbol harness; this is not a proof of a cutoff-uniform physical direction field.
- [NS banded vorticity](../../DASHI/Physics/Fluid/BandedVorticityCrossPollination.agda): signed finite atoms, not continuum vorticity.
- [History-conditioned choice](../../DASHI/Core/HistoryConditionedChoiceExact.agda) and [intersectional nonfactorability](../../DASHI/Core/IntersectionalNonFactorability.agda): the latter is the actual proof dependency for Rodgers's order-erasure witness.
- [Temporal restriction before quotient](../../DASHI/Cognition/PNF/DemandLocalWildcardTemporalOrderExact.agda): the source-order / arrival-order distinction must not be erased by a coarse history quotient.
- [Consciousness instantiation boundary](../../DASHI/Governance/ConsciousnessAbstractionInstantiationBoundaryExact.agda): code equivalence, physical implementation, actual uptake and phenomenology are different claims.
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
- **Fail closed**: Agda typechecks and Lean kernel checks have not been observed in the GitHub connector; the static tests are not substitutes. Neither paper supplies an unconditional global-unforced 3D regularity result or an empirical consciousness proof.
