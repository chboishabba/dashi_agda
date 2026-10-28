# Horned C3 attribution and acceptance ledger — 2026-10-25

## Provenance discipline (source roots, not repeated citations)

1. **J. W. Alexander (1924)**: original horned-sphere counterexample; historical mathematical source, not new DASHI construction.
2. **Allen Hatcher, Algebraic Topology, Example 2B.2**, PDF pp. 178–180 (printed pp. 170–172), https://pi.math.cornell.edu/~hatcher/AT/AT.pdf: explicit decreasing handlebodies X_n, increasing exteriors Y_n, punctured-torus attachment, pi1(Y_n)=F_(2^n), injection sending each meridian to a commutator, and compactness-based direct limit. This is **the original proof source for the version of the exterior group used here**.
3. **Franca Lippert, The Alexander Horned Sphere and Bing's Hooked Rug**, §§2.1–2.3, https://www.maths.gla.ac.uk/~mpowell/WriteUp_Franca.pdf: expository supported pillbox construction, shrinking horns, wild-point Cantor set. Its figure credits and bibliography should be retained as upstream provenance; this exposition is not an independent new discovery of Alexander's sphere.
4. **Existing DASHI PR #1244**: chosen threefold placement, radial spokes, exact sphere atlases, C3 action and conditional free-product gluing, group and gauge simulators. New composite claims require proof that their *specific* wild satellite and collar interfaces satisfy the corresponding classical hypotheses. Numerical samples do not settle infinite point-set topology.
5. **Existing Lean and Agda consumers**: `proofs/horned_c3_lean/HornedC3/ThreeArmVanKampen.lean` consumes path connectivity, open-cover and trivial-overlap certificates; `ThreeArmCollarIntersections.lean` handles set identities; `DASHI/Mathematics/Topology/AlexanderHornedC3ExteriorBridge.agda` handles abstract meridian/rotation relations. Do not cite these as discharged geometric existence certificates or as kernel-checked without exact-head compilation.
6. **Experimental prior art**: Sugawa et al. (2021), DOI 10.1038/s41534-021-00483-2, and Liang et al. (2024), DOI 10.1038/s41567-024-02644-4, demonstrate non-Abelian controls in their respective settings. Neither claims a horned-sphere experimental device.

## Higher-resolution split of what is accepted

| Claim | Status | Next evidence gate |
|---|---|---|
| Classical one-sector Hatcher exterior group | Original published mathematical construction | Cite original text and exact page |
| Threefold rotation symmetry of a chosen Euclidean scaffold | Explicit equations and finite checks in PR | Prove invariance of the fully instantiated infinite wild ball |
| Collar cap and separator open-disk stereographic model | Exact algebra plus source-supported geometric setup | Supply global maps and genuine open cover of the **same** exterior |
| Free product of 3 Hatcher groups for glued exterior | Classical paper-level cut-and-paste argument with hypotheses | Instantiate actual satellite-side deformation retractions and Lean cover structure |
| Abstract order-three outer rotation on free product | Group-theoretic retraction argument | Transport through a proved equivariant geometric isomorphism |
| Finite 2I recursion and SU2 actor | Existing exact finite scripts, independent numerical audit | Exact-head execution and tests |
| iid isotropic SU2 noise mean | Analytic derivation in preceding cut | Cross-check actual horn-word compiler and its trial uncertainty |
| Physical AB/holonomy, Maxwell/Dirac effects | Not established | Device, local flatness validation, matched controls, measurements |

## New code acceptance envelope

`scripts/alexander_horned_c3_wilson_statistical_acceptance.py` supplies a conservative Hoeffding acceptance radius for independent trial means. If N independent trials have bounded readout X_i in [-1,1], then

`P(|mean_N-E[X]| >= eps) <= 2 exp(-N eps²/2)`.

At simultaneous confidence c for m tested depths, a union-bound radius is

`sqrt(2 log(2*m/(1-c))/N)`.

For the specified unbiased ancilla readout with independent per-trial gates, E[X] is the noise-envelope mean

`-exp(-3*4^depth*sigma_rad²/8)`.

This does **not** imply independence of individual gates in real equipment, laboratory repeatability, a physical non-Abelian flat connection, or direct measurement of a limiting wild complement. The statistical bounds are deliberately conservative; calibrated shot and run variance can offer sharper estimators when justified.

## Pareto + snowball/Ibrahim source-following priorities

**P0: same-object proof**. Follow Hatcher's original punctured-torus van Kampen attachment and Lippert's supported construction back to the concrete threefold satellite. Reuse Lean `ThreeArmCollarCover` rather than writing another abstract free-product theorem. Highest-value target is one explicit certificate that the *actual* satellite open piece deformation-retracts onto a Hatcher exterior with the prescribed meridian maps. Source papers should be read for hypotheses and exact scope, not for coincident vocabulary.

**P1: exact-head integration verification**. Run both current analytic and existing actual-word tests, then kernel/typecheck only the precise imported theorem chain. Report failures separately as source-level, dependency-resolution, typechecking, and geometric-hypothesis gaps.

**P1: practical finite gauge protocol**. Quantify noise and shot uncertainties independently; test curvature/plaquette flatness separately from Wilson response. Do not infer an experimental topology from synthetic gates.

**P2: direct Maxwell/Dirac consequences**. Require a concrete operator/domain and boundary conditions before claiming a spectral observable. Exotic propulsion/free-energy/quantum-consciousness connections have no evidence from this construction.

## Attribution guardrails

Keep separate: original mathematical sources; secondary exposition; source-written implementation; executable finite witness; proof-checker acceptance; model predictions; external-world experiments. Do not promote analogy, shared notation, repeated secondary reporting, compatible representation or quotient into geometric identity, independent corroboration or physical proof.
