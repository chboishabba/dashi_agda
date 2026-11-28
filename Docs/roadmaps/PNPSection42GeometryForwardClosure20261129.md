# P vs NP — Section 42 geometry-forward closure campaign
**Date:** 29 November 2026  
**Integration branch:** research/clay-p0-polynomial-coverage-endpoint-20261124  
**Controlling PR:** https://github.com/chboishabba/dashi_agda/pull/1548

## 0. Claim boundary and execution policy

This tranche turns the Section 42 review into executable, source-preserving controls. It does not promote the structured producer to a universal SAT solver and does not discharge any of the thirteen universal endpoint contracts. A finite acceptance result is not a Clay result.

The construction order remains: recover the whole geometric carrier first; expose every promise and overlap; preserve the complete original Boolean observation; solve exact finite closure; then refine resource bounds and native proof replay. Do not replace this with unrelated test-only patches.

## 1. Repository reconciliation — existing work reused

The default branch was checked at master commit c67d5d0e51f98d6171e77f440ddacc717a3201d8. The controlling P vs NP work is concentrated in open draft PR #1548, head 0eb2a1ed8d60481f9377b89685ff48aa67671693 at audit time. The branch was 787 commits ahead and one commit behind master; GitHub reported it mergeable. The PNP roadmap and donors below are on that PR branch, not yet on master.

| Existing owner | Relevance | Boundary retained |
|---|---|---|
| DASHI/Mathematics/Complexity/PNPOriginalHallPigeonholeExact.agda | Source-derived Hall/PHP counting and partition receiver | Counting certificates do not establish proof-system hardness |
| scripts/check_pnp_hall_geometry.py and scripts/check_pnp_hall_portfolio_campaign.py | Existing syntactic row/clique discovery and original-witness replay | No supplied pigeon/hole partition; only recognized source geometry |
| scripts/check_pnp_boolean_fibre.py and scripts/check_pnp_boolean_separator_campaign.py | Existing Boolean fibre and separator constructions | Scoped source families, not universal coverage |
| scripts/check_pnp_observation_lift.py | Existing bounded local ANF observation lift and original reopening | Width/scope limits and overlap refusal remain real |
| DASHI/Mathematics/Complexity/PNPQuadraticMobiusExact.agda | Existing ternary/F3 quadratic and Boolean-cube intersection donor | It is not a GF(2) polar congruence proof |
| Docs/roadmaps/ClayP0SevenRouteExactRemainingLemmas20261126.md | Seven-route map and thirteen universal endpoint contracts | All universal targets remain open |
| Docs/roadmaps/ClayPNPResidualGeometryForwardMaxCut20261128.md | Latest residual-geometry/max-cut work, including source ANF lift | Scoped finite work is not uniform affordable progress |

The local Section 42 commit 82d3cd07add0 was not retrievable from GitHub. Its report is therefore treated as supplied prior evidence, not as a remotely verified source commit. The five n=32/48 degree instances and the full recovery-attempt CSV were not present in the attached report or PR #1548's changed-file list. This tranche does not invent those inputs.

## 2. Polar geometry — exact identity and promise boundary

Write a squarefree quadratic Boolean polynomial as

q(x) = c + sum_i b_i x_i + sum_{i<j} a_ij x_i x_j.

Its polar is

beta_q(x,y) = q(x+y)+q(x)+q(y)+q(0)
            = sum_{i<j} a_ij (x_i y_j + x_j y_i).

Thus its matrix M_q is alternating. Under q_B(x)=q(Bx), for invertible B over GF(2),

M_(q_B) = B^T M_q B.

Since left multiplication by B^T preserves row rank and right multiplication sends row vectors r to rB, the row space transforms as B^T row(M_q). Hence intersection dimensions and incidence relations are invariant under arbitrary invertible changes of basis, not merely sparse shears.

For the graph construction,

U_v = direct_sum_{e incident to v} E_e

implies U_v intersect U_w = E_vw for adjacent vertices. This conclusion requires the global direct-sum promise. It is not justified by the pairwise formula alone. The producer must check that the concatenated edge-plane basis has rank equal to the sum of the plane dimensions before using pairwise recovery.

### Executable dense-basis control

scripts/check_pnp_section42_geometry_forward.py constructs cycle incidence carriers at ambient dimensions 36, 48, 72 and 96, builds the actual alternating matrices, applies dense random GL(n,2) congruences, recovers row spaces from the transformed matrices, and checks every pairwise intersection against the transformed edge planes. The deterministic self-test passed at all four dimensions. Observed matrix densities were approximately 0.476, 0.486, 0.510 and 0.511. This is a finite covariance test of the actual matrix congruence, not evidence of a universal decomposition algorithm.

### Promise-violating arrangement control

The triangle arrangement E_ab=<e0,e1>, E_bc=<e1,e2>, E_ca=<e2,e0> has six total summand dimensions but joint rank three. Every pairwise vertex-space intersection has dimension three, not the claimed edge dimension two. The producer returns OVERLAP_LATTICE_REQUIRED rather than selecting an arbitrary pairwise plane.

### Exact next overlap weld

Generalize from direct sums to an indexed intersection lattice I_S = intersection over v in S of U_v. Retain:
- every nonempty higher-order intersection and its inclusion maps;
- overlap multiplicities and the rank defect of the proposed summands;
- compatibility equations among the original quadratic observations on those intersections;
- the full affine/constant ANF data;
- an original-variable witness reopening receipt.

The target is a unique decomposition only when the observations identify one. Otherwise the correct result is a family of compatible decompositions or an explicit non-identifiability receipt. Pairwise intersections alone are insufficient. The triangle control is only a refusal test; the general lattice compatibility solver remains open.

## 3. Polar information loss — preserve the complete Boolean source

Polarization discards the linear and constant parts. It also presupposes squarefree Boolean normalization: x_i squared equals x_i, so diagonal quadratic terms reduce to linear terms. The executable control constructs distinct ANFs with the same polar and checks x_i^2=x_i normalization.

The source object carried by the producer must therefore retain:
1. the alternating polar matrix;
2. the squarefree linear coefficient vector;
3. the constant coefficient;
4. original clause/block identity and nonlinear observation table;
5. the affine reopening map back to original variables.

A recovered polar decomposition is a geometric index, not a replacement for the original equations. Every proposed component assignment must be checked against the complete original ANF and original source constraints.

Also keep two problems distinct:
- decomposition of a family of bilinear forms into common direct-sum blocks;
- isometry testing between two such families.

The current result concerns the first, under an explicit incidence promise. It does not solve family isometry. Wilson-style adjoint-algebra methods are a possible donor for decomposition; class-2 p-group isomorphism complexity is a warning against silently upgrading this to general isometry.

## 4. Sparse exact degree closure — executable producer

The new sparse engine accepts either raw grouped-ANF axioms, each polynomial represented by squarefree monomial bitmasks, or CNF clauses converted to Boolean clause-violation ANFs.

For degree D it maintains a sparse GF(2) row basis S. For each variable x_j it projects onto degree-D monomials not containing x_j and computes a provenance-carrying basis for ker(pi_j restricted to S). Every kernel relation is multiplied by x_j in the Boolean quotient, with duplicate monomials cancelling mod 2. It iterates

S <- S + sum_j x_j ker(pi_j restricted to S)

until 1 is in S or the span stabilizes.

The projection-kernel construction is the key weld: it admits combinations whose degree-D terms cancel before multiplication. It is not equivalent to multiplying each current basis row separately. The code uses sparse monomial supports rather than allocating the full Macaulay column universe.

Result meanings:
- REFUTED: the constant-one polynomial is in the admitted span.
- STABLE_NO_REFUTATION: exact fixed point reached for this declared inference system and degree.
- UNKNOWN_RESOURCE_CENSORED: row/work/time cap hit; this is not a lower bound.
- exact_minimum_in_tested_degrees is emitted only when every lower tested degree stabilizes without refutation and the candidate degree refutes.

The work counter is an explicit logical row/monomial scan proxy, not a machine-bit clock. The wall cap, sparse-row count, coefficient encoding, serialization, discovery attempts and original-source reification still need a full bit-complexity ledger.

### Why n=32 and n=48 need sparse columns

| n | degree at most 4 | degree at most 5 |
|---:|---:|---:|
| 32 | 41,449 | 242,825 |
| 48 | 213,053 | 1,925,357 |

The Section 42 n=32/48 cohort is exactly where materializing all degree-five columns becomes unattractive. The new engine records columns actually touched and stops with UNKNOWN under explicit caps.

### Exact source inputs still required

The five original n=32/48 neutral instances are not included in the attached Section 42 report. Supply them in a JSON file using either:
- degree_cases[].axioms: list of ANF polynomials, each a list of integer monomial masks; bit 0 denotes x1 and mask 0 denotes the constant monomial; or
- degree_cases[].clauses: signed-literal clauses, only if clause-violation ANFs are the intended source axioms.

Each case must retain source_id, family, n, degrees and coupled_constraint_control. Use the original grouped-ANF axioms for direct comparison with Section 42; CNF conversion is a separate proof-system encoding.

The committed smoke fixture uses the eight width-three clauses on the first three variables, padded with unused variables to n=32 and n=48. It checks sparse support and the degree-three floor only. It is not one of the five neutral calibration instances and must not be reported as such.

The previously reported static degree five versus iterative degree three remains a supplied Section 42 result; this tranche implements the iterative saturation path and does not independently reproduce that historical comparison. Conventional polynomial-calculus degree and this grouped Boolean quotient degree must not be identified without an explicit translation theorem.

## 5. Recovery attempts and duplicate-family integrity

The new recovery-record reader requires source_id, family, n and attempts, and accepts a stable source_fingerprint. It groups attempts by n and rejects duplicate-looking families unless every duplicate is explicitly marked coupled_constraint_control. This prevents hidden and hidden_extra rows from being silently counted as independent evidence.

The current self-test uses synthetic records solely to test the metadata guard. It does not claim an empirical attempt-versus-n trend. The Section 42 report only gives a 2–12 attempt range for four extra-clause cases, not the per-instance mapping needed for a scaling analysis.

Required next data: original source fingerprint and exact family label; n and graph/constraint density; candidate attempts, failed-attempt reason and work charged per attempt; whether added constraints were independently satisfiable; whether their combination was compatible or contradictory; and whether original witness reopening or degree-two proof replay succeeded.

Only then fit attempts versus n, and report both candidate count and total charged work. A low attempt count on four cases is not a polynomial bound.

## 6. PHP with auxiliary exclusions and clique-colouring control

The executable source builder introduces auxiliary exclusion bits e_h. Each pigeon row gives sum_h x[p,h] at least one; each hole column has capacity at most one; x[p,h] is forbidden when e_h=1; and exactly r holes are excluded. Summing yields

p <= sum_(p,h) x[p,h] <= sum_h (1-e_h) = h-r.

The source recognizer independently reconstructs positive pigeon rows, negative same-hole cliques, the e_h-to-column exclusion clauses, and the exact auxiliary cardinality. The self-test checks the contradictory case p=3,h=3,r=1 and a satisfiable boundary control p=2,h=3,r=1. This is an auxiliary-variable extension of the existing Hall/PHP constructor, not a new proof of hardness.

The clique-colouring control is kept separate. The finite script checks the two semantic sides on K3 and K2,2 and exhausts all 64 graphs on four vertices to ensure no graph simultaneously has a 3-clique and a 2-colouring. It does not prove Pudlák's asymptotic lower bound. The relevant proof-complexity boundary is the monotone-real interpolation lower bound for the clique-colouring disjoint pair / cutting-planes reflection setting (Pudlák, Journal of Symbolic Logic 62(3), 981–998, 1997; DOI: https://doi.org/10.2307/2275583). Fixed-witness branch contradictions can reduce to PHP, but that does not provide the global monotone interpolant. The counting producer must not claim to solve that lower-bound problem.

## 7. Executable acceptance and committed artifacts

New files:
- scripts/check_pnp_section42_geometry_forward.py
- scripts/fixtures/pnp_section42_degree_smoke_20261129.json
- scripts/receipts/pnp_section42_geometry_forward_selftest_20261129.json
- scripts/receipts/pnp_section42_degree_smoke_20261129.json

Local commands already executed successfully:
- python scripts/check_pnp_section42_geometry_forward.py --self-test
- python scripts/check_pnp_section42_geometry_forward.py --input scripts/fixtures/pnp_section42_degree_smoke_20261129.json --output scripts/receipts/pnp_section42_degree_smoke_20261129.json --max-rows 10000 --max-work 1000000 --seconds 5

Self-test results:
- dense-B congruence and all pair intersections: 4/4 dimensions PASS (36,48,72,96);
- explicit overlap triangle: direct-sum rank defect detected, producer refuses unique plane recovery;
- affine/constant loss and squarefree diagonal control: PASS;
- sparse degree floor: lower degrees 0,1,2 stable; degree 3 refutes the eight-clause three-variable control;
- same sparse control at n=32 and n=48 touches only eight monomial columns;
- auxiliary PHP source discovery and boundary controls: PASS;
- clique-colouring semantic control: 64/64 four-vertex graphs;
- duplicate-family guard: PASS, including refusal without the coupled-control label.

The two smoke inputs return exact minimum degree 3 in their tested grouped Boolean quotient system. These are floor controls, not the five missing neutral instances.

## 8. Exact remaining lemmas and welds

| Lemma / weld | Current status | Exact remaining obligation |
|---|---|---|
| polarCongruenceRowSpaceCovariance | Executable dense-B control PASS; elementary identity derived above | Native Agda/Lean proof over the chosen GF(2) matrix owner and actual source-matrix adapter |
| directSumIncidencePromiseAudit | Rank check implemented | Prove producer rejects every failed promise before pairwise recovery |
| overlapIntersectionLatticeCompatibility | Open | Higher-order intersection lattice, compatible overlap maps, uniqueness/non-identifiability and original witness reopening |
| affineANFReopening | Finite information-loss control PASS | Carry linear, constant, diagonal-normalization and original nonlinear tables through the real producer |
| decompositionVsIsometryScope | Boundary clarified | Do not claim general family isometry; if required, prove a separate adjoint-algebra/isometry theorem |
| sparseGroupedANFKernelCompleteness | Exact sparse fixed point implemented for declared system | Native proof of projection-kernel completeness, independent certificate replay and proof-system translation |
| degree32And48ExactMinimum | Smoke controls PASS | Load the five original formulas, complete lower degrees and D=4/5 under explicit resource caps |
| candidateAttemptPolynomialCost | Metadata schema and duplicate guard implemented | Original per-instance attempt/work ledger and a genuine polynomial upper bound |
| auxiliaryPHPWithExclusions | Python source discovery and counting control PASS | Native proof/source adapter and broader auxiliary encodings |
| cliqueColourInterpolationBoundary | Small semantic control PASS | Keep Pudlák's global monotone-real lower-bound theorem separate; no lower-bound proof added here |
| uniformNonlinearCoreProgress | Still open | Universal affordable source-derived choice, coverage or verified bypass |

## 9. Relation to the thirteen endpoint contracts

This tranche does not discharge any of the thirteen universal contracts. It contributes scoped receivers to the existing constructive route: polar incidence recovery can feed the nonlinear core; sparse exact closure can provide a degree-bounded refutation; auxiliary PHP can strengthen source-derived counting; and the overlap lattice can become a compatibility/observation route.

It does not establish uniformNonlinearCoreProgress, uniformVerifiedSuccessMass, conditionalBoundedContrast, weightedExceptionalContrastBound, uniformIsolatingPortfolio, deterministicSufficientObservation, globallySoundRelativeSupport, any of the four unrestricted S1 obligations, fullCodeGainTotality, or sameObjectResourceClosure.

The seven-route roadmap remains authoritative. These are alternative endpoint routes, not thirteen serial tasks. No P=NP or P!=NP claim is made.

## 10. Next coherent implementation cut

1. Recover the exact five n=32/48 grouped-ANF source instances and the original Section 42 recovery CSV from the local bundle; preserve source IDs and family labels. Do not substitute generated random formulas.
2. Run degrees 0–5 for each exact source with checkpointed row/work/time caps. Persist every lower-degree stable span, D=4/5 refutation or explicit UNKNOWN receipt. Compare iterative and static axiom-only spans separately.
3. Extend the overlap triangle to nontrivial rank-two/rank-three arrangements. Compute the full intersection lattice, test multiple decompositions with identical pairwise intersections, and use affine/nonlinear original observations to distinguish or certify non-identifiability.
4. Weld the recovered arrangement into existing normal-space, Boolean fibre, ANF observation-lift and original witness-reopening machinery. Preserve UNKNOWN on unsupported overlap or failed reopening.
5. Load the actual attempt records; calculate per-n attempt distributions and total work, including failed candidate tests and source discovery.
6. Formalize the polar congruence and sparse kernel fixed-point rules in the existing native GF(2)/Boolean proof owners. The current F3 quadratic module is a donor for structure, not a substitute for GF(2).
7. Add auxiliary-variable PHP and clique-colouring source controls to the existing Hall/PHP campaign without replacing the current default route.
8. Only after these scoped welds are integrated, revisit their contribution to universal constructive progress. Keep the unrestricted S1/R1 lanes separate.

No CI, Agda or Lean kernel run is claimed in this tranche. The Python self-test and fixture were executed locally; the five source-specific degree results and native certification await the original inputs and user-side execution.

## 11. Cross-PR donor audit — do not rebuild existing normal/fibre machinery

A second audit of open PR #1549 found executable donors already covering much of the apparent overlap gap:
- scripts/check_pnp_affine_normal_components.py — intrinsic affine normal-component decomposition;
- scripts/check_pnp_normal_boundary_join.py — canonical normal span, exact intersection and boundary join;
- scripts/check_pnp_normal_transversal.py — Rado independent representatives and deficient-core recovery;
- scripts/check_pnp_collective_fibre_escape.py — conditional overlap forest, quotient-dependent intersections and exact reopening;
- scripts/check_pnp_oriented_affine_elimination.py — existential projection and lift;
- scripts/check_pnp_adaptive_signed_escape.py and scripts/check_pnp_grouped_quotient_floor.py — adaptive/grouped signed quotient consumers.

These files are committed on PR #1549 branch research/clay-p0-ramified-langlands-gct-20261124, not master and not yet in PR #1548's branch. The Section 42 bridge is committed there as scripts/check_pnp_section42_polar_normal_weld.py at commit 8c1091c45c3ffa8c1eb87f527fcce61d9137c07, with its roadmap Docs/roadmaps/PNPSection42PolarNormalSpaceWeld20261129.md.

Therefore revise the earlier overlap work order: do not build a second general normal-space, affine-component, transversal, boundary-join or conditional overlap-forest subsystem. First adapt the recovered polar spaces into these existing owners. A higher-order intersection lattice is still a valid explicit certificate when the existing conditional quotient receivers cannot distinguish arrangements, but it is not the default subsystem to rebuild.

## 12. Critical squarefree-ANF correction under dense basis changes

The polar still transforms by M' = B^T M B, but the canonical squarefree linear coefficient does not generally transform by B^T l alone. For q(x)=c+sum_i l_i x_i+sum_{i<j}m_ij x_i x_j,

l'_j = q(B e_j) + q(0).

This includes the diagonal contributions generated by expanding the quadratic terms and reducing x_j^2 to x_j. The constant remains q(0). The new bridge implements this evaluation formula and checks q'(x)=q(Bx).

For an affine chart x=u+Vt, the exact restricted squarefree coefficients are

c_t = q(u),

l_t,i = q(u+V_i)+q(u),

m_t,ij = q(u+V_i+V_j)+q(u+V_i)+q(u+V_j)+q(u).

Only if every m_t,ij vanishes may q=0 be passed to the existing affine-flat/fibre constructors. Otherwise the restricted quadratic polynomial remains a nonlinear residual. The bridge retains it and checks every reopened candidate against the full original source.

The bridge's local control-flow receipt used API-compatible test doubles for the PR #1549 modules. It is not a real donor-module acceptance run. The script imports the actual donors and is ready for execution on PR #1549's branch. Its synthetic source uses constant one, so the zero point is an easy witness; this validates coordinate/restriction/reopening, not witness search on the five original neutral instances.

## 13. Revised remaining path

1. Run the polar-to-normal bridge against the actual PR #1549 modules.
2. Replace synthetic cycle forms with the exact Section 42 polar matrices and complete affine ANF payloads.
3. For each chart, classify all original observations as affine, constant or nonlinear; prove this partition is exhaustive. Send only affine restrictions to collective fibre escape, normal boundary join and Rado receivers.
4. Recheck every returned point against all nonlinear residuals and the original source; never promote an affine-subset escape alone.
5. Use oriented affine elimination and signed/grouped quotient consumers only after their exact source promises are satisfied.
6. Load the five original n=32/48 grouped-ANF instances and the per-instance recovery-attempt ledger; run D=4/5 and candidate-work scaling.
7. Formalize the polar congruence, Boolean diagonal correction and affine restriction identities in the native GF(2)/Boolean proof owners.

The Section 42 bridge and the PR #1549 donor suite are separate open branches. No cherry-pick or merge has been performed. All thirteen universal endpoint contracts remain open.
