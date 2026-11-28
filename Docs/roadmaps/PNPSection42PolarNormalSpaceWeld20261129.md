# Section 42 — polar observation to existing normal/fibre constructors
**Date:** 29 November 2026  
**Donor branch:** research/clay-p0-ramified-langlands-gct-20261124  
**Donor PR:** https://github.com/chboishabba/dashi_agda/pull/1549  
**Section 42 source roadmap:** https://github.com/chboishabba/dashi_agda/blob/research/clay-p0-polynomial-coverage-endpoint-20261124/Docs/roadmaps/PNPSection42GeometryForwardClosure20261129.md

## 1. Why this is an adapter, not another subsystem

The PR #1549 branch already contains the executable normal/fibre machinery:
- scripts/check_pnp_affine_normal_components.py — normal-space component decomposition, exact affine restriction and original witness solving;
- scripts/check_pnp_normal_boundary_join.py — canonical normal span, exact orthogonal/intersection tables and boundary join;
- scripts/check_pnp_normal_transversal.py — Rado-style independent representatives, deficient-core certificate and reopening;
- scripts/check_pnp_collective_fibre_escape.py — conditional overlap forest, quotient-dependent affine fibres and exact reopening;
- scripts/check_pnp_oriented_affine_elimination.py — direction discovery, existential projection and lift;
- scripts/check_pnp_adaptive_signed_escape.py and scripts/check_pnp_grouped_quotient_floor.py — adaptive and grouped signed quotient consumers.

These are existing committed implementations on PR #1549, not hypothetical future modules. Section 42 must reuse them. It must not introduce a second normal-space basis, intersection, transversal, affine-component, overlap-forest or signed-quotient implementation.

The Section 42 polar spaces are not themselves affine forbidden flats. A polar row space is a normal carrier; the original quadratic observation is still a quadratic Boolean function. The exact bridge is restriction to an affine chart, classifying which restrictions genuinely become affine and retaining every nonlinear residual.

## 2. The missing Boolean diagonal correction

Let

q(x) = c + sum_i l_i x_i + sum_{i<j} m_ij x_i x_j

be the squarefree Boolean ANF, with alternating polar matrix M. Under an invertible basis change x -> Bx,

M' = B^T M B.

But the new linear coefficient is not generally just B^T l. The diagonal terms generated while expanding q(Bx) satisfy x_i^2=x_i and therefore contribute to the linear ANF. The exact coefficient can be recovered by evaluation on basis vectors:

l'_j = q(B e_j) + q(0).

Equivalently, l' = B^T l + delta, where delta_j is the sum of the original quadratic coefficients multiplied by the two corresponding entries of column j of B. The constant remains q(0).

This is a critical source-preservation weld. Polar congruence alone is insufficient even after the original linear vector is retained; the Boolean diagonal correction must also be retained.

## 3. Exact affine-chart restriction

For an affine chart x=u+Vt, with chart directions V_1,...,V_d, define

c_t = q(u)

l_t,i = q(u+V_i) + q(u)

m_t,ij = q(u+V_i+V_j) + q(u+V_i) + q(u+V_j) + q(u).

These are exact squarefree ANF coefficients of q restricted to the chart. The local polar is V^T M V. The evaluation formulas for l_t include the diagonal Boolean correction automatically.

Classification:
- If all m_t,ij are zero and l_t is nonzero, q=0 is an affine forbidden flat and may be passed to the existing affine normal/fibre receivers.
- If the quadratic part is zero and l_t=0, c_t=0 means the whole chart is forbidden; c_t=1 means it contributes no forbidden point.
- If any m_t,ij is nonzero, retain the full restricted quadratic residual. Do not send it to an affine solver and do not drop it.

The bridge verifies the restricted polynomial at every point of the two-dimensional edge chart and rechecks every reopened candidate against the original quadratic source. An affine-subset escape is never promoted to a full source witness unless all retained nonlinear residuals also pass.

## 4. Reused construction path

scripts/check_pnp_section42_polar_normal_weld.py imports the actual PR #1549 owners:
1. normal_boundary_join.span and intersection recover the polar normal spaces and their pairwise intersections;
2. affine_normal_components.split decomposes the affine subset's normal carriers;
3. normal_transversal.transversal produces independent representatives or a deficient core;
4. collective_fibre_escape.certificate and reopen_block construct and reopen an affine-subset escape;
5. the adapter re-evaluates the complete restricted quadratic payload and maps the candidate back through the dense basis change to check the original source.

The collective fibre receiver is given only restrictions proven affine. It does not receive the nonlinear residuals as if they were flats. The original residual list stays attached throughout.

## 5. Synthetic structural control and local test boundary

The control family is a cycle incidence geometry. Each vertex observation has polar form equal to the sum of its incident edge planes, a random linear ANF part and constant one. Dense invertible basis changes are applied. The edge chart is transported by the inverse basis matrix.

For n=36,48,72,96 the local algebra/control-flow test found:
- all pairwise polar intersections recover the transformed edge planes;
- the Boolean diagonal correction is nonzero and explicitly retained;
- each edge chart has exactly two retained nonlinear residual observations;
- the other observations are classified as affine or constant;
- the affine subset can be sent to the collective-fibre receiver;
- reopened points are checked against every original quadratic observation.

The source uses constant one deliberately, so the zero point is an easy original witness. This is a structural coordinate/restriction/reopening control, not a hard SAT instance or evidence of universal witness search.

Execution qualification: the local control-flow run used API-compatible test doubles for the PR #1549 donor modules. It validates the polar, affine restriction and original-coordinate algebra, but it is not a donor acceptance run. The committed bridge script imports the real donor files and is intended to be run on this PR branch. No Agda, Lean, CI or native kernel result is claimed.

## 6. Overlap is not silently repaired

The triangle E_ab=<e0,e1>, E_bc=<e1,e2>, E_ca=<e2,e0> has total proposed summand dimension six but joint rank three. Every pairwise vertex-space intersection has dimension three rather than the claimed edge dimension two. The adapter returns OVERLAP_LATTICE_REQUIRED; it does not select an arbitrary edge plane.

The existing normal transversal still operates on the resulting normal family and can produce an independent representative/deficient-core result. That is a different receiver: it does not recover the missing edge-plane decomposition. For conditional affine overlaps, reuse the existing collective quotient/forest construction. If the quadratic observations still fail to identify a unique arrangement, preserve a non-identifiability receipt or carry the full higher-order intersection lattice into that receiver.

## 7. Exact remaining welds

| Weld | Status | Next obligation |
|---|---|---|
| Polar congruence to normal-space intersection | Finite algebra tested; donor calls in bridge | Run against actual PR #1549 modules |
| Boolean diagonal correction under dense B | Exact evaluation formula and local controls | Native GF(2)/Boolean proof and source adapter |
| Quadratic restriction to affine chart | Exact evaluation formulas; local exhaustive chart checks | Formal proof and use on actual Section 42 source observations |
| Affine-only restriction to collective fibre escape | Bridge calls existing certificate/reopen APIs | Actual donor execution; retain UNKNOWN when certificate fails |
| Nonlinear residual preservation | Bridge retains and rechecks all residuals | Weld into original Section 42 grouped-ANF source identity |
| Direct-sum promise failure | Triangle refusal control | Feed non-identifiable overlap into collective/normal consumers without arbitrary recovery |
| Rado independent transversal / deficient core | Existing PR #1549 constructor | Use as a receiver, not as a substitute for edge-plane recovery |
| Oriented projection and signed quotient | Existing PR #1549 constructors | Compose only after source-preserving affine/nonlinear split |
| Five n=32/48 exact minimum degrees | Still missing original inputs | Load original five formulas and run D=4/5 sparse closure |
| Candidate attempt scaling | Still missing per-instance attempt ledger | Measure attempts and charged work against n |
| Universal nonlinear progress | Open | No universal source coverage or P vs NP endpoint supplied |

## 8. Next implementation cut

1. Run the bridge on this branch against the real donor modules, not the API-compatible local doubles.
2. Replace the synthetic cycle observations with the exact Section 42 source matrices and affine ANF payloads.
3. For every recovered edge/chart, classify each original observation as affine, constant or nonlinear; prove the partition is exhaustive and source preserving.
4. Send only the affine subset to collective fibre escape and normal boundary/transversal consumers; retain every nonlinear residual for exact grouped-ANF closure.
5. Compare overlap cases against the existing conditional quotient forest before adding any new intersection-lattice code.
6. Compose with oriented affine elimination and grouped/signed quotient consumers only when their exact input promises hold.
7. Run the original five n=32/48 degree cases and attempt ledger separately.
8. Formalize the polar congruence, Boolean diagonal correction and affine restriction identities in the native proof owners.

This bridge is a real architectural weld between Section 42 and the existing PNP machinery. It is not a universal producer. All thirteen universal endpoint contracts remain open.
