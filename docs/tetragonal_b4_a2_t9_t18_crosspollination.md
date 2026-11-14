# B4 / A2 / T9 / T18 crystallographic reuse cut

## Established mathematics and attribution
The crystallographic D4h point group is the Coxeter/Weyl group
W(B2)×W(A1), order 8×2=16. It embeds into the signed permutation
groups W(B3) (order 48) and W(B4) (order 384) via block-diagonal
signed matrices. It is not the 4-dimensional B4 group itself.
W(A2)≅S3, order 6, with the even-permutation subgroup C3, order 3.
These are classical facts, not discoveries from this PR.

## Repo prior art (native owners)
- Biology.D4NineCellOrbitCompressionExact: distinct centre/edge/corner
  D4 orbit types; do not collapse the corner into the edge orbit.
- Reasoning.TrialecticObserverMatrix369Exact: ObserverMatrix3 (View);
  positional D4 operations lift polymorphically to fields.
- Reasoning.Trialectic369DyadicKernel4DescentCountExact:
  the T4 ×3 minus T1 ×3 chart-overlap count of T9.
- Reasoning.Trialectic369DyadicLocalComplementFactorizationExact:
  T9 ↔ T4-local × T5-complement coordinate rechart.
- Reasoning.TrialecticGrothendieckTransportCoherenceExact:
  existing C3 chart transport, distinct from tetragonal C4.
- Reasoning.TrialecticThreeCellHyperformSynthesisExact:
  six independent T3 cells forming a T18 compatible boundary.

## New exact source-level bridges
- Mathematics.Symmetry.TetragonalNineCellD4BridgeExact:
  an equivariant forget-height projection to the NineCell edge orbit.
- Mathematics.Symmetry.TrialecticT9D4ConfigurationActionExact:
  literal positional r and s acting on ObserverMatrix3 View, with
  r^4=s²=1, srs=r^-1 proof terms by record constructor matching.
- Mathematics.Symmetry.TrialecticT18CyclicBoundaryActionExact:
  an even A2 three-cycle rotating simultaneously participant
  (A,B,C) and synthesis (SAB,SBC,SCA) cells, so the six-cell
  boundary compatibility is preserved by reconstruction.
- scripts/tetragonal_b4_a2_trialectic_bridge_audit.py:
  literal signed-permutation subgroup checks, C3 and reflection
  fixed-point obstruction.

## Open naturality cuts
The T9 position-permutation action is not yet shown to commute with
the pre-existing T4 local-chart restrictions, because a rotation
must also transport the chart index and overlap labelling.
An equality holding after permuting the global 3×3 matrix is not
automatically a *same-index* AB local-section equality.
For T18, the three-cycle is defined and transported by the existing
coordinates/compatible-boundary maps; the arbitrary-boundary
three-cycle theorem depends on the owner's exact round-trip proofs,
and no unverified transport across an irreducible synthesis face
is asserted. The B4 and A2 facts have computational checks but
no newly constructed Coxeter-root Agda/Lean equivalences.

## Attribution/verification boundary
All group/Weyl facts are classical. The DASHI contribution is
typed use of existing chart records, new finite carrier maps and
audits. Agda modules contain submitted proof terms, not a
compiler-accepted receipt in this session. The screenshot is not
material evidence for microscopic crystal structure or magnetic
order. No CI claim is made.
