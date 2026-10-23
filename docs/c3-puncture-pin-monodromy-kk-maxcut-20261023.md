# Punctured T9 / Pin / KK braid max-cut

## Precise distinction
A **puncture** is removal of a point from a geometric carrier. `Pin(p,q)` is the Clifford-theoretic double cover of the full orthogonal group `O(p,q)`, including orientation reversing reflections. They are NOT etymologically or definitionally the same. Their connection is that a punctured domain has noncontractible loops on which a chosen Pin/Spin bundle can have nontrivial monodromy / spin structure. A puncture *does not automatically force* a Pin rather than Spin structure: the oriented punctured plane is orientable and spin.

## Existing actual owners (not newly invented)
- `DASHI/Foundations/Base369FaceSheetPunctureIncidenceIdentityExact.agda` realizes each cube outer face as 9 positions, with one centre and eight noncentral positions; 6×9=54 counts incidences, not distinct cube vertices.
- `DASHI/Moonshine/OggSSPP2BalancedTernaryPuncturedPlaneExact.agda` has a typed eight-position punctured balanced-ternary T9 sheet and a duplicated-centre F4-shaped target. This is a finite discrete carrier, not by itself a smooth R² minus origin.
- `DASHI/Moonshine/JInvariantPuncturedLatticeReindexExact.agda` transports nonzero lattice points through SL2(Z) reindexings.
- `DASHI/Foundations/C3NineSiteSixStepMirrorExact.agda`, `C3ReflectionCliffordPinBridgeExact.agda` and `C3O2SignedWindingTransportExact.agda` are the independent mirror, generator Pin, and framed winding/parity owners.

## New obstruction + positive model
`scripts/check_c3_punctured_sheet_pin_winding.py` confirms all three phase-shifted strands of the *actual 12-time-step path on a 9-position sheet* pass through centre `(0,0)` twice each. Therefore they are NOT maps to the centre-punctured plane, and no winding number about this puncture can be assigned to the current unmodified paths. A separately chosen perimeter loop of the eight noncentral T9 positions does avoid centre, winds +1 about it, and its horizontal mirror winds -1. Two mirrors return winding +1.

The sample loop represents a continuous polygonal path in R² minus origin. It is not the current three-strand braid and cannot be substituted for it without an explicit homotopy or path modification maintaining the required physical constraints. In particular a local detour around the removed centre is a *new model choice*, with winding sign and C3/gluing compatibility to prove.

## Geometric Pin / spin / braid connections
The spatial reflection `M_x=diag(-1,1)` is orientation-reversing. Its lift in Cl(3,1) is a Pin representative `e1` with the twisted adjoint `v ↦ -e1 v e1` once full Clifford multiplication exists. In contrast an ordinary loop around a puncture does not reverse the base orientation and can lift to Spin. Spin-structure holonomy choices around punctures and frame twist winding are distinct but potentially coupled via a physically specified bundle map and connection. O(2) fibre phase inversion is another optional action, not a consequence of puncturing.

## Next Pareto mathematical cut
1. Define a continuous centre-avoiding three-strand detour construction with exact positive pairwise clearance and mirror + C3 equivariance; classify its braid monodromy and winding choices.
2. Build a genuinely nonvanishing continuous transverse normal along the 3D trajectories and prove the Pin lift commutes with frame transport, preserving independent C3, C2 and Z data.
3. Use existing pants/sheaf gluing and SL2 punctured lattice only when their actual carrier and transition types match.
4. Compare candidate circle bundle transport with KK connection through a paid bundle map, not a symmetry coincidence.

## Acceptance
```sh
python3 scripts/check_c3_punctured_sheet_pin_winding.py
```
New script is source-written and committed; no checkout CI/kernel run claimed. Its finite identities are exact, while the polygon winding computation uses floating atan2 as a regression witness and must not be confused with a formal integer-valued homotopy theorem.
