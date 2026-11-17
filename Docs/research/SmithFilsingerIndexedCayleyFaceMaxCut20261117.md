# Smith/Filsinger F13/F10 — original indexed-face Cayley and mesh-membership cut
**17 November 2026 · PR #1524 · mathematical source identification, not physical source qualification**

## Reused original owners

- `SmithFilsingerIndexedFaceIncidenceExact.DirectedFace`, `IndexedMesh.faces`, and `sameID`: canonical source/target, incidence and exact face IDs
- `SmithFilsingerLocalCayleyZeroWeldExact.CertifiedCayley` / `DistinctCayleyEdge`: actual 2×2 rational Cayley source coefficients and non-self-loop constraint
- `SmithFilsingerLocalCayleyMidpointExact.CertifiedHalfStep` and the two exact implicit midpoint equations
- `SmithFilsingerLocalCausalADEReachExact.noSignalOutsideInterleavedSourceCone`: zero-preserving stage and source-injection support
- the original source-owned heterogeneous Maxwell/Lorentz `edge_updates` and `cayley_edge_step` Python implementation

## F13 new typed source-indexed Agda weld

`DASHI/Physics/Motors/SmithFilsingerIndexedCayleyFaceWeldExact.agda` identifies the two stage coordinates **exactly** with `DirectedFace.source` and `.target` of one selected original face and requires a proof they are distinct. It *constructs* `Cayley.DistinctCayleyEdge` from that face and the same pre-existing `CertifiedHalfStep`, without a new numerical Green solver.

It authors:
- `indexedSourceIDExact`, `indexedTargetIDExact`: the actual frame operator uses precisely the original face source/target IDs
- `indexedGuardedSamePrimitive`: its zero-preserving dynamic cone stage uses the identical underlying original coefficient-defined primitive
- `indexedFaceFirstMidpoint`, `indexedFaceSecondMidpoint`: both original Cayley implicit midpoint equations apply to that selected original face
- `indexedFaceWithSource`, `indexedFaceSourceCone`: a tagged natural/controller current is a separately introduced source root, not an unexplained passive source term

To avoid confusing a merely constructed face with a member of the original finite-volume mesh, the new `FaceMember` inductive carrier requires actual list membership; `MeshSelectedCayleyFace.selectedReallyOccurs` is a constructive receipt against **the same** `IndexedMesh.faces`. The two `meshSelectedFaceMidpoint...` theorems consume it.

**Crucial boundary:** the original finite-volume `DirectedFace` record indexes *geometric cell* incidence, while the rational Cayley solver has *state-coordinate* indices E/H/P/V. This record selects their identical numeric IDs conditional on the user/provider supplying an actual geometric-to-state index calibration. Numeric identity and membership are not proof that a physical geometric face couples precisely those electromagnetic coordinates. The genuine field/face projection, signed normal Poynting integral, Maxwell 3D retarded dyadic, terminal return current and source-meter evidence all remain independently open. This is a typed mathematical source-identification bridge, not a physical-port weld.

## Independent exact testing

`scripts/test_smith_filsinger_indexed_cayley_face_sympy.py` runs source-owned heterogeneous Maxwell/ADE edges for n=2..5 and verifies the explicit edge-ID mapping, the same rational midpoint output and both original two-variable equations, and no mutation beyond that stage's selected endpoints. It rejects reversed source/target, coincident endpoints, wrong other-face endpoint, a one-coordinate diagonal damping edge mislabeled as a two-endpoint face, untyped source/meter overclaim, missing original mesh membership, same-ID different-face members and duplicate face IDs.

Prior tests 164 + 11 new parameterized/adversarial cases = **175/175 PASS**, executed locally with SymPy 1.14.0 and pytest 9.0.2. New test and source registered in the original consolidated Python runner, independent SymPy fail-closed gate, and Agda 2.9 pinned owner lists. This is locally verified *mathematical* parity; no PR-head CI or Agda acceptance has been claimed.

## Next highest-alpha and strict gates

- **D1:** Actually run the pinned Agda 2.9 checker on this exact commit and repair the first failure; Agda source is not yet typechecked. No postulates or explicit proof holes are introduced by the new module.
- **F13:** Prove the *same physical* geometric-cell face to E/H/P/V cochain projection with oriented normals, metric factors, actual permittivity/magnetic/curl coefficients, and source-to-terminal work. Reuse `SmithFilsingerSignedIndexedFaceFluxExact` and `SmithFilsingerSpaceTimePoyntingTelescopeExact` rather than manufacturing positive source work.
- **F15:** Independently metered/replenished original Sun–Earth source under receiver backaction and fully restored environmental/receiver/material/controller cycles, including all losses and uncertainty bounds.
- A finite Cayley graph dependency bound is not the physical Maxwell light cone, nor a signed Poynting meter.

Original Smith/Filsinger attribution retained; no ESD edits.
