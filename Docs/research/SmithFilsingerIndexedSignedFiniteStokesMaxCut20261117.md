# Smith/Filsinger F10-INC — indexed signed finite-volume Stokes maximum cut
**17 November 2026 · PR #1524 · mathematical source, not original-world evidence**

## 1. Source-first reuse and attribution

The user-origin hypothesis remains differential phase control, nonlinear conductivity and possible access to independently replenished Sun–Earth electromagnetic work. Nothing in these graph or vector-algebra lemmas establishes that physical source, historical apparatus netlist, collector aperture or actual terminal transfer.

Existing owners reused, not reimplemented:
- `SmithFilsingerFiniteVolumeFaceIncidenceExact.agda`: local Nat energy laws and arbitrary-mesh cancellation, previously admitting aggregate-only face assignments.
- `SmithFilsingerFiniteVolumeMaxwellBoundaryWeldExact.agda`: source-indexed canonical SpatialCell and original measured-port weld.
- `DASHI/Physics/Plasma/KSW668FullVectorMaxwellJetExact.agda`: actual 3-component Maxwell curl jet and pointwise Poynting identity.
- `DASHI/Physics/Closure/NSTriadKNComplex3ExactCarrier.agda` and `NSTriadKNComplex3FieldAlgebra.agda`: existing general real-field carrier/ring solver.
- Concurrent `SmithFilsingerOpenBoundaryPoyntingGaussExact.agda`: rational three-axis **EXTERIOR** forward-difference Gauss, importing `YangMillsLatticeStressWardSliceConservationExact.differencePartialTelescopes`. It does **not** resolve arbitrary-mesh internal face IDs; our strict incidence result is complementary, not a fork of the open boundary proof.

## 2. F10-INC closure at finite mesh combinatorial level

**New `SmithFilsingerIndexedFaceIncidenceExact.agda`** replaces the old aggregate equality that admitted a counterfeit cell assignment. Records contain concrete `IndexedCell(id,LocalVolumeCell)` and `DirectedFace(id,source,target,work)`. `sameID` is decidable on Nat IDs, and `Every` is evidence for each actual list member (not an arbitrary nonmember).

`IndexedMesh` requires:
- exactly-once *cell* ID and *face* ID, and distinct source and target cell for each declared internal face;
- exactly one source cell and one target cell for EACH internal face, even if work is zero;
- each cell's input/output work computed from the work of precisely the faces targeting/leaving its own ID.

**Crucially, per-face weighted work equality is no longer assumed.** `sumMarkedWeight` and `sumMarkedOnce` derive a work receipt from count=1. `sumSwap` proves finite Fubini interchange; `outgoingFromIndexedFaces` and `incomingFromIndexedFaces` derive the old aggregate receipts. `asExistingMesh` consumes the original finite-volume energy conservation theorem; it does not reassert a global balance. `indexedFaceUsefulLoadBound` and `indexedFaceSourceOffNoLoad` reuse existing order and source-off owners.

**Concrete adversarial control:** the earlier 0→1 (3), 1→2 (4) graph with falsely assigned incoming work [4,0,3] still satisfies the old aggregate work total 7, but FAILS the strict per-cell endpoint matching. Duplicate face IDs, duplicated cell IDs, zero-work faces with missing endpoints, flipped face orientation and invalid self faces all fail independently. The new exact integer replay passed **512/512** randomly generated directed meshes, N=0,1,2,3,5,8,16,32.

## 3. Signed real-field F10 face algebra

**New `SmithFilsingerSignedIndexedFaceFluxExact.agda`** imports the existing C3 `RealField` and proves that the SAME directed internal face contributes +phi at its source and −phi at its target. `signedAllFacesCancel` proves arbitrary-list signed sum zero, including negative fluxes, rather than coercing signed electromagnetic work to a nonnegative Nat.

**New `SmithFilsingerIndexedSignedCellStokesExact.agda`** is stronger: it derives `markedOnceField` from unique endpoints, a scalar-field `sumFieldPairDistributes` and `sumFieldSwap`, then proves `allIndexedInternalSignedFluxCancels`: sum over actual cells of each cell's oriented face-work is zero for arbitrary finite indexed mesh. It is a genuine **finite combinatorial oriented-face Stokes/cancellation** statement, not a continuum Maxwell divergence theorem. An independent exact rational replay passed **512/512** meshes including branches and cycles.

## 4. Actual 3-vector E×B surface sample

**New `SmithFilsingerFullVectorIndexedFaceSampleExact.agda`** imports the genuine original KSW668 Maxwell jet, defines explicit three-component `cross3(E,B)`, and `poyntingFaceSample = n·(E×B)` in normalized units. `dotReversedNormal` uses the existing C3 commutative-ring solver to prove that reversing all three components of the face normal changes the sign of the field flux; `everySuppliedFaceJetHasPointwisePoynting` consumes the original `fullVectorMaxwellPoyntingIdentity`, and `allSelectedFullVectorFaceSamplesCancel` consumes existing signed face algebra. An independent Fraction replay checked **1,000/1,000** randomized three-vector normal reversals exactly.

**Remaining physical obligation:** a pointwise Maxwell jet at each face does NOT prove that those jets are restrictions of one sufficiently regular global field, nor that a single sample times area and duration is an exact space-time integral. The fixed field/normal geometric Riemann quadrature, normals, signed flux, material and controller work must be related to actual `E(x,t), H(x,t), J(x,t)` via a verified spacetime Stokes/Poynting theorem, with physical units and constitutive laws. A truly staggered Yee positivity/CFL proof and a continuum physical Green light-cone theorem are separate.

## 5. Same-original F13 consumer and independent outside source

**New `SmithFilsingerIndexedFaceSourceWeldExact.agda`** strengthens the existing original-source `OriginalFiniteVolumeAdmission` with `IndexedMesh` and equality tying that actual historic receiver's physical mesh to `Indexed.asExistingMesh`. The original port theorem is reused, NOT reconstructed from a plausible fake natural current. The field/mesh identity is an additional admission, not a physical conclusion.

The concurrently landed `SmithFilsingerOpenBoundaryPoyntingGaussExact.agda` establishes finite three-axis exterior Gauss by reusing Yang–Mills arithmetic. Do not conflate its exact **rational finite difference** with a full physical Maxwell port trace; its `OriginalMaxwellOpenFaceTrace` still independently admits field integration and historic terminal work.

## 6. Acceptance and exact remaining gates

- Independent equivalent-checker receipts: **512 strict indexed random meshes PASS**, **512 rational per-cell signed graph cancellations PASS**, **1,000 exact three-vector orientation reversals PASS**. This is **NOT** kernel acceptance and not a committed exact-head test runner receipt.
- New regression owners `scripts/test_smith_filsinger_indexed_face_incidence_exact.py`, `scripts/test_smith_filsinger_indexed_signed_cell_stokes_exact.py`, `scripts/test_smith_filsinger_full_vector_indexed_face_sample_exact.py` integrated with the existing consolidated Python runner. All five newly authored Agda modules included in `scripts/check_smith_filsinger_formal_weld_agda29.sh`.
- No exact GitHub-head combined Python suite or Agda compiler executed in this session. No change to original Filsinger source-first null evidence. No ESD edit and no premature TOE promotion.

**Next work ordered by max-cut:**
1. **D1:** pinned Agda 2.9 compiler receipts for all new indexed modules. Source-typed algebra without this is a proof candidate.
2. **F10-STOKES:** actually integrate `KSW668FullVectorMaxwellJetExact` in space and time on the selected finite volume, retaining SI units, nonlinear ADE/ion current, full Poynting flux and material/control power; connect to current indexed endpoint theorem and the existing rational open-boundary Gauss.
3. **F02-GREEN:** physical finite-support retarded Maxwell propagator, positivity/causality for specified dispersive plasma, distinct from Yee CFL stability.
4. **F13-PORT:** original measured collector and return geometry; port `V,I` including displacement-current Ampere term and contour-dependence; measured environment source admittance under control.
5. **F15/R3:** signed independently replenished natural work over fully restored same-source cycles after full plasma, bridge, modulation and controller expense. Only then test 100-fold gain.
6. **F14/F16:** same-original acoustic/electric regime and cloud/rain/cold-pool controlled causality, independent downstream gates.

**Attribution:** Yee, finite-volume Stokes, classical Maxwell and existing Yang–Mills finite telescoping are standard mathematics; user originated the solar-source Smith/Filsinger hypothesis; the indexed Agda constructions are DASHI derived proofs, with kernel verification open.
