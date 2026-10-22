# T3/T6/T9/T18/T27, pants gluing and continuous theta: six-step mirrored braid

## Exact new result: 12 = 6 with reflection, NOT necessarily negative scalar
For the user trajectory:
```
t=0..5: TL TM MM BM BR MR
t=6..11: TR TM MM BM BL ML
```
the precise identity is `orbit(t+6)=mirror(orbit(t))`; `mirror` exchanges left/right columns and fixes the middle column. It is an orientation-reversing involution of the ambient 2D grid; after twelve steps the original grid position returns. Module `C3NineSiteSixStepMirrorExact` proves both equalities by cases. **Do not mistake grid reflection for negative of both coordinates**; for example TL reflects to TR, not BR.

For the phase-shifted triple `X(t)=(orbit(t),orbit(t+4),orbit(t+8))`, reflection commutes with the shift and hence `X(t+6)=mirror³(X(t))`. The C3 time-shift acts on selected strand labels; the mirror Z2 acts on coordinates, and in this particular finite model the two commute. Abstractly `C3×C2 ≅ C6` for the index action, but not an automatic spinorial `SU2→SO3` lift nor a Möbius strip theorem.

## Existing repo owners (verified from files)
- `DASHI/Topology/TernaryCylinderPantsGeometryExact.agda`: ternary tree/cylinder refinement and 1→3 combinatorial pants; explicit warning that this is not an identification with a smooth connected pants surface or a TQFT.
- `DASHI/Reasoning/WavePantsBundleGluingAdapterExact.agda`: exact interface matching and zero/nonzero transport defect; arbitrary BundleSheaf family gluing and exact restriction remain unpaid.
- `DASHI/Moonshine/JInvariant369CodecPantsFrameBidiExact.agda`: compact 27 code's frame trit equals the third pants/refinement slot **for this renderer consumer**; not physical frame angle.
- `DASHI/Geometry/TwistedCycleOrientationCover.agda`: finite non-orientability holonomy and no compatible global orientation; not a smooth Möbius surface.
- PR #1133 native T3→T9→T18→graph-T27 with explicit policy and residual (on its sibling branch); must preserve policy provenance on integration.
- `DASHI/Foundations/Base369Ternary27HypervoxelFabricGeometryExact.agda`: three ternary axes = 27 sites, three such voxels = 3^9 possible fine states.
- `DASHI/Foundations/Base369MobiusTransport.agda`: +3 mod 6 flips orientation polarity while preserving triadic phase; a distinct action from the new +6 mod 12 spatial reflection, though they have compatible involution abstractly.

## Recover full continuous theta — exact information requirements
A local SO2 frame is a circle-valued phase `e^{i theta(t)}`, but full turns require the **unwrapped lift** `Theta(t)∈R` via the universal covering map `R→S1`. Given a *continuous* observed phase history and an initial real-angle lift, path lifting determines Theta uniquely; sparse snapshots cannot generally determine an arbitrary winding number without an angular-rate/bandwidth bound. A 27-point finite code cannot record unbounded winding injectively.

For a 3D ribbon centreline gamma(s) carry a unit transverse normal n(s), with n·gamma'=0, alongside chosen reference normal and a compatible transport rule (Bishop/parallel frame or gauge connection). For a periodic closed ribbon, an integer self-framing/winding is defined relative to a compatible reference; a frame angle at only one or both ends does not suffice to determine it.

Affine coordinates, anisotropic tensor metrics, sparse codecs and quaternion rotations are potential **implementations**, not replacement proofs:
- a 3D SO3 frame uses quaternion q∈SU2 up to sign, and continuous q history can preserve spin lift;
- reflections require an extra O3/Pin parity, not only unit quaternions;
- bundle connection and holonomy govern parallel transport;
- pants/gluing interfaces need orientation, frame/phase transition functions and cocycle compatibility in addition to position matching.

`C3ContinuousFramingObservationBoundaryExact` now declares a typed continuous angular lift, framing and reconstruction obligations, a reflection frame lift interface, and exhibits two differently twisted states with the same observed endpoint. These are partly inhabited no-go lemmas and partly *explicit required fields*, not a fully constructed continuous-real Fréchet frame theorem.

## Next integration max-cut
1. Add actual analytic S1 phase and continuous path lifting, prove uniqueness given an initial lift. Bridge `theta→circle` with explicit regularity, not finite enumerations alone.
2. Lift six-step mirror into a **specific** SO2/O2 or SO3/Pin frame representation, then prove compatibility with phase-triple C3 transport. Compare Möbius w1 sign separately from integer framed twist.
3. Extend pants boundary gluing to include normals, unwrapped phase/gluing integer, and orientation sign, with exact restriction-back theorem under explicit compatibility hypotheses.
4. Connect to native graph T27 from PR #1133 without collapsing hidden policy data or assuming its third trit is a geometric frame angle.
5. Link to physical three-body orbit/KK gauge only through an actual dynamical/connection producer with typed same-object evidence.

## Certification
```sh
agda -i . -i /path/to/agda-stdlib DASHI/Foundations/C3NineSiteSixStepMirrorExact.agda
agda -i . -i /path/to/agda-stdlib DASHI/Foundations/C3ContinuousFramingObservationBoundaryExact.agda
```
Not run on the GitHub commit. No new kernel-certified proof claimed.
