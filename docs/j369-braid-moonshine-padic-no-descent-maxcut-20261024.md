# MAX-CUT: 369 braided Moonshine modular information across all ternary levels

## Scope and prior art
Keep exact previous owners: DASHI/Biology/TriadicBraidDialecticExact.agda (3-strand endpoint/Yang-Baxter and crossing history); DASHI/Moonshine/JInvariantOrderThreeSeamModularWordExact.agda (signed SSP FRACTRAN T and positive-L shears); DASHI/Moonshine/JInvariant369ModularLevelCuspObserversExact.agda, JInvariant369PrincipalLevelTowerExact.agda, JInvariant369JointPhaseLevelBundleExact.agda and JInvariant369LevelNonDescentThroughJExact.agda (3/9/27 congruence levels and j information loss); DASHI/Biology/MoonshineOrbifoldModularSectorActionExact.agda (finite four-sector orbifold S/T); DASHI/Moonshine/TwistedModuleModularity.agda, MonsterGradedVOABridgeExact.agda (V-natural VOA and analytic modularity requires explicit producers); and the existing punctured eight-point owner OggSSPP2BalancedTernaryPuncturedPlaneExact.agda. Relevant historical PRs #208, #433, #437, #1029, #1162, #1179.

## Results now implemented
1. JInvariant369BraidModularGeneratorWeldExact.agda: B3 Artin second generator equals inverse of the old *positive* signed SSP lower shear, not the lower shear itself; exact braid relation and central -I, and same native integral SL2Z matrix for the recorded word M=(T^-1 U)^3=[[13,-8],[-8,5]].
2. JInvariant369BraidOrbifoldSectorKernelExact.agda: uses the ACTUAL preexisting Z2 Moonshine twisted-sector action. Three strand roles map equivariantly to three nontrivial sector labels for both generators; the recorded pure braid is identity on all four sector labels.
3. JInvariant369PuncturedSheetModularBraidActionExact.agda: SAME existing eight-point finite punctured sheet; M modulo 3 acts in two 4-cycles, square antipodal, fourth identity and no noncentral fixed point.
4. JInvariant369OrbifoldToPunctureNoDescentExact.agda: **impossibility theorem**. If a coarse-sector decoder to eight-point punctured states respected the recorded pure braid, coarse identity would imply an M-fixed punctured point. None exists. Thus no equivariant coarse-sector -> noncentral ternary decoder can exist, even without assuming surjectivity or injectivity.
5. JInvariant369BraidModularTernaryTowerExact.agda: for all depths n, implements the SAME braid word on two native balanced-ternary residue coordinates with the existing carry adder, digitwise negation and reduction; proves the 3^(n+1)->3^n square commutes by genuine existing reduce-addResidue and an independently proven reduceNegate identity. This is not a replacement modular curve or a C3-counting metaphor.

## Quantitative 3-adic monodromy theorem
M mod2=I, while mod 3^k has order 4 for k=1, and 4*3^(k-2) for every k>=2. The integer M^4 is [[75025,-46368],[-46368,28657]]=I+9B with B=[[8336,-5152],[-5152,3184]], B mod3 invertible (det 1 mod3).
For any integer matrix X=I+3^s C with s>=1 and C not zero modulo3, the binomial identity X^3=I+3^(s+1)(C+3^s C^2+3^(2s-1) C^3) shows that cubing increases the entrywise minimum 3-adic valuation by exactly one. Raising to an exponent coprime to 3 preserves this valuation. Since M mod9 has order 4 and M^4 has valuation exactly two, the displayed order formula follows for all k (not just twelve tested levels). Projectivising by central -I halves the order: 2 for k=1,2, and 2*3^(k-2) for k>=2.
Executable check scripts/check_369_braid_padic_order_lifting.py tests the closed form up to k=12; independent local exact arithmetic verified all those cases.

## The stronger level 3 -> 27 no-section theorem
Every nonzero v in F3^2 satisfies M^4 v=v. A would-be M-equivariant section s into (Z/27)^2 would therefore require M^4 s(v)=s(v). But M^4-I=9B and B mod3 is invertible, so a fixed point modulo27 must reduce to 0 in F3^2. Contradiction. No such section exists even on the eight nonzero points. Exhaustive integer proof script scripts/check_369_level27_no_equivariant_section.py checks the 729 level-27 vectors, exact 81 fixed vectors, and all 8 x 81 noncentral lifts.

## What this does and does not establish
The fine 369 principal-level tower genuinely carries modular monodromy invisible to the coarse mod2 orbifold label action. The *finite* punctured plane F3² minus zero is not the analytic punctured real plane; prior continuous C3 trajectories pass through the origin and have not yet acquired an origin-winding number. Nor does a modular action on four Z2 sector LABELS construct the full twisted Monster VOA modules, modular S/T multipliers, or holographic AdS3 gravitational Hilbert space. The internal KK circle of our Ricci-flat pp-wave is likewise distinct without a geometric connection-preserving map.

## Pareto-critical next cuts
(a) Kernel-check the five new Agda source modules against the exact current head; source-written is not kernel-certified.
(b) Use existing TwistedModuleModularity and actual constructed VOA representation to lift B3 generators from sector-label permutations to module/traces with projective modular multipliers and an invariant/stress operator, and calculate the action of central -I.
(c) Decide whether the physical 3D braided paths have the recorded B3 word via full continuous framed isotopy, not just a sampled crossing projection.
(d) Embed into a specific AdS3 boundary theory with Brown-Henneaux c=24 and a KK reduction/compactification that preserves equations of motion and boundary observables; existing 5D Ricci-flat pp-wave need not admit this reduction.
(e) dashiQ falsifiers: compare modular-trace (coarse), twisted trace / central multiplier, full level27 congruence and frame holonomy observables on the *same physical source*.

## Local acceptance
python3 scripts/check_369_braid_modular_prior_art_weld.py
python3 scripts/check_369_braid_padic_order_lifting.py
python3 scripts/check_369_level27_no_equivariant_section.py
agda -i . -i /path/to/agda-stdlib DASHI/Moonshine/JInvariant369BraidModularTernaryTowerExact.agda
agda -i . -i /path/to/agda-stdlib DASHI/Moonshine/JInvariant369OrbifoldToPunctureNoDescentExact.agda

Verification boundary: the exact modular arithmetic was independently executed in the assistant's local container for the modular orders, valuations and 81 fixed-point classification. The latest committed new Python scripts and Agda modules have not received an exact-head checkout/Agda-kernel receipt.
## 2026-10-24 testable observability update
The fine ternary/3-adic non-descent theorems do not themselves show real Monster VOA states measure the pure braid. See `docs/monster369-physical-braid-defect-observable-maxcut-20261024.md` and the new `Monster369TwistedTraceObservableCutExact.agda`. Source-backed 2A/2B character q-series are positive controls. For order27 Monster 27A/B, the braid maps (g,1)->(g^13,g^19) and their ninth powers give the existing 3B lane, but actual twisted-character comparison is open. A standard selected braided Ising anyon rep maps the particular braid word to -I, yielding a negative control for isolated probability observables. A separate 3A/Potts W-defect carries the published golden-ratio coefficient, not an identification of 3A with 3B. Require actual VOA trace and projective multiplier, controlled boundary cycle marking and a bulk defect/Wilson operator.

## 2026-10-24 canonical 27-geometric correction
**Default DASHI 27 = 3×3×3 balanced-ternary spatial cube**, with literal x,y,z coordinates, nearest-neighbour grid adjacency, and six faces; see `DASHI/Foundations/Base369Ternary27HypervoxelFabricGeometryExact.agda` and `docs/369-27-cube-geometry-modular-carrier-disambiguation-20261024.md`. A principal-level residue Z/27 is a different 27-element *cyclic* object, while a Monster class 27A/27B denotes an element of *order 27*, not a 27-position cube. Twisted sector exponent pairs or two independent residues mod27 have 729 labels, not 27 cube positions. The new `JInvariant369Cube27CuspCodecNonIsometryExact.agda` gives a lossless finite-digit set chart but proves corner wrap is not a cube edge; a stronger bipartite/odd-cycle no-go is checked by `scripts/check_369_cube27_geometry_vs_modular_charge.py`. `JInvariant369Cube27ModularSliceActionExact.agda` maps the recorded modular action onto the ACTUAL cube, chosen z sheets, with three fixed centres and six four-cycles; this is not a graph isometry or geometric physical rotation. The earlier AdS3/Monster order-27 calculations continue to concern the separate cyclic-power carrier and require a physical bundle/operator identification before speaking about cube physics.
