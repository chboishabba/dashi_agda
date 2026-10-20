# Cube-root-three / 691 / Base369 max-cut (2026-10-20)

## Existing canonical owners (reuse, do not duplicate)
- `DASHI/Foundations/Base369Ternary27HypervoxelFabricGeometryExact.agda`: 27-point ternary cube, 19683-point 9-coordinate hyperfabric.
- `DASHI/Moonshine/Base369Ternary27SpectralSymmetryIrrepBridgeExact.agda`: `rotateXYZ` with `rotateXYZOrderThree`, stabilizers and characters.
- `DASHI/Foundations/Base369CoarseFineFabricAdapterExact.agda`: exact interaction/appraisal fibre decomposition.
- `DASHI/Foundations/RepresentationChartInvariant.agda` and `RadixValuationStageBridge.agda`: representation and radix stage semantics.
- `DASHI/Unified/ThreePhaseCrossPollinationExact.agda`: free C3 torsor equivalences, **not** a free action on every 27-cube point (the cube origin is fixed).
- `DASHI/Moonshine/C3FourierConjugationExact.agda`: symbolic depth-one C3 characters.
- `DASHI/Moonshine/Monster3BMultiplicityCharacterProjectorExact.agda`: finite projector trace with actual Monster class embedding/character remaining open.

## New concrete arithmetic witness
`python3 scripts/check_cuberoot3_691_maxcut.py` checks with integer arithmetic:
- First six base-691 fractional digits of cube root of 3 are (305,410,530,36,70,523); decimal first five are 44224.
- Let p=691 and ω=3^230 mod p=437. Then ω^3=1, ω≠1.
- Because the multiplicative group F_p* is cyclic and p≡1 mod 3, 3 is not a cube mod p. Hence X³−3 is irreducible over F_p.
- In K=F_p[x]/(x³−3), Frobenius sends x to ωx, fixes F_p, has exact order 3 and fixed field F_p.
- The Python receipt checks explicit polynomial multiplication and Frobenius multiplicativity on sample vectors; it is **not** an exhaustive ring homomorphism proof. Algebraically, (a+b x+c x²)^p = a+ω b x+ω² c x² by the Frobenius binomial identity.
- For α=cuberoot(3)−1, the spectrum R(b)=floor(bα) has increments in {0,1}; test checks b=3..999. A general proof follows from 0<α<1. The Sturmian factor-complexity theorem is not proved by this script.

## Distinct actions and honest obstruction
The field extension C3 is Frobenius. The 27-point coordinate-rotation C3 has fixed points. Therefore these cannot be identified as free C3 torsors on the entire carriers. A bridge should target a marked orbit, a suitable quotient/observable, or an equivariant map with a precise witness. No Monster representation, Yang–Mills continuum statement, or physical identification follows from a common abstract C3.

## Open kernel cut
1. Transport the explicit X³−3/691 quotient field and Frobenius calculation into the existing finite-field Agda/Lean owner, with a compiler/kernel receipt.
2. Supply an explicit observation/intertwiner or a typed negative receipt relating chosen field and hypervoxel C3 actions.
3. Instantiate a real-number algebraic root and certified radix interval semantics via the existing chart interface; the executable Python computation does not inhabit that formal interface.
4. Distinguish arithmetic decimal-prefix coincidences from representations with invariant-preserving maps.

Status: one executable Python arithmetic fixture committed; no Agda/Lean kernel claims made.
