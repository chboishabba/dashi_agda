# Stage-13 marked symmetry versus JMD cube-root-three diagrams

## Source status
Branch: chatgpt/cuberoot3-691-maxcut
New owners:
- DASHI/Foundations/TrialecticStageThirteenMarkedC3CubieExact.agda
- DASHI/Foundations/TrialecticStageThirteenMarkedOrbitAdapterExact.agda
Inherited:
- Foundations/JPlusOneScaleBridge.agda
- Foundations/StageAtlasZeroToTwelve.agda
- Moonshine/Base369Ternary27SpectralSymmetryIrrepBridgeExact.agda
- Moonshine/JInvariant369TenRankSeventeenHyperformalismExact.agda

## New inhabited finite facts (source-written, kernel not run)
* Arithmetic: 10j + 3j = 13 with j=1.
* The 27-cell carrier has S3 coordinate permutation structure, inherited
  from the spectral-geometry owner.
* The marked one-hot triple provides an injective C3-equivariant map into
  one 3-cycle orbit of the 27 cubies.
* The positive (111) cubie is C3-fixed and not in this orbit.
* Therefore the order-three action has both moving and fixed points; it is
  not globally a free torsor.
* This is NOT the promotion of numeric rank 13 into philosophical semantic
  Stage 13, and not a proof of a Monster representation.

## Re-assessment of JMD image claims
A. Cube: cbrt(3) gives a cube of volume 3. It does not uniquely select
   a discrete cubie of a 3x3x3 tessellation. Such selection requires a
   coordinate/quantization map. The geometric action, if coordinate
   equivariant, can be transported independently of its physical units.
B. Binary/ternary: same algebraic real has distinct positional words.
   Existing Base369BinaryTernaryRefinement proves the 2^a3^b index
   diamond; it does not yet provide a certified common real-interval
   observation for this specific algebraic number.
C. Digit blocks: 44224=64*691 is exact; no theorem identifies decimal
   factorization with the 27-cubie orbit or with stage rank 13.
D. Sturmian: irrational alpha=cbrt(3)-1 gives mechanical Sturmian word.
   rational 230/691 gives periodic mechanical/Christoffel-type coding,
   not an irrational Sturmian word.
E. Cubic field: F_691[X]/(X^3-3), Frobenius of order 3. This is an
   independent C3 action with its own fixed-field structure. The
   one-hot cubie orbit and this field can both model a C3 torsor,
   but no canonical field-to-cubie physical interpretation follows.
F. 691 Eisenstein congruence: tau(n)=sigma_11(n) modulo 691 is a distinct,
   classical modular-form theorem. Existing EisensteinDiscriminantWeight12Exact
   and RamanujanTauHecke23Exact are promising owners for an all-n proof.
G. Neither 13=111_balanced nor 691 mod 3 alone upgrades any of the
   preceding correspondences into a universal physical theory.

## Honest next boundaries
1. Compile exact-head Agda modules and attach kernel receipts.
2. Formalize the actual (not identity) Stage10 marked extension / Stage12
   relation object -> Stage13 action; current positive theorem covers marked
   one-hot slots and the existing voxel, not the full semantic stage process.
3. Prove an explicitly selected algebraic-real-to-cubie quantizer, or
   demonstrate non-canonicity under natural symmetry requirements.
4. Prove any chosen Frobenius / cubie orbit map with observation laws.
5. Reuse normalized weight-12 Eisenstein/Delta series to prove the
   all-n Ramanujan mod-691 congruence in a kernel.
