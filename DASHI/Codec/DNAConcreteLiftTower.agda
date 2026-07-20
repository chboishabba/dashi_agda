module DASHI.Codec.DNAConcreteLiftTower where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Codec.DNAFirstFormalism using
  ( Base; complement
  ; Axis3
  ; Line3; Voxel9; Cube27
  ; LiftTower
  )
open import DASHI.Codec.DNACarrierFibre using
  ( ChemicalPair; chemicalPair; chemicalPair-complement-invariant )

------------------------------------------------------------------------
-- Geometry-aware complement actions.

complementLine : Line3 → Line3
complementLine line i = complement (line i)

complementVoxel : Voxel9 → Voxel9
complementVoxel voxel i j = complement (voxel i j)

complementCube : Cube27 → Cube27
complementCube cube i j k = complement (cube i j k)

------------------------------------------------------------------------
-- Concrete macro-symbols retain an exact source block and its chemistry
-- quotient. This is an identity-recognisable baseline: it proves the lift
-- plumbing and equivariance before any lossy/eigenstate quotient is selected.

record LineSymbol : Set where
  constructor lineSymbol
  field
    lineSource : Line3
    lineChemistry : Axis3 → ChemicalPair

record VoxelSymbol : Set where
  constructor voxelSymbol
  field
    voxelSource : Voxel9
    voxelChemistry : Axis3 → Axis3 → ChemicalPair

record CubeSymbol : Set where
  constructor cubeSymbol
  field
    cubeSource : Cube27
    cubeChemistry : Axis3 → Axis3 → Axis3 → ChemicalPair

open LineSymbol public
open VoxelSymbol public
open CubeSymbol public

liftLine : Line3 → LineSymbol
liftLine line = lineSymbol line (λ i → chemicalPair (line i))

liftVoxel : Voxel9 → VoxelSymbol
liftVoxel voxel = voxelSymbol voxel (λ i j → chemicalPair (voxel i j))

liftCube : Cube27 → CubeSymbol
liftCube cube = cubeSymbol cube (λ i j k → chemicalPair (cube i j k))

projectLine : LineSymbol → Line3
projectLine = lineSource

projectVoxel : VoxelSymbol → Voxel9
projectVoxel = voxelSource

projectCube : CubeSymbol → Cube27
projectCube = cubeSource

project-lift-line : ∀ line → projectLine (liftLine line) ≡ line
project-lift-line line = refl

project-lift-voxel : ∀ voxel → projectVoxel (liftVoxel voxel) ≡ voxel
project-lift-voxel voxel = refl

project-lift-cube : ∀ cube → projectCube (liftCube cube) ≡ cube
project-lift-cube cube = refl

line-chemistry-correct :
  ∀ line i → lineChemistry (liftLine line) i ≡ chemicalPair (line i)
line-chemistry-correct line i = refl

voxel-chemistry-correct :
  ∀ voxel i j → voxelChemistry (liftVoxel voxel) i j ≡ chemicalPair (voxel i j)
voxel-chemistry-correct voxel i j = refl

cube-chemistry-correct :
  ∀ cube i j k → cubeChemistry (liftCube cube) i j k ≡ chemicalPair (cube i j k)
cube-chemistry-correct cube i j k = refl

------------------------------------------------------------------------
-- Complement leaves the chemistry quotient invariant at every scale.

line-complement-chemistry :
  ∀ line i →
  lineChemistry (liftLine (complementLine line)) i ≡
  lineChemistry (liftLine line) i
line-complement-chemistry line i = chemicalPair-complement-invariant (line i)

voxel-complement-chemistry :
  ∀ voxel i j →
  voxelChemistry (liftVoxel (complementVoxel voxel)) i j ≡
  voxelChemistry (liftVoxel voxel) i j
voxel-complement-chemistry voxel i j = chemicalPair-complement-invariant (voxel i j)

cube-complement-chemistry :
  ∀ cube i j k →
  cubeChemistry (liftCube (complementCube cube)) i j k ≡
  cubeChemistry (liftCube cube) i j k
cube-complement-chemistry cube i j k = chemicalPair-complement-invariant (cube i j k)

------------------------------------------------------------------------
-- Concrete baseline LiftTower instance. Recognisability is constructive via
-- project-after-lift; macro adjacency is intentionally permissive here and is
-- refined by the state-machine boundary receipts in concrete codec modules.

concreteLiftTower : LiftTower
concreteLiftTower = record
  { LineSymbol = LineSymbol
  ; VoxelSymbol = VoxelSymbol
  ; CubeSymbol = CubeSymbol
  ; liftLine = liftLine
  ; liftVoxel = liftVoxel
  ; liftCube = liftCube
  ; lineRecognisable = ⊤
  ; voxelRecognisable = ⊤
  ; cubeRecognisable = ⊤
  ; lineMacroAdmissible = λ x y → ⊤
  ; voxelMacroAdmissible = λ x y → ⊤
  ; cubeMacroAdmissible = λ x y → ⊤
  }

lineRecognisableWitness : LiftTower.lineRecognisable concreteLiftTower
lineRecognisableWitness = tt

voxelRecognisableWitness : LiftTower.voxelRecognisable concreteLiftTower
voxelRecognisableWitness = tt

cubeRecognisableWitness : LiftTower.cubeRecognisable concreteLiftTower
cubeRecognisableWitness = tt
