module DASHI.Codec.DNACompressiveMacros where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Codec.DNAFirstFormalism using
  ( Base; A; C; G; T
  ; Axis3; axis0; axis1; axis2
  ; Line3; Voxel9; Cube27
  )
open import DASHI.Codec.DNACarrierFibre using
  ( ChemicalPair; ComplementPhase
  ; chemicalPair; complementPhase
  ; primaryPhase; mirrorPhase
  )

infixr 6 _xor_
_xor_ : Bool → Bool → Bool
false xor b = b
true xor false = true
true xor true = false

phaseBit : ComplementPhase → Bool
phaseBit primaryPhase = false
phaseBit mirrorPhase = true

------------------------------------------------------------------------
-- Genuine quotient summaries: source blocks are not retained.

record LineMacro : Set where
  constructor lineMacro
  field
    lineChem0 : ChemicalPair
    lineChem1 : ChemicalPair
    lineChem2 : ChemicalPair
    linePhaseParity : Bool
open LineMacro public

summarizeLine : Line3 → LineMacro
summarizeLine line =
  lineMacro
    (chemicalPair (line axis0))
    (chemicalPair (line axis1))
    (chemicalPair (line axis2))
    (phaseBit (complementPhase (line axis0)) xor
     (phaseBit (complementPhase (line axis1)) xor
      phaseBit (complementPhase (line axis2))))

record VoxelMacro : Set where
  constructor voxelMacro
  field
    voxelChemistry : Axis3 → Axis3 → ChemicalPair
    voxelPhaseParity : Bool
open VoxelMacro public

voxelParity : Voxel9 → Bool
voxelParity v =
  phaseBit (complementPhase (v axis0 axis0)) xor
  (phaseBit (complementPhase (v axis0 axis1)) xor
  (phaseBit (complementPhase (v axis0 axis2)) xor
  (phaseBit (complementPhase (v axis1 axis0)) xor
  (phaseBit (complementPhase (v axis1 axis1)) xor
  (phaseBit (complementPhase (v axis1 axis2)) xor
  (phaseBit (complementPhase (v axis2 axis0)) xor
  (phaseBit (complementPhase (v axis2 axis1)) xor
   phaseBit (complementPhase (v axis2 axis2)))))))))

summarizeVoxel : Voxel9 → VoxelMacro
summarizeVoxel v =
  voxelMacro
    (λ i j → chemicalPair (v i j))
    (voxelParity v)

record CubeMacro : Set where
  constructor cubeMacro
  field
    cubeChemistry : Axis3 → Axis3 → Axis3 → ChemicalPair
    cubeLayerParity : Axis3 → Bool
open CubeMacro public

layerParity : Cube27 → Axis3 → Bool
layerParity c k = voxelParity (λ i j → c i j k)

summarizeCube : Cube27 → CubeMacro
summarizeCube c =
  cubeMacro
    (λ i j k → chemicalPair (c i j k))
    (layerParity c)

------------------------------------------------------------------------
-- Explicit collision witness proving that LineMacro is genuinely compressive.

lineACA : Line3
lineACA axis0 = A
lineACA axis1 = C
lineACA axis2 = A

lineTGA : Line3
lineTGA axis0 = T
lineTGA axis1 = G
lineTGA axis2 = A

lineMacro-collision : summarizeLine lineACA ≡ summarizeLine lineTGA
lineMacro-collision = refl

data ⊥ : Set where

_≢_ : ∀ {X : Set} → X → X → Set
x ≢ y = x ≡ y → ⊥

cong : ∀ {X Y : Set} (f : X → Y) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

lineACA≢lineTGA : lineACA ≢ lineTGA
lineACA≢lineTGA eq with cong (λ line → line axis0) eq
... | ()

record CompressiveMacroReceipt : Set where
  field
    lineSummary : Line3 → LineMacro
    voxelSummary : Voxel9 → VoxelMacro
    cubeSummary : Cube27 → CubeMacro
    collisionLeft : Line3
    collisionRight : Line3
    sourcesDiffer : collisionLeft ≢ collisionRight
    summariesCollide : lineSummary collisionLeft ≡ lineSummary collisionRight

compressiveMacroReceipt : CompressiveMacroReceipt
compressiveMacroReceipt = record
  { lineSummary = summarizeLine
  ; voxelSummary = summarizeVoxel
  ; cubeSummary = summarizeCube
  ; collisionLeft = lineACA
  ; collisionRight = lineTGA
  ; sourcesDiffer = lineACA≢lineTGA
  ; summariesCollide = lineMacro-collision
  }
