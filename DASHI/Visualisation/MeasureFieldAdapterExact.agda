module DASHI.Visualisation.MeasureFieldAdapterExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Finite source -> measure -> field -> slice -> image bridge.

data SourceKind : Set where
  timelineSource : SourceKind
  citationGraphSource : SourceKind
  eventTableSource : SourceKind
  entityNetworkSource : SourceKind

record SourceObject : Set where
  constructor sourceObject
  field
    sourceKind : SourceKind
    firstMass : Nat
    secondMass : Nat

open SourceObject public

record FiniteMeasure : Set where
  constructor finiteMeasure
  field
    atomLeft : Nat
    atomRight : Nat

open FiniteMeasure public

extractMeasure : SourceObject → FiniteMeasure
extractMeasure source =
  finiteMeasure
    (firstMass source)
    (secondMass source)

totalMeasureMass : FiniteMeasure → Nat
totalMeasureMass measure =
  atomLeft measure + atomRight measure

record Field2 : Set where
  constructor field2
  field
    fieldLeft : Nat
    fieldRight : Nat

open Field2 public

------------------------------------------------------------------------
-- A denominator-two smoothing kernel.  Each atom sends one scaled unit to
-- each output cell, so total field mass is twice source mass.

convolveScaled : FiniteMeasure → Field2
convolveScaled measure =
  field2
    (atomLeft measure + atomRight measure)
    (atomLeft measure + atomRight measure)

totalFieldMass : Field2 → Nat
totalFieldMass field =
  fieldLeft field + fieldRight field

canonicalSource : SourceObject
canonicalSource =
  sourceObject citationGraphSource 2 3

canonicalMeasureMass :
  totalMeasureMass (extractMeasure canonicalSource) ≡ 5
canonicalMeasureMass = refl

scaledConvolutionPreservesMass :
  totalFieldMass
    (convolveScaled (extractMeasure canonicalSource))
  ≡
  2 * totalMeasureMass (extractMeasure canonicalSource)
scaledConvolutionPreservesMass = refl

------------------------------------------------------------------------
-- Embedding isometry witness: swapping the two latent locations swaps the
-- field, while the isotropic smoothing rule is equivariant.

swapMeasure : FiniteMeasure → FiniteMeasure
swapMeasure measure =
  finiteMeasure
    (atomRight measure)
    (atomLeft measure)

swapField : Field2 → Field2
swapField field =
  field2
    (fieldRight field)
    (fieldLeft field)

isotropicSwapEquivariance :
  (measure : FiniteMeasure) →
  convolveScaled (swapMeasure measure)
  ≡
  swapField (convolveScaled measure)
isotropicSwapEquivariance (finiteMeasure left right) =
  cong (λ mass → field2 mass mass) (+-comm right left)

------------------------------------------------------------------------
-- Slice and colour projections can erase distinctions.

data SliceChoice : Set where
  leftCellSlice : SliceChoice
  rightCellSlice : SliceChoice

restrictField : SliceChoice → Field2 → Nat
restrictField leftCellSlice field = fieldLeft field
restrictField rightCellSlice field = fieldRight field

data ImageTone : Set where
  darkTone : ImageTone
  brightTone : ImageTone

coarseColour : Nat → ImageTone
coarseColour zero = darkTone
coarseColour (suc _) = brightTone

sourceA : SourceObject
sourceA = sourceObject timelineSource 1 0

sourceB : SourceObject
sourceB = sourceObject eventTableSource 0 1

sourcesRemainDistinct : sourceA ≡ sourceB → ⊥
sourcesRemainDistinct ()

differentSourcesSameCoarseImage :
  coarseColour
    (restrictField leftCellSlice
      (convolveScaled (extractMeasure sourceA)))
  ≡
  coarseColour
    (restrictField leftCellSlice
      (convolveScaled (extractMeasure sourceB)))
differentSourcesSameCoarseImage = refl

record AdapterStageBoundary : Set where
  constructor adapterStageBoundary
  field
    sourceRelationIsAdapterGeometry : Bool
    sourceRelationIsAdapterGeometryIsFalse :
      sourceRelationIsAdapterGeometry ≡ false

    layoutGeometryIsIntrinsicGraphGeometry : Bool
    layoutGeometryIsIntrinsicGraphGeometryIsFalse :
      layoutGeometryIsIntrinsicGraphGeometry ≡ false

    fieldImageIsLosslessReplacementForSource : Bool
    fieldImageIsLosslessReplacementForSourceIsFalse :
      fieldImageIsLosslessReplacementForSource ≡ false

    smoothingArtefactIsSourceEvidence : Bool
    smoothingArtefactIsSourceEvidenceIsFalse :
      smoothingArtefactIsSourceEvidence ≡ false

open AdapterStageBoundary public

canonicalAdapterStageBoundary : AdapterStageBoundary
canonicalAdapterStageBoundary =
  adapterStageBoundary
    false refl
    false refl
    false refl
    false refl
