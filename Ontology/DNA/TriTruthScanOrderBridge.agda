module Ontology.DNA.TriTruthScanOrderBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

open import Base369 using (TriTruth; tri-low; tri-mid; tri-high; rotateTri)
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor; layerMajor)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

lineMajor≢layerMajor : lineMajor ≢ layerMajor
lineMajor≢layerMajor ()

nextScan : ScanOrder → ScanOrder
nextScan lineMajor  = layerMajor
nextScan layerMajor = lineMajor

ι-tri-scan : TriTruth → ScanOrder
ι-tri-scan tri-low  = lineMajor
ι-tri-scan tri-mid  = layerMajor
ι-tri-scan tri-high = lineMajor

triToCurrentScanEquivarianceImpossible :
  ((t : TriTruth) → ι-tri-scan (rotateTri t) ≡ nextScan (ι-tri-scan t)) →
  ⊥
triToCurrentScanEquivarianceImpossible equiv =
  lineMajor≢layerMajor (equiv tri-high)

data TriScanOrder : Set where
  triLine triLayer triReturn : TriScanOrder

nextTriScan : TriScanOrder → TriScanOrder
nextTriScan triLine   = triLayer
nextTriScan triLayer  = triReturn
nextTriScan triReturn = triLine

triScanOf : TriTruth → TriScanOrder
triScanOf tri-low  = triLine
triScanOf tri-mid  = triLayer
triScanOf tri-high = triReturn

triScanEquivariant :
  (t : TriTruth) →
  triScanOf (rotateTri t) ≡ nextTriScan (triScanOf t)
triScanEquivariant tri-low  = refl
triScanEquivariant tri-mid  = refl
triScanEquivariant tri-high = refl

record TriTruthScanOrderBridge : Set where
  constructor triTruthScanOrderBridge
  field
    currentMap : TriTruth → ScanOrder
    currentTwoStateObstruction :
      ((t : TriTruth) → currentMap (rotateTri t) ≡ nextScan (currentMap t)) →
      ⊥
    refinedMap : TriTruth → TriScanOrder
    refinedEquivariance :
      (t : TriTruth) →
      refinedMap (rotateTri t) ≡ nextTriScan (refinedMap t)

triTruthScanOrderBridgeSurface : TriTruthScanOrderBridge
triTruthScanOrderBridgeSurface =
  triTruthScanOrderBridge
    ι-tri-scan
    triToCurrentScanEquivarianceImpossible
    triScanOf
    triScanEquivariant
