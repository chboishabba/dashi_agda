module DASHI.Physics.YangMills.QITMassGapLane where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Geometry.Gauge.SUNPrimitives

record QITMassGapLane : Set₁ where
  field
    localAlgebrasDefined : Bool
    entropyConcept : Bool
    infoDecayExponential : Bool
    splitPropertyHolds : Bool
    areaLawHolds : Bool
    bridgeToMassGap : Bool
    localAlgebrasDefinedIsFalse : localAlgebrasDefined ≡ false
    entropyConceptIsFalse : entropyConcept ≡ false
    infoDecayExponentialIsFalse : infoDecayExponential ≡ false
    splitPropertyHoldsIsFalse : splitPropertyHolds ≡ false
    areaLawHoldsIsFalse : areaLawHolds ≡ false
    bridgeToMassGapIsFalse : bridgeToMassGap ≡ false
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalQITMassGapLane : QITMassGapLane
canonicalQITMassGapLane = record
  { localAlgebrasDefined = false
  ; entropyConcept = false
  ; infoDecayExponential = false
  ; splitPropertyHolds = false
  ; areaLawHolds = false
  ; bridgeToMassGap = false
  ; localAlgebrasDefinedIsFalse = refl
  ; entropyConceptIsFalse = refl
  ; infoDecayExponentialIsFalse = refl
  ; splitPropertyHoldsIsFalse = refl
  ; areaLawHoldsIsFalse = refl
  ; bridgeToMassGapIsFalse = refl
  ; noClayPromotion = refl
  }
