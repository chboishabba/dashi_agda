module DASHI.Physics.YangMills.MassGapSpectralStatement where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.Gauge.SUNPrimitives

record MassGapSpectralStatement : Set₁ where
  field
    hamiltonianAvailable : Bool
    vacuumEigenvalueZero : Bool
    vacuumMultiplicityOne : Bool
    spectralGapPositive : Bool
    gapBound : String
    clayPromoted : Bool
    hamiltonianAvailableIsFalse : hamiltonianAvailable ≡ false
    vacuumEigenvalueZeroIsFalse : vacuumEigenvalueZero ≡ false
    vacuumMultiplicityOneIsFalse : vacuumMultiplicityOne ≡ false
    spectralGapPositiveIsFalse : spectralGapPositive ≡ false
    clayPromotedIsFalse : clayPromoted ≡ false
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalMassGapSpectralStatement : MassGapSpectralStatement
canonicalMassGapSpectralStatement = record
  { hamiltonianAvailable = false
  ; vacuumEigenvalueZero = false
  ; vacuumMultiplicityOne = false
  ; spectralGapPositive = false
  ; gapBound = "unproved"
  ; clayPromoted = false
  ; hamiltonianAvailableIsFalse = refl
  ; vacuumEigenvalueZeroIsFalse = refl
  ; vacuumMultiplicityOneIsFalse = refl
  ; spectralGapPositiveIsFalse = refl
  ; clayPromotedIsFalse = refl
  ; noClayPromotion = refl
  }
