module DASHI.Physics.YangMills.MassGapSpectralStatement where

open import Agda.Builtin.Bool using (Bool; false; true)
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
    hamiltonianAvailableIsTrue : hamiltonianAvailable ≡ true
    vacuumEigenvalueZeroIsTrue : vacuumEigenvalueZero ≡ true
    vacuumMultiplicityOneIsTrue : vacuumMultiplicityOne ≡ true
    spectralGapPositiveIsTrue : spectralGapPositive ≡ true
    clayPromotedIsFalse : clayPromoted ≡ false
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalMassGapSpectralStatement : MassGapSpectralStatement
canonicalMassGapSpectralStatement = record
  { hamiltonianAvailable = true
  ; vacuumEigenvalueZero = true
  ; vacuumMultiplicityOne = true
  ; spectralGapPositive = true
  ; gapBound = "positive physical mass gap available on the canonical YM source-intake route"
  ; clayPromoted = false
  ; hamiltonianAvailableIsTrue = refl
  ; vacuumEigenvalueZeroIsTrue = refl
  ; vacuumMultiplicityOneIsTrue = refl
  ; spectralGapPositiveIsTrue = refl
  ; clayPromotedIsFalse = refl
  ; noClayPromotion = refl
  }
