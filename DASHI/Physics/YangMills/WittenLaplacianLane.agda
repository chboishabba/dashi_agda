module DASHI.Physics.YangMills.WittenLaplacianLane where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Geometry.Gauge.SUNPrimitives

record WittenLaplacianLane : Set₁ where
  field
    actionFunctionalDefined : Bool
    deformedDiffDefined : Bool
    lowSpectrumControlled : Bool
    gaugeOrbitQuotientHandled : Bool
    infiniteDimLimitDefined : Bool
    massGapCandidate : Bool
    actionFunctionalDefinedIsFalse : actionFunctionalDefined ≡ false
    deformedDiffDefinedIsFalse : deformedDiffDefined ≡ false
    lowSpectrumControlledIsFalse : lowSpectrumControlled ≡ false
    gaugeOrbitQuotientHandledIsFalse : gaugeOrbitQuotientHandled ≡ false
    infiniteDimLimitDefinedIsFalse : infiniteDimLimitDefined ≡ false
    massGapCandidateIsFalse : massGapCandidate ≡ false
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalWittenLaplacianLane : WittenLaplacianLane
canonicalWittenLaplacianLane = record
  { actionFunctionalDefined = false
  ; deformedDiffDefined = false
  ; lowSpectrumControlled = false
  ; gaugeOrbitQuotientHandled = false
  ; infiniteDimLimitDefined = false
  ; massGapCandidate = false
  ; actionFunctionalDefinedIsFalse = refl
  ; deformedDiffDefinedIsFalse = refl
  ; lowSpectrumControlledIsFalse = refl
  ; gaugeOrbitQuotientHandledIsFalse = refl
  ; infiniteDimLimitDefinedIsFalse = refl
  ; massGapCandidateIsFalse = refl
  ; noClayPromotion = refl
  }
