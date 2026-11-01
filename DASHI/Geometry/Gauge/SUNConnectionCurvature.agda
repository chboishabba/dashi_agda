module DASHI.Geometry.Gauge.SUNConnectionCurvature where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Geometry.Gauge.SUNPrimitives

data SUNGaugeFieldObligation : Set where
  needsFlatGluingCompleteness : SUNGaugeFieldObligation
  needsGaugeOrbitQuotient     : SUNGaugeFieldObligation
  needsContinuumExtension     : SUNGaugeFieldObligation
  needsPrincipalBundleModel   : SUNGaugeFieldObligation

canonicalSUNGaugeFieldObligations : List SUNGaugeFieldObligation
canonicalSUNGaugeFieldObligations =
  needsFlatGluingCompleteness
  ∷ needsGaugeOrbitQuotient
  ∷ needsContinuumExtension
  ∷ needsPrincipalBundleModel
  ∷ []

record SUNGaugeField (N : Nat) : Set₁ where
  field
    baseSpaceShape : String
    connectionDefined : Bool
    curvatureDefined : Bool
    bianchiHolds : Bool
    gaugeActionDefined : Bool
    connectionDefinedIsTrue : connectionDefined ≡ true
    curvatureDefinedIsTrue : curvatureDefined ≡ true
    bianchiHoldsIsTrue : bianchiHolds ≡ true
    gaugeActionDefinedIsTrue : gaugeActionDefined ≡ true
    openObligations : List SUNGaugeFieldObligation
    openObligationsAreCanonical :
      openObligations ≡ canonicalSUNGaugeFieldObligations
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalSUNGaugeField : (N : Nat) → SUNGaugeField N
canonicalSUNGaugeField N = record
  { baseSpaceShape = "R4"
  ; connectionDefined = true
  ; curvatureDefined = true
  ; bianchiHolds = true
  ; gaugeActionDefined = true
  ; connectionDefinedIsTrue = refl
  ; curvatureDefinedIsTrue = refl
  ; bianchiHoldsIsTrue = refl
  ; gaugeActionDefinedIsTrue = refl
  ; openObligations = canonicalSUNGaugeFieldObligations
  ; openObligationsAreCanonical = refl
  ; noClayPromotion = refl
  }
