module DASHI.Physics.Closure.NSA1TypeILorentzToAbelMassRouteBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data A1RouteStage : Set where
  typeIOrLorentzInputStage : A1RouteStage
  littlewoodPaleyShellMassStage : A1RouteStage
  reciprocalScaleWindowStage : A1RouteStage
  abelAverageStage : A1RouteStage
  boundedVariationTargetStage : A1RouteStage
  clayPromotionGuardStage : A1RouteStage

canonicalA1RouteStages : List A1RouteStage
canonicalA1RouteStages =
  typeIOrLorentzInputStage
  ∷ littlewoodPaleyShellMassStage
  ∷ reciprocalScaleWindowStage
  ∷ abelAverageStage
  ∷ boundedVariationTargetStage
  ∷ clayPromotionGuardStage
  ∷ []

a1RouteStageCount : Nat
a1RouteStageCount = listLength canonicalA1RouteStages

a1RouteStageCountIs6 : a1RouteStageCount ≡ 6
a1RouteStageCountIs6 = refl

data A1EstimateComponent : Set where
  typeIRescalingProfile : A1EstimateComponent
  uniformLorentzBound-L3∞ : A1EstimateComponent
  localizedL2ShellMass : A1EstimateComponent
  abelWindowWeight : A1EstimateComponent
  abelFiniteVariationBound : A1EstimateComponent

canonicalA1EstimateComponents : List A1EstimateComponent
canonicalA1EstimateComponents =
  typeIRescalingProfile
  ∷ uniformLorentzBound-L3∞
  ∷ localizedL2ShellMass
  ∷ abelWindowWeight
  ∷ abelFiniteVariationBound
  ∷ []

a1EstimateComponentCount : Nat
a1EstimateComponentCount = listLength canonicalA1EstimateComponents

a1EstimateComponentCountIs5 : a1EstimateComponentCount ≡ 5
a1EstimateComponentCountIs5 = refl

data A1Blocker : Set where
  lorentzToShellMassConstantTrackingMissing : A1Blocker
  offDiagonalTailAbsorptionMissing : A1Blocker
  pdeDefectMeasureConstructionMissing : A1Blocker
  abelTightnessTheoremMissing : A1Blocker

canonicalA1Blockers : List A1Blocker
canonicalA1Blockers =
  lorentzToShellMassConstantTrackingMissing
  ∷ offDiagonalTailAbsorptionMissing
  ∷ pdeDefectMeasureConstructionMissing
  ∷ abelTightnessTheoremMissing
  ∷ []

data NSA1TypeILorentzToAbelMassRouteBoundary : Set where
  mkNSA1TypeILorentzToAbelMassRouteBoundary :
    NSA1TypeILorentzToAbelMassRouteBoundary

canonicalNSA1TypeILorentzToAbelMassRouteBoundary :
  NSA1TypeILorentzToAbelMassRouteBoundary
canonicalNSA1TypeILorentzToAbelMassRouteBoundary =
  mkNSA1TypeILorentzToAbelMassRouteBoundary

boundaryRecorded :
  NSA1TypeILorentzToAbelMassRouteBoundary → Bool
boundaryRecorded _ = true

routeText :
  NSA1TypeILorentzToAbelMassRouteBoundary → String
routeText _ =
  "Type-I/L^{3,infty} -> LP shell mass -> Abel averaging -> bounded Abel mass"

boundedAbelMassTargetText :
  NSA1TypeILorentzToAbelMassRouteBoundary → String
boundedAbelMassTargetText _ =
  "sup_r TV(mu_r) <= C_A1(R,M) along reciprocal-scale Abel windows"

lorentzToShellMassProved :
  NSA1TypeILorentzToAbelMassRouteBoundary → Bool
lorentzToShellMassProved _ = false

abelFiniteVariationProved :
  NSA1TypeILorentzToAbelMassRouteBoundary → Bool
abelFiniteVariationProved _ = false

abelDefectMeasureConstructed :
  NSA1TypeILorentzToAbelMassRouteBoundary → Bool
abelDefectMeasureConstructed _ = false

a1Proved :
  NSA1TypeILorentzToAbelMassRouteBoundary → Bool
a1Proved _ = false

clayNavierStokesPromoted :
  NSA1TypeILorentzToAbelMassRouteBoundary → Bool
clayNavierStokesPromoted _ = false

terminalPromotion :
  NSA1TypeILorentzToAbelMassRouteBoundary → Bool
terminalPromotion _ = false

boundaryRecordedTrue :
  boundaryRecorded canonicalNSA1TypeILorentzToAbelMassRouteBoundary ≡ true
boundaryRecordedTrue = refl

lorentzToShellMassStillOpen :
  lorentzToShellMassProved canonicalNSA1TypeILorentzToAbelMassRouteBoundary
  ≡ false
lorentzToShellMassStillOpen = refl

abelFiniteVariationStillOpen :
  abelFiniteVariationProved canonicalNSA1TypeILorentzToAbelMassRouteBoundary
  ≡ false
abelFiniteVariationStillOpen = refl

a1StillOpen :
  a1Proved canonicalNSA1TypeILorentzToAbelMassRouteBoundary ≡ false
a1StillOpen = refl

clayPromotionStillFalse :
  clayNavierStokesPromoted canonicalNSA1TypeILorentzToAbelMassRouteBoundary
  ≡ false
clayPromotionStillFalse = refl

