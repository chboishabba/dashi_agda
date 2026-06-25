module DASHI.Physics.YangMills.BalabanAnisotropicDiameterCompatibility where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
import DASHI.Physics.Closure.ClaySprintSeventySixYMAnisotropicAllDiameterKPReceipt
  as KP76
import DASHI.Physics.YangMills.BalabanSpatialLinkWeightLowerBound
  as LinkLB

Scalar : Set
Scalar = String

data AnisotropicDiameterObligation : Set where
  singleLinkBase : AnisotropicDiameterObligation
  minLinkWeightPositive : AnisotropicDiameterObligation
  spanningPathStep : AnisotropicDiameterObligation

canonicalAnisotropicDiameterObligations :
  List AnisotropicDiameterObligation
canonicalAnisotropicDiameterObligations =
  singleLinkBase
  ∷ minLinkWeightPositive
  ∷ spanningPathStep
  ∷ []

record AnisotropicDiameterCompatibility : Set₁ where
  field
    arithmeticReceipt :
      KP76.ClaySprintSeventySixYMAnisotropicAllDiameterKPReceipt
    spatialLinkWeightLowerBound :
      LinkLB.SpatialLinkWeightLowerBound
    spatialLinkRegularityAssumption :
      LinkLB.SpatialLinkRegularityAssumption
    weightedArithmeticCloses :
      KP76.anisotropicKPArithmeticClosed arithmeticReceipt ≡ true
    targetConvention : String
    targetConventionIsLoss :
      targetConvention ≡
      "loss convention: ||.||_diameter <= C_loss * ||.||_anisotropic"
    targetInequality : String
    targetInequalityIsCanonical :
      targetInequality ≡
      "||.||_diameter <= C_loss * ||.||_anisotropic"
    marginConstraint : String
    marginConstraintIsCanonical :
      marginConstraint ≡
      "C_loss * 4q < 1 iff C_loss < 1.0786 iff minLinkWeight > 0.9271"
    fourQValue : Scalar
    fourQValueIsCanonical :
      fourQValue ≡ "0.9271275790105094"
    lossBudgetUpperBound : Scalar
    lossBudgetUpperBoundIsCanonical :
      lossBudgetUpperBound ≡ "1.0786"
    requiredMinLinkWeight : Scalar
    requiredMinLinkWeightIsCanonical :
      requiredMinLinkWeight ≡ "0.9271"
    singleLinkBaseAvailable :
      Bool
    minLinkWeightPositiveAvailable :
      Bool
    diameterLossMarginSurvives :
      Bool
    spanningPathStepAvailable :
      Bool
    dominationConclusion :
      Bool
    diameterLossConstant : Scalar
    diameterLossConstantAvailable : Bool
    singleLinkBaseAvailableIsFalse :
      singleLinkBaseAvailable ≡ false
    minLinkWeightPositiveAvailableIsFalse :
      minLinkWeightPositiveAvailable ≡ false
    diameterLossMarginSurvivesIsFalse :
      diameterLossMarginSurvives ≡ false
    spanningPathStepAvailableIsFalse :
      spanningPathStepAvailable ≡ false
    dominationConclusionIsFalse :
      dominationConclusion ≡ false
    diameterLossConstantAvailableIsFalse :
      diameterLossConstantAvailable ≡ false
    blockerSummary : String
    blockerSummaryIsCanonical :
      blockerSummary ≡
      "The bridge now isolates the first missing mathematical input: a typed spatial link-weight lower bound. Until minLinkWeight > 0 is exposed, single-link base and spanning-path induction remain unavailable; until minLinkWeight > 0.9271 is exposed, the KP margin does not survive."
    openObligations : List AnisotropicDiameterObligation
    openObligationsAreCanonical :
      openObligations ≡ canonicalAnisotropicDiameterObligations
    noClayPromotion : clayYangMillsPromoted ≡ false

currentAnisotropicDiameterCompatibility :
  AnisotropicDiameterCompatibility
currentAnisotropicDiameterCompatibility = record
  { arithmeticReceipt =
      KP76.canonicalSprint76YMAnisotropicAllDiameterKPReceipt
  ; spatialLinkWeightLowerBound =
      LinkLB.currentSpatialLinkWeightLowerBound
  ; spatialLinkRegularityAssumption =
      LinkLB.currentSpatialLinkRegularityAssumption
  ; weightedArithmeticCloses =
      KP76.anisotropicKPArithmeticClosedIsTrue
        KP76.canonicalSprint76YMAnisotropicAllDiameterKPReceipt
  ; targetConvention =
      "loss convention: ||.||_diameter <= C_loss * ||.||_anisotropic"
  ; targetConventionIsLoss = refl
  ; targetInequality =
      "||.||_diameter <= C_loss * ||.||_anisotropic"
  ; targetInequalityIsCanonical = refl
  ; marginConstraint =
      "C_loss * 4q < 1 iff C_loss < 1.0786 iff minLinkWeight > 0.9271"
  ; marginConstraintIsCanonical = refl
  ; fourQValue = "0.9271275790105094"
  ; fourQValueIsCanonical = refl
  ; lossBudgetUpperBound = "1.0786"
  ; lossBudgetUpperBoundIsCanonical = refl
  ; requiredMinLinkWeight = "0.9271"
  ; requiredMinLinkWeightIsCanonical = refl
  ; singleLinkBaseAvailable = false
  ; minLinkWeightPositiveAvailable = false
  ; diameterLossMarginSurvives = false
  ; spanningPathStepAvailable = false
  ; dominationConclusion = false
  ; diameterLossConstant = "unproved"
  ; diameterLossConstantAvailable = false
  ; singleLinkBaseAvailableIsFalse = refl
  ; minLinkWeightPositiveAvailableIsFalse = refl
  ; diameterLossMarginSurvivesIsFalse = refl
  ; spanningPathStepAvailableIsFalse = refl
  ; dominationConclusionIsFalse = refl
  ; diameterLossConstantAvailableIsFalse = refl
  ; blockerSummary =
      "The bridge now isolates the first missing mathematical input: a typed spatial link-weight lower bound. Until minLinkWeight > 0 is exposed, single-link base and spanning-path induction remain unavailable; until minLinkWeight > 0.9271 is exposed, the KP margin does not survive."
  ; blockerSummaryIsCanonical = refl
  ; openObligations = canonicalAnisotropicDiameterObligations
  ; openObligationsAreCanonical = refl
  ; noClayPromotion = refl
  }
