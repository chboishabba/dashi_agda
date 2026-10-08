module DASHI.Physics.Optics.MatchedPhotonImagerComparatorExact where

open import Agda.Primitive using (Set; Set₁)
open import Relation.Binary.PropositionalEquality using (_≡_)

data ImagerFamily : Set where
  focusedLens : ImagerFamily
  randomDiffuser : ImagerFamily
  fresnelZonePlate : ImagerFamily

record MatchedPhotonComparator
    (Budget Pixels SceneFamily Metric : Set) : Set₁ where
  field
    photonBudget : ImagerFamily → Budget
    pixelBudget : ImagerFamily → Pixels
    admittedSceneFamily : ImagerFamily → SceneFamily
    metric : ImagerFamily → Metric

    samePhotonBudget :
      photonBudget focusedLens ≡ photonBudget randomDiffuser
    samePhotonBudgetZonePlate :
      photonBudget focusedLens ≡ photonBudget fresnelZonePlate
    samePixelBudget :
      pixelBudget focusedLens ≡ pixelBudget randomDiffuser
    samePixelBudgetZonePlate :
      pixelBudget focusedLens ≡ pixelBudget fresnelZonePlate
    sameSceneFamily :
      admittedSceneFamily focusedLens ≡ admittedSceneFamily randomDiffuser
    sameSceneFamilyZonePlate :
      admittedSceneFamily focusedLens ≡ admittedSceneFamily fresnelZonePlate

    throughputCalibrationAuthority : Set
    throughputCalibrationReceipt : throughputCalibrationAuthority
    metricAuthority : Set
    metricReceipt : metricAuthority

open MatchedPhotonComparator public
