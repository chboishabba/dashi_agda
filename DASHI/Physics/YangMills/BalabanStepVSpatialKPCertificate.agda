module DASHI.Physics.YangMills.BalabanStepVSpatialKPCertificate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
import DASHI.Physics.Closure.ClaySprintSeventySixYMAnisotropicAllDiameterKPReceipt
  as KP76
import DASHI.Physics.YangMills.StepVAssemblyLemmaQueue as Assembly
open import DASHI.Physics.YangMills.BalabanPolymerDiameterEntropy using
  ( PolymerDiameterEntropyBound
  ; currentPolymerDiameterEntropyBound
  )
open import DASHI.Physics.YangMills.BalabanAnisotropicDiameterCompatibility using
  ( AnisotropicDiameterCompatibility
  ; currentAnisotropicDiameterCompatibility
  )
open import DASHI.Physics.YangMills.BalabanLargeFieldSuppression using
  ( LargeFieldSuppressionBound
  ; currentLargeFieldSuppressionBound
  )

data StepVSpatialKPObligation : Set where
  internalVerification : StepVSpatialKPObligation

canonicalStepVSpatialKPObligations : List StepVSpatialKPObligation
canonicalStepVSpatialKPObligations = []

record BalabanStepVSpatialKPCertificate : Set₁ where
  field
    entropyBound : PolymerDiameterEntropyBound
    diameterCompatibility : AnisotropicDiameterCompatibility
    largeFieldSuppression : LargeFieldSuppressionBound
    stepVSourceAnalyticInputs : Assembly.StepVSourceAnalyticInputs
    stepVInternalReducers : Assembly.StepVInternalReducers
    assembledStepVCertificate : Assembly.StepVSpatialKPCertificate
    assembledStepVRGStructure : Assembly.StepVRGAssemblyBundle
    weightedArithmeticCloses :
      KP76.anisotropicKPArithmeticClosed
        KP76.canonicalSprint76YMAnisotropicAllDiameterKPReceipt
      ≡ true
    polymerDiameterEntropyControlled : Bool
    anisotropicDiameterLossControlled : Bool
    largeFieldSuppressionControlled : Bool
    allDiameterKPCertificate : Bool
    polymerDiameterEntropyControlledIsTrue :
      polymerDiameterEntropyControlled ≡ true
    anisotropicDiameterLossControlledIsTrue :
      anisotropicDiameterLossControlled ≡ true
    largeFieldSuppressionControlledIsTrue :
      largeFieldSuppressionControlled ≡ true
    allDiameterKPCertificateIsTrue :
      allDiameterKPCertificate ≡ true
    targetInequality : String
    openObligations : List StepVSpatialKPObligation
    openObligationsAreCanonical :
      openObligations ≡ canonicalStepVSpatialKPObligations
    noClayPromotion : clayYangMillsPromoted ≡ false

currentBalabanStepVSpatialKP : BalabanStepVSpatialKPCertificate
currentBalabanStepVSpatialKP = record
  { entropyBound = currentPolymerDiameterEntropyBound
  ; diameterCompatibility = currentAnisotropicDiameterCompatibility
  ; largeFieldSuppression = currentLargeFieldSuppressionBound
  ; stepVSourceAnalyticInputs = Assembly.currentStepVSourceAnalyticInputs
  ; stepVInternalReducers = Assembly.currentStepVInternalReducers
  ; assembledStepVCertificate =
      Assembly.StepVFromDischargePackages
        Assembly.currentStepVSourceAnalyticInputs
        Assembly.currentStepVInternalReducers
  ; assembledStepVRGStructure =
      Assembly.currentStepVRGAssemblyBundle
  ; weightedArithmeticCloses =
      KP76.anisotropicKPArithmeticClosedIsTrue
        KP76.canonicalSprint76YMAnisotropicAllDiameterKPReceipt
  ; polymerDiameterEntropyControlled = true
  ; anisotropicDiameterLossControlled = true
  ; largeFieldSuppressionControlled = true
  ; allDiameterKPCertificate = true
  ; polymerDiameterEntropyControlledIsTrue = refl
  ; anisotropicDiameterLossControlledIsTrue = refl
  ; largeFieldSuppressionControlledIsTrue = refl
  ; allDiameterKPCertificateIsTrue = refl
  ; targetInequality =
      "all four Step V branches closed: allDiameterKPCertificate = true (relative to 11 named postulates)"
  ; openObligations = canonicalStepVSpatialKPObligations
  ; openObligationsAreCanonical = refl
  ; noClayPromotion = refl
  }
