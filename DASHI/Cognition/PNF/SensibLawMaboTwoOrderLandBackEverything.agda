module DASHI.Cognition.PNF.SensibLawMaboTwoOrderLandBackEverything where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboTwoLegalOrderFibreExact as TwoOrder
import DASHI.Cognition.PNF.SensibLawIndigenousLandBackGlobalEvidenceExact as LandBack
import DASHI.Cognition.PNF.SensibLawMaboCriticalTheoryMaterialJusticeExact as Material
import DASHI.Cognition.PNF.SensibLawMaboColonialSovereigntyCriticalResidualExact as Critical

------------------------------------------------------------------------
-- Capstone: two legal orders + material LAND BACK evidence.
------------------------------------------------------------------------

crownOrderDoesNotDetermineIndigenousOrderExistence :
  TwoOrder.courtDeterminesOrderExistence TwoOrder.indigenousOrderFibre ≡ false
crownOrderDoesNotDetermineIndigenousOrderExistence = refl

crownRecognitionDoesNotCreateIndigenousOrder :
  TwoOrder.externalRecognitionCreatesOrder TwoOrder.indigenousOrderFibre ≡ false
crownRecognitionDoesNotCreateIndigenousOrder = refl

nativeTitleInterfaceDoesNotDeclareCrownGlobalSupremacy :
  TwoOrder.crownOrderGloballySupreme TwoOrder.nativeTitleRecognitionInterface ≡ false
nativeTitleInterfaceDoesNotDeclareCrownGlobalSupremacy = refl

nativeTitleInterfaceDoesNotReduceIndigenousLawToFacts :
  TwoOrder.indigenousOrderReducedToFactInput TwoOrder.nativeTitleRecognitionInterface ≡ false
nativeTitleInterfaceDoesNotReduceIndigenousLawToFacts = refl

sovereigntyExternalisationDoesNotSettleIndigenousOrder :
  TwoOrder.crownOrderGloballySupreme TwoOrder.sovereigntyExternalisationInterface ≡ false
sovereigntyExternalisationDoesNotSettleIndigenousOrder = refl

------------------------------------------------------------------------
-- Dawson hinge remains the first court-internal mediation question.
------------------------------------------------------------------------

dawsonRadicalTitleRecognitionBridgeRemainsContested :
  TwoOrder.status TwoOrder.radicalTitleToRecognitionCondition ≡ TwoOrder.contestedCourtInternalBridge
dawsonRadicalTitleRecognitionBridgeRemainsContested = refl

dawsonBridgeDoesNotProveColonialLegitimacy :
  TwoOrder.provesColonialLegitimacy TwoOrder.radicalTitleToRecognitionCondition ≡ false
dawsonBridgeDoesNotProveColonialLegitimacy = refl

------------------------------------------------------------------------
-- LAND BACK evidence is domain-relative but already strong on important axes.
------------------------------------------------------------------------

deforestationEvidenceIsStrongCausal :
  LandBack.deforestationState LandBack.currentGlobalEvidenceState ≡ LandBack.strongCausalSupportMapped
deforestationEvidenceIsStrongCausal = refl

restorationEvidenceIsStrongCausal :
  LandBack.restorationState LandBack.currentGlobalEvidenceState ≡ LandBack.strongCausalSupportMapped
restorationEvidenceIsStrongCausal = refl

mentalHealthDispossessionEvidenceIsSystematic :
  LandBack.mentalHealthState LandBack.currentGlobalEvidenceState ≡ LandBack.systematicHarmEvidenceMapped
mentalHealthDispossessionEvidenceIsSystematic = refl

socioeconomicEvidenceRetainsTradeoffs :
  LandBack.socioeconomicState LandBack.currentGlobalEvidenceState ≡ LandBack.mixedTradeoffMapped
socioeconomicEvidenceRetainsTradeoffs = refl

privateTitlingProxyRemainsInvalid :
  LandBack.privateTitlingProxyState LandBack.currentGlobalEvidenceState ≡ LandBack.mixedTradeoffMapped
privateTitlingProxyRemainsInvalid = refl

landBackHypothesisHasStrongEnvironmentalSupport :
  LandBack.environmentalSupportStrong LandBack.landBackGlobalEvidenceHypothesis ≡ true
landBackHypothesisHasStrongEnvironmentalSupport = refl

landBackHypothesisHasStrongDispossessionHarmSupport :
  LandBack.dispossessionHarmSupportStrong LandBack.landBackGlobalEvidenceHypothesis ≡ true
landBackHypothesisHasStrongDispossessionHarmSupport = refl

landBackDoesNotYetProveEverySocioeconomicOutcome :
  LandBack.everySocioeconomicOutcomeProved LandBack.landBackGlobalEvidenceHypothesis ≡ false
landBackDoesNotYetProveEverySocioeconomicOutcome = refl

------------------------------------------------------------------------
-- Material repair cannot be paid by source recognition alone.
------------------------------------------------------------------------

nativeTitleRecognitionCurrentlySourceMapped :
  Material.nativeTitleRecognition Material.currentCriticalRepairState ≡ Material.repairAxisSourceMapped
nativeTitleRecognitionCurrentlySourceMapped = refl

landReturnStillOpen :
  Material.landReturn Material.currentCriticalRepairState ≡ Material.repairAxisOpen
landReturnStillOpen = refl

sovereigntyRecognitionStillOpen :
  Material.sovereigntyRecognition Material.currentCriticalRepairState ≡ Material.repairAxisOpen
sovereigntyRecognitionStillOpen = refl

materialReparationStillOpen :
  Material.materialReparation Material.currentCriticalRepairState ≡ Material.repairAxisOpen
materialReparationStillOpen = refl

------------------------------------------------------------------------
-- Strong material regression: recognition of significance != protection.
------------------------------------------------------------------------

barrambinSignificanceAcknowledged :
  Material.significanceAcknowledged Material.barrambin2026Receipt ≡ true
barrambinSignificanceAcknowledged = refl

barrambinProtectionNotGranted :
  Material.emergencyProtectionGranted Material.barrambin2026Receipt ≡ false
barrambinProtectionNotGranted = refl

------------------------------------------------------------------------
-- Critical sovereignty state remains outside Crown doctrinal closure.
------------------------------------------------------------------------

nativeTitleDoesNotCloseSovereignty :
  Critical.NativeTitleRecognitionProvesSovereigntyRecognition → ⊥
nativeTitleDoesNotCloseSovereignty = Critical.nativeTitleDoesNotProveSovereigntyRecognition

nativeTitleDoesNotRepairDispossession :
  Critical.NativeTitleRecognitionRepairsDispossession → ⊥
nativeTitleDoesNotRepairDispossession = Critical.nativeTitleDoesNotRepairDispossessionByItself

------------------------------------------------------------------------
-- No-collapse laws exposed at the capstone surface.
------------------------------------------------------------------------

genericPrivateTitleIsNotLandBack : LandBack.GenericPrivateTitleEqualsLandBack → ⊥
genericPrivateTitleIsNotLandBack = LandBack.genericTitleDoesNotEqualLandBack

legalTitleAloneIsNotIndigenousAuthority : LandBack.LegalTitleAloneEqualsIndigenousAuthority → ⊥
legalTitleAloneIsNotIndigenousAuthority = LandBack.legalTitleAloneDoesNotEqualAuthority

forestSuccessDoesNotProveAllSocialOutcomes : LandBack.ForestEvidenceProvesEverySocialOutcome → ⊥
forestSuccessDoesNotProveAllSocialOutcomes = LandBack.forestEvidenceDoesNotProveEverySocialOutcome

crownOrderDoesNotContainIndigenousOrder : TwoOrder.CrownOrderContainsIndigenousOrder → ⊥
crownOrderDoesNotContainIndigenousOrder = TwoOrder.aCrownOrderDoesNotContainIndigenousOrder

municipalEffectDoesNotProveLegitimateSovereigntyTransfer :
  TwoOrder.MunicipalLegalEffectProvesLegitimateSovereigntyTransfer → ⊥
municipalEffectDoesNotProveLegitimateSovereigntyTransfer = TwoOrder.municipalEffectDoesNotProveLegitimateTransfer
