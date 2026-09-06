module DASHI.Cognition.PNF.SensibLawMaboLandBackParaconsistentAttributedEverything where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.RequiredAxisSupportSquareExact as Square
import DASHI.Cognition.PNF.SensibLawMaboDawsonCrownDerivationHingeClosureExact as Dawson
import DASHI.Cognition.PNF.SensibLawMaboTwoOrderParaconsistentSpaceExact as Para
import DASHI.Cognition.PNF.SensibLawIndigenousLandBackAttributedSourceAtlasExact as Sources
import DASHI.Cognition.PNF.SensibLawIndigenousLandBackAttributedSourceAtlasSupplementExact as Supplement
import DASHI.Cognition.PNF.SensibLawIndigenousCarbonColonialClassificationCriticalExact as CarbonCritical

------------------------------------------------------------------------
-- Preferred downstream surface after attribution + paraconsistency audit.
------------------------------------------------------------------------

primaryStructuredSourceCount :
  Attr.sourceCount (Attr.sources Sources.landBackAttributedSourceAtlas) ≡ 15
primaryStructuredSourceCount = refl

supplementStructuredSourceCount :
  Attr.sourceCount (Attr.sources Supplement.supplementarySourceAtlas) ≡ 5
supplementStructuredSourceCount = refl

primaryAtlasDoesNotCreateAuthority :
  Attr.atlasCreatesAuthority Sources.landBackAttributedSourceAtlas ≡ false
primaryAtlasDoesNotCreateAuthority = refl

supplementAtlasDoesNotCreateAuthority :
  Attr.atlasCreatesAuthority Supplement.supplementarySourceAtlas ≡ false
supplementAtlasDoesNotCreateAuthority = refl

-- Representative exact metadata regressions.
denBraberDoiPinned :
  Attr.doiState Sources.denBraber2024Source
  ≡ Attr.doiRecorded "10.1038/s41559-024-02458-w"
denBraberDoiPinned = refl

baragwanath2020DoiPinned :
  Attr.doiState Sources.baragwanathBayi2020Source
  ≡ Attr.doiRecorded "10.1073/pnas.1917874117"
baragwanath2020DoiPinned = refl

probst2020DoiPinned :
  Attr.doiState Sources.probst2020Source
  ≡ Attr.doiRecorded "10.1038/s41893-020-0537-2"
probst2020DoiPinned = refl

biaNoDoiClaimRemainsAtlasLocal :
  Attr.doiState Sources.biaCarbon2023Source ≡ Attr.noDOIRecordedByAtlas
biaNoDoiClaimRemainsAtlasLocal = refl

------------------------------------------------------------------------
-- Dawson internal closure is one paraconsistent axis, not the global state.
------------------------------------------------------------------------

dawsonInternalLogicIsPositiveOnlyNotGlobalClosure :
  Para.dawsonInternal Para.currentMaboParaconsistentSpace ≡ Square.positiveOnly
dawsonInternalLogicIsPositiveOnlyNotGlobalClosure = refl

crownExhaustiveSourceClaimRemainsConflicting :
  Para.crownSourceExhaustiveness Para.currentMaboParaconsistentSpace
  ≡ Square.conflictingState
crownExhaustiveSourceClaimRemainsConflicting = refl

colonialLegitimacyRemainsMissing :
  Para.colonialLegitimacy Para.currentMaboParaconsistentSpace
  ≡ Square.missingState
colonialLegitimacyRemainsMissing = refl

indigenousCessionRemainsMissing :
  Para.indigenousCession Para.currentMaboParaconsistentSpace
  ≡ Square.missingState
indigenousCessionRemainsMissing = refl

materialRepairIsNotPaidByNativeTitleRecognition :
  Para.materialRepair Para.currentMaboParaconsistentSpace
  ≡ Square.negativeOnly
materialRepairIsNotPaidByNativeTitleRecognition = refl

internalClosureAndCrossOrderConflictCoexist :
  Para.dawsonInternal Para.currentMaboParaconsistentSpace ≡ Square.positiveOnly
  × Para.crownSourceExhaustiveness Para.currentMaboParaconsistentSpace ≡ Square.conflictingState
internalClosureAndCrossOrderConflictCoexist = refl , refl

------------------------------------------------------------------------
-- The narrow Dawson consumer remains closed, but that does not globally close
-- the cross-order support space.
------------------------------------------------------------------------

dawsonNarrowConsumerStillClosed :
  Dawson.consumerClosure Dawson.reconstructDawsonInternalLogic
  ≡ Dawson.consumerClosed
dawsonNarrowConsumerStillClosed = refl

narrowClosureDoesNotImplyGlobalResolution :
  Para.internalClosureImpliesGlobalResolution Para.currentMaboParaconsistentSpace ≡ false
narrowClosureDoesNotImplyGlobalResolution = refl

paraconsistentConflictDoesNotExplodeSpace :
  Para.conflictExplodesEveryAxis Para.currentMaboParaconsistentSpace ≡ false
paraconsistentConflictDoesNotExplodeSpace = refl

------------------------------------------------------------------------
-- BIA: administrative proposition, critical interpretation and decolonial
-- hypothesis remain separately attributed.
------------------------------------------------------------------------

biaClassificationIsAgencyProposition :
  CarbonCritical.propositionKind CarbonCritical.biaStoredCarbonNotTrustAsset
  ≡ CarbonCritical.agencyClassificationProposition
biaClassificationIsAgencyProposition = refl

extractiveLegibilityIsOurCriticalInterpretation :
  CarbonCritical.propositionKind CarbonCritical.extractiveLegibilityAsymmetry
  ≡ CarbonCritical.criticalInstitutionalInterpretation
extractiveLegibilityIsOurCriticalInterpretation = refl

colonialConvenienceRemainsDecolonialInterpretation :
  CarbonCritical.propositionKind CarbonCritical.colonialConvenienceHypothesis
  ≡ CarbonCritical.decolonialNormativeInterpretation
colonialConvenienceRemainsDecolonialInterpretation = refl

biaDoesNotSayOurCriticalInterpretation :
  CarbonCritical.sourceSaysThisDirectly CarbonCritical.extractiveLegibilityAsymmetry ≡ false
biaDoesNotSayOurCriticalInterpretation = refl

biaClassificationDoesNotExhaustValueOntology :
  CarbonCritical.agencyClassificationExhaustsValueOntology
    CarbonCritical.canonicalExtractiveLegibilityBoundary ≡ false
biaClassificationDoesNotExhaustValueOntology = refl

------------------------------------------------------------------------
-- No-collapse exports.
------------------------------------------------------------------------

dawsonClosureDoesNotResolveSupremacyConflict :
  Para.DawsonInternalClosureResolvesCrownSupremacyConflict → ⊥
dawsonClosureDoesNotResolveSupremacyConflict =
  Para.dawsonInternalClosureDoesNotResolveSupremacyConflict

supremacyConflictDoesNotResolveLegitimacy :
  Para.CrownSupremacyConflictResolvesColonialLegitimacy → ⊥
supremacyConflictDoesNotResolveLegitimacy =
  Para.supremacyConflictDoesNotResolveColonialLegitimacy

crossOrderOppositionDoesNotAutoBecomeClassicalNegation :
  Para.CrossOrderOppositionAutomaticallyClassicalNegation → ⊥
crossOrderOppositionDoesNotAutoBecomeClassicalNegation =
  Para.crossOrderOppositionIsNotAutomaticallyNegation

biaClassificationDoesNotProveColonialIntent :
  CarbonCritical.BIAClassificationProvesColonialIntent → ⊥
biaClassificationDoesNotProveColonialIntent =
  CarbonCritical.biaClassificationDoesNotProveColonialIntent

criticalInterpretationDoesNotBecomeBiaAuthorship :
  CarbonCritical.CriticalInterpretationIsBIAAuthorship → ⊥
criticalInterpretationDoesNotBecomeBiaAuthorship =
  CarbonCritical.criticalInterpretationDoesNotTransferToBia
