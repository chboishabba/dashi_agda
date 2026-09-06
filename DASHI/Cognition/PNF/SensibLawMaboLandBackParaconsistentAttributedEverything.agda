module DASHI.Cognition.PNF.SensibLawMaboLandBackParaconsistentAttributedEverything where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.RequiredAxisSupportSquareExact as Square
import DASHI.Cognition.PNF.SensibLawMaboLandBackAuditedCausalEverything as Audited
import DASHI.Cognition.PNF.SensibLawMaboTwoOrderParaconsistentSpaceExact as Para
import DASHI.Cognition.PNF.SensibLawIndigenousLandBackAttributedSourceAtlasExact as Sources
import DASHI.Cognition.PNF.SensibLawIndigenousLandBackAttributedSourceAtlasSupplementExact as Supplement
import DASHI.Cognition.PNF.SensibLawIndigenousCarbonColonialClassificationCriticalExact as CarbonCritical

------------------------------------------------------------------------
-- Preferred downstream surface after attribution + paraconsistency audit.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Structured bibliography is first-class and non-promoting.
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

------------------------------------------------------------------------
-- The Dawson result is placed inside the actual support space.
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
-- The older audited consumer closure remains true but is no longer the whole
-- state description.
------------------------------------------------------------------------

dawsonNarrowConsumerStillClosed :
  Audited.Dawson.consumerClosure Audited.Dawson.reconstructDawsonInternalLogic
  ≡ Audited.Dawson.consumerClosed
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
