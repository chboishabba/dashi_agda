module DASHI.Cognition.PNF.SensibLawDominantChartEpistemicCompressionCrossPollinationExact where

------------------------------------------------------------------------
-- SENSIBLAW DOMINANT-CHART EPISTEMIC COMPRESSION CROSS-POLLINATION
--
-- This owner cross-pollinates recurring theorem shapes without claiming that
-- Crown law, capitalism, psychology, feminist theory, intersectionality or the
-- Amalek operator are one doctrine.  The shared mathematical question is:
--
--   Which consumer-relevant distinctions disappear under this observer?
--
-- Country/community relations are NOT called assets by this owner.  The phrase
-- "trust asset" appears only where the BIA administrative source/category is
-- being represented as such.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.DominantChartEpistemicCompressionExact as Compression
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.FeministRechartingSourceBridgeExact as Feminist
import DASHI.Core.RepresentationSubjectPositionNonfactorabilityExact as Subject
import DASHI.Core.TrinhSubjectInMakingNoncollapseExact as Trinh
import DASHI.Core.ButlerPerformativeGenesisNonDescentExact as Butler
import DASHI.Core.LugonesPurityCurdlingNonfactorabilityExact as Lugones
import DASHI.Core.McCallCategoryStrategyBoundaryExact as McCall
import DASHI.Core.SituatedFormalisationBoundaryExact as Haraway
import DASHI.Core.PlumwoodMasterModelOperationFamilyExact as Plumwood
import DASHI.Core.DifferenceWithoutHierarchyExact as Difference
import DASHI.Core.CriticalSocialEcologyObserverRegimeExact as Ecology
import DASHI.Core.RecognitionConstitutionNonfactorabilityExact as Recognition
import DASHI.Core.PoliticalContestabilityExact as Contestability
import DASHI.Culture.IntersectionalPowerValueFolkModelBoundary as Intersectional
import DASHI.Culture.AmalekAuthorityProjectionBoundary as Amalek
import DASHI.Physics.Foundations.SettlerEnemyAbstractionExact as EnemyCompression
import DASHI.Culture.LopezRiosPsychologisationDialecticNonDescentExact as Lopez
import DASHI.Cognition.PNF.SensibLawMaboCrownRecognitionProjectionNonFactorabilityExact as Crown
import DASHI.Cognition.PNF.SensibLawLandBackIncomeProjectionNonFactorabilityExact as Income
import DASHI.Cognition.PNF.SensibLawIndigenousCarbonValueProjectionNonFactorabilityExact as Carbon

------------------------------------------------------------------------
-- Exact domain instances of one generic projection-inadequacy compiler.
------------------------------------------------------------------------

crownRecognitionCompression :
  Compression.ProjectionInadequacyReceipt
    Crown.crownRecognitionObserver
    Crown.indigenousAuthorityOutcome
crownRecognitionCompression =
  Compression.projection-inadequacy-receipt
    Compression.juridicalRecognitionCompression
    "Crown recognition / municipal native-title status observer"
    "consumer requiring independently modelled Country/community authority"
    "same Crown-recognition status can coexist with distinct community-authority outcomes"
    Crown.crownRecognitionCannotRecoverIndigenousAuthorityWitness
    true refl
    false refl
    false refl
    false refl

cashIncomeCompression :
  Compression.ProjectionInadequacyReceipt
    Income.cashIncomeObserver
    Income.landAuthorityOutcome
cashIncomeCompression =
  Compression.projection-inadequacy-receipt
    Compression.economicScalarCompression
    "cash-income / fiscal socioeconomic observer"
    "consumer requiring collective land security, decision authority and relational/material state"
    "same cash-income observation can coexist with dispossessed and land-secure authority states"
    Income.cashIncomeCannotRecoverLandAuthorityWitness
    true refl
    false refl
    false refl
    false refl

biaTrustAssetAdministrativeCompression :
  Compression.ProjectionInadequacyReceipt
    Carbon.trustAssetObserver
    Carbon.stewardshipValueOutcome
biaTrustAssetAdministrativeCompression =
  Compression.projection-inadequacy-receipt
    Compression.administrativeClassificationCompression
    "BIA administrative 'trust asset' classification observer"
    "consumer requiring non-extractive stewardship/ecological/cultural/community value distinctions"
    "same BIA administrative category can coexist with distinct stewardship-value states"
    Carbon.canonicalTrustAssetNonFactorability
    true refl
    false refl
    false refl
    false refl

representationalSubjectCompression :
  Compression.ProjectionInadequacyReceipt
    Subject.categoryVisibility
    Subject.subjectPosition
representationalSubjectCompression =
  Compression.projection-inadequacy-receipt
    Compression.representationalSubjectCompression
    "public category visibility / representability"
    "consumer requiring originating subject-position or relational authority"
    "same representable category can contain represented-only and originating-subject positions"
    (INF.nonFactorabilityWitness
      Subject.representedOnly
      Subject.originatingSubject
      refl
      Subject.subjectPositionDiffers)
    true refl
    false refl
    false refl
    false refl

psychologisingCompression :
  Compression.ProjectionInadequacyReceipt
    (λ state → Lopez.individualObservation state Lopez.samePerson)
    (λ state → Lopez.structuralDependency state Lopez.samePerson)
psychologisingCompression =
  Compression.projection-inadequacy-receipt
    Compression.psychologisingIndividualisationCompression
    "individual psychological distress observation"
    "consumer requiring structural/material dependency"
    "same individual distress observation can occur under distinct structural dependency states"
    Lopez.genericPsychologisationWitness
    true refl
    false refl
    false refl
    false refl

intersectionalSingleAxisCompression :
  Compression.ProjectionInadequacyReceipt
    INF.flatProjection
    INF.relationalOutcome
intersectionalSingleAxisCompression =
  Compression.projection-inadequacy-receipt
    Compression.singleAxisIntersectionalCompression
    "single-axis demographic/category observer"
    "consumer requiring situated relational outcome"
    "same demographic label can contain different relational-power outcomes"
    INF.canonicalIntersectionalNonFactorability
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Exact generic consequences for all six lanes.
------------------------------------------------------------------------

crownRecognitionCannotCarryCountryCommunityAuthority :
  INF.FactorsThrough Crown.crownRecognitionObserver Crown.indigenousAuthorityOutcome → ⊥
crownRecognitionCannotCarryCountryCommunityAuthority =
  Compression.projectionCannotFactorTarget crownRecognitionCompression

cashIncomeCannotCarryCollectiveLandAuthority :
  INF.FactorsThrough Income.cashIncomeObserver Income.landAuthorityOutcome → ⊥
cashIncomeCannotCarryCollectiveLandAuthority =
  Compression.projectionCannotFactorTarget cashIncomeCompression

biaCategoryCannotCarryStewardshipRelation :
  INF.FactorsThrough Carbon.trustAssetObserver Carbon.stewardshipValueOutcome → ⊥
biaCategoryCannotCarryStewardshipRelation =
  Compression.projectionCannotFactorTarget biaTrustAssetAdministrativeCompression

publicRepresentationCannotCarryOriginatingSubjectPosition :
  INF.FactorsThrough Subject.categoryVisibility Subject.subjectPosition → ⊥
publicRepresentationCannotCarryOriginatingSubjectPosition =
  Compression.projectionCannotFactorTarget representationalSubjectCompression

individualDistressCannotCarryStructuralDependency :
  INF.FactorsThrough
    (λ state → Lopez.individualObservation state Lopez.samePerson)
    (λ state → Lopez.structuralDependency state Lopez.samePerson) → ⊥
individualDistressCannotCarryStructuralDependency =
  Compression.projectionCannotFactorTarget psychologisingCompression

singleAxisCannotCarrySituatedRelationalOutcome :
  INF.FactorsThrough INF.flatProjection INF.relationalOutcome → ⊥
singleAxisCannotCarrySituatedRelationalOutcome =
  Compression.projectionCannotFactorTarget intersectionalSingleAxisCompression

------------------------------------------------------------------------
-- Feminist repair theorem: re-description after collapse is insufficient.
------------------------------------------------------------------------

feministPositiveRepair : Feminist.PositiveRecharting Feminist.inheritedChart
feministPositiveRepair = Feminist.canonicalPositiveRecharting

crownRewordingCannotRecoverErasedAuthority :
  ∀ {Recharted : Set} →
  (rechart : Crown.CrownRecognitionObservation → Recharted) →
  INF.FactorsThrough
    (λ state → rechart (Crown.crownRecognitionObserver state))
    Crown.indigenousAuthorityOutcome → ⊥
crownRewordingCannotRecoverErasedAuthority =
  Compression.projectionCannotBeRepairedByPostcomposition crownRecognitionCompression

incomeReweightingCannotRecoverErasedRelation :
  ∀ {Recharted : Set} →
  (rechart : Income.CashIncomeObservation → Recharted) →
  INF.FactorsThrough
    (λ state → rechart (Income.cashIncomeObserver state))
    Income.landAuthorityOutcome → ⊥
incomeReweightingCannotRecoverErasedRelation =
  Compression.projectionCannotBeRepairedByPostcomposition cashIncomeCompression

biaReclassificationCannotRecoverStewardshipRelation :
  ∀ {Recharted : Set} →
  (rechart : Carbon.TrustAssetProjection → Recharted) →
  INF.FactorsThrough
    (λ state → rechart (Carbon.trustAssetObserver state))
    Carbon.stewardshipValueOutcome → ⊥
biaReclassificationCannotRecoverStewardshipRelation =
  Compression.projectionCannotBeRepairedByPostcomposition biaTrustAssetAdministrativeCompression

------------------------------------------------------------------------
-- Political/interpretive audit lenses remain explicit, situated and bounded.
------------------------------------------------------------------------

data PoliticalEpistemicAuditLens : Set where
  antiCapitalistCommodityFormAudit : PoliticalEpistemicAuditLens
  communistMaterialRelationAudit : PoliticalEpistemicAuditLens
  decolonialRecognitionAudit : PoliticalEpistemicAuditLens
  feministSubjectPositionAudit : PoliticalEpistemicAuditLens
  intersectionalSingleAxisAudit : PoliticalEpistemicAuditLens
  antiPsychologisationStructuralAudit : PoliticalEpistemicAuditLens


record AuditLensBoundary : Set where
  constructor audit-lens-boundary
  field
    lens : PoliticalEpistemicAuditLens
    question : String
    automaticallyProvesNamedInstitutionIntent : Bool
    automaticallyProvesNamedInstitutionIntentIsFalse :
      automaticallyProvesNamedInstitutionIntent ≡ false
    automaticallyBecomesWorldTruth : Bool
    automaticallyBecomesWorldTruthIsFalse : automaticallyBecomesWorldTruth ≡ false

open AuditLensBoundary public

antiCapitalistAuditBoundary : AuditLensBoundary
antiCapitalistAuditBoundary = audit-lens-boundary
  antiCapitalistCommodityFormAudit
  "what relations disappear when value is made legible primarily through property, income, price, commodity or administrative asset categories?"
  false refl
  false refl

communistMaterialRelationBoundary : AuditLensBoundary
communistMaterialRelationBoundary = audit-lens-boundary
  communistMaterialRelationAudit
  "what material and collective relations of social reproduction are hidden by individualised or commodity-form observations?"
  false refl
  false refl

------------------------------------------------------------------------
-- Country/land vocabulary boundary.
------------------------------------------------------------------------

record CountryRelationVocabularyBoundary : Set where
  constructor country-relation-vocabulary-boundary
  field
    countryRelationIsAssetByDefault : Bool
    countryRelationIsAssetByDefaultIsFalse : countryRelationIsAssetByDefault ≡ false
    indigenousAuthorityReducedToPropertyTitle : Bool
    indigenousAuthorityReducedToPropertyTitleIsFalse :
      indigenousAuthorityReducedToPropertyTitle ≡ false
    biaTrustAssetPhraseRetainedOnlyAsSourceAdministrativeCategory : Bool
    biaTrustAssetPhraseRetainedOnlyAsSourceAdministrativeCategoryIsTrue :
      biaTrustAssetPhraseRetainedOnlyAsSourceAdministrativeCategory ≡ true
    cashIncomeIsSovereignMeasureOfWellbeing : Bool
    cashIncomeIsSovereignMeasureOfWellbeingIsFalse :
      cashIncomeIsSovereignMeasureOfWellbeing ≡ false
    commodityFormIsNeutralUniversalOntology : Bool
    commodityFormIsNeutralUniversalOntologyIsFalse :
      commodityFormIsNeutralUniversalOntology ≡ false
    preferredDomainVocabulary : String

open CountryRelationVocabularyBoundary public

canonicalCountryRelationVocabularyBoundary : CountryRelationVocabularyBoundary
canonicalCountryRelationVocabularyBoundary =
  country-relation-vocabulary-boundary
    false refl
    false refl
    true refl
    false refl
    false refl
    "Country; collective authority; relation; obligation; stewardship; material reproduction; ecological and cultural continuity. Property/asset/commodity terms are source- or regime-specific observers, not the default ontology."

------------------------------------------------------------------------
-- Intersectionality is not one frozen fixed-axis technique.
------------------------------------------------------------------------

intersectionalBoundary : Intersectional.IntersectionalPowerValueFolkModelBoundary
intersectionalBoundary = Intersectional.canonicalIntersectionalPowerValueFolkModelBoundary

mccallStrategyBoundary : McCall.CategoryStrategyBoundary
mccallStrategyBoundary = McCall.canonicalCategoryStrategyBoundary

allIntersectionalMethodsUseFixedAxesIsFalse :
  McCall.allIntersectionalMethodsUseFixedAxes mccallStrategyBoundary ≡ false
allIntersectionalMethodsUseFixedAxesIsFalse = refl

------------------------------------------------------------------------
-- Anti-Lacanian/feminist noncollapse: representation is not subjecthood.
------------------------------------------------------------------------

trinhPublicCategoryDoesNotRecoverBecoming :
  INF.FactorsThrough Trinh.publicCategory Trinh.subjectFormation → ⊥
trinhPublicCategoryDoesNotRecoverBecoming =
  Trinh.publicCategoryCannotRecoverSubjectFormation

butlerPresentCategoryDoesNotRecoverGenesis :
  INF.FactorsThrough Butler.presentCategory Butler.genesis → ⊥
butlerPresentCategoryDoesNotRecoverGenesis =
  Butler.presentCategoryCannotRecoverGenesis

lugonesPurityFactorisationBlocked : Lugones.PureEndpointFactorisation → ⊥
lugonesPurityFactorisationBlocked = Lugones.curdledWitnessBlocksPureEndpointFactorisation

------------------------------------------------------------------------
-- Difference and observer approval are not hierarchy or realised affordance.
------------------------------------------------------------------------

differenceNeedNotCreateHierarchy :
  Difference.DifferenceWithEqualStanding Difference.modeObserver Difference.modeStanding
differenceNeedNotCreateHierarchy = Difference.canonicalDifferenceWithEqualStanding

inclusiveRhetoricDoesNotDetermineMaterialAccessibility :
  INF.FactorsThrough Ecology.feministObserver Ecology.realizedRemain → ⊥
inclusiveRhetoricDoesNotDetermineMaterialAccessibility =
  Ecology.inclusiveReadingCannotRecoverRealizedAffordance

------------------------------------------------------------------------
-- Haraway/category-authority firewall: there is no view from nowhere.
------------------------------------------------------------------------

formalCarrierIsNotEpistemicallyPositionless :
  Haraway.formalCarrierIsEpistemicallyPositionless
    Haraway.canonicalSituatedFormalisationBoundary ≡ false
formalCarrierIsNotEpistemicallyPositionless = refl

administrativeAuthorityDoesNotImplyContestability :
  Contestability.administrativeAuthorityImpliesPoliticalContestability
    Contestability.canonicalPoliticalAuthorityBoundary ≡ false
administrativeAuthorityDoesNotImplyContestability = refl

recognitionDoesNotConstituteAuthorityByDefault :
  Recognition.recognitionConstitutesAuthorityByDefault
    Recognition.canonicalRecognitionConstitutionBoundary ≡ false
recognitionDoesNotConstituteAuthorityByDefault = refl

------------------------------------------------------------------------
-- Amalek/terminalisation: special correction-closure risk, not a human label.
------------------------------------------------------------------------

amalekBoundary : Amalek.AmalekAuthorityProjectionBoundary
amalekBoundary = Amalek.canonicalAmalekAuthorityProjectionBoundary

amalekClosedAuthorityRisk : Amalek.ClosedAuthorityLoop
amalekClosedAuthorityRisk = Amalek.canonicalClosedAuthorityRisk

amalekCorrectionChannelIsNotIndependentInClosedLoop :
  Amalek.correctionChannelIndependent Amalek.canonicalClosedAuthorityRisk ≡ false
amalekCorrectionChannelIsNotIndependentInClosedLoop = refl

terminalisationMayCloseCorrectionChannel :
  Compression.terminalisationMayCloseCorrectionChannel
    Compression.canonicalTerminalisationRiskBoundary ≡ true
terminalisationMayCloseCorrectionChannel = refl

humanGroupCannotBePromotedToTerminalEnemyPredicate :
  Compression.humanGroupMayBePromotedToTerminalEnemyPredicate
    Compression.canonicalTerminalisationRiskBoundary ≡ false
humanGroupCannotBePromotedToTerminalEnemyPredicate = refl

indigenousAustraliaAmalekComparisonRemainsStructuralOnly :
  EnemyCompression.comparisonAuthority EnemyCompression.indigenousAustraliaSettlerStructure
  ≡ EnemyCompression.structuralHomologyOnly
indigenousAustraliaAmalekComparisonRemainsStructuralOnly = refl

------------------------------------------------------------------------
-- Plumwood: domination operations stay differentiated.
------------------------------------------------------------------------

plumwoodBoundary : Plumwood.MasterModelOperationBoundary
plumwoodBoundary = Plumwood.canonicalMasterModelOperationBoundary

oneMasterModelOperationDoesNotImplyAll :
  Plumwood.presenceOfOneOperationImpliesAllOthers plumwoodBoundary ≡ false
oneMasterModelOperationDoesNotImplyAll = refl

------------------------------------------------------------------------
-- Explicit invisibility audits.
------------------------------------------------------------------------

crownInvisibilityAudit : Compression.InvisibilityAudit
crownInvisibilityAudit = Compression.invisibility-audit
  "Crown recognition"
  "two cross-order states share the same recognition surface"
  "independent Country/community authority"
  "cross-order sovereignty/authority consumer"
  "Country/community authority and relation must remain an independent coordinate"
  true
  "decolonial recognition audit"
  false refl

cashIncomeInvisibilityAudit : Compression.InvisibilityAudit
cashIncomeInvisibilityAudit = Compression.invisibility-audit
  "cash income"
  "two land-relation states share the same cash-income surface"
  "collective land security and decision authority"
  "LAND BACK material/relational consumer"
  "collective authority, distribution, cultural continuity, ecology and externality coordinates"
  false
  "anti-capitalist / communist material-relation audit"
  false refl

biaInvisibilityAudit : Compression.InvisibilityAudit
biaInvisibilityAudit = Compression.invisibility-audit
  "BIA administrative 'trust asset' category"
  "two stewardship states share the same administrative category"
  "non-extractive stewardship value and relation"
  "stewardship / ecological / cultural consumer"
  "stewardship relation must remain independently represented"
  true
  "decolonial + anti-capitalist commodity-form audit"
  false refl

------------------------------------------------------------------------
-- No-collapse / anti-synthesis boundary.
------------------------------------------------------------------------

data CountryRelationEqualsAssetByDefault : Set where
data AntiCapitalistCritiqueMeansEveryMetricIsUseless : Set where
data CommunistAuditProvesInstitutionalIntent : Set where
data FeministTheoryEqualsIndigenousSovereigntyTheory : Set where
data IntersectionalityEqualsAmalekTerminalisation : Set where
data AmalekTerminalisationEqualsOrdinaryProjectionLoss : Set where
data SharedMathematicsTransfersHistoricalAuthorship : Set where

countryRelationDoesNotDefaultToAssetOntology : CountryRelationEqualsAssetByDefault → ⊥
countryRelationDoesNotDefaultToAssetOntology ()

antiCapitalistCritiqueDoesNotMakeEveryMetricUseless :
  AntiCapitalistCritiqueMeansEveryMetricIsUseless → ⊥
antiCapitalistCritiqueDoesNotMakeEveryMetricUseless ()

communistAuditDoesNotProveInstitutionalIntent : CommunistAuditProvesInstitutionalIntent → ⊥
communistAuditDoesNotProveInstitutionalIntent ()

feministAndIndigenousTheoriesDoNotMergeByFormalSimilarity :
  FeministTheoryEqualsIndigenousSovereigntyTheory → ⊥
feministAndIndigenousTheoriesDoNotMergeByFormalSimilarity ()

intersectionalityDoesNotEqualTerminalisation :
  IntersectionalityEqualsAmalekTerminalisation → ⊥
intersectionalityDoesNotEqualTerminalisation ()

amalekIsStrongerThanOrdinaryProjectionLoss :
  AmalekTerminalisationEqualsOrdinaryProjectionLoss → ⊥
amalekIsStrongerThanOrdinaryProjectionLoss ()

sharedMathematicsDoesNotTransferAuthorship :
  SharedMathematicsTransfersHistoricalAuthorship → ⊥
sharedMathematicsDoesNotTransferAuthorship ()
