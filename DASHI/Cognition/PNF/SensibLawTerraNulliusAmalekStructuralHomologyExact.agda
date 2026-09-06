module DASHI.Cognition.PNF.SensibLawTerraNulliusAmalekStructuralHomologyExact where

------------------------------------------------------------------------
-- TERRA NULLIUS / AMALEK STRUCTURAL HOMOLOGY
--
-- This is a strictly bounded comparison owner.
--
-- It does NOT assert:
--   * that Australian settlers historically called Indigenous Australians
--     "Amalek";
--   * that Mabo held Indigenous people were literally non-human;
--   * that the biblical/theological narrative and Australian colonial law are
--     historically identical;
--   * that any human population may inhabit the repository's Amalek predicate.
--
-- The permitted comparison is structural: a dominant order can make an
-- antecedent subject/order illegible to its own normative categories, treat the
-- resulting absence as confirmation of its own authority, and act on that
-- projection. Amalek adds the stronger terminalisation/correction-closure risk.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawNativeTitleRecognitionCriticalSourceAtlasExact as Sources
import DASHI.Culture.AmalekAuthorityProjectionBoundary as Amalek
import DASHI.Physics.Foundations.SettlerEnemyAbstractionExact as Settler
import DASHI.Core.DominantChartEpistemicCompressionExact as Compression

------------------------------------------------------------------------
-- Distinct feature spaces.
------------------------------------------------------------------------

data TerraNulliusFeature : Set where
  antecedentLawMadeIllegible
  antecedentLandRightsMadeIllegible
  dominantRecognitionDefinesLegibility
  socialOrganisationDevalued
  colonialPossessionEnabledByNonRecognition
  : TerraNulliusFeature

data AmalekOperatorFeature : Set where
  terminalEnemyProduction
  authoritySelfValidation
  externalCorrectionDelegitimation
  dissentAsConfirmingFault
  humanPollutantProjectionRisk
  : AmalekOperatorFeature

data ComparisonStrength : Set where
  noComparison
  structuralHomologyOnly
  historicalLineageEstablished
  doctrinalIdentityEstablished
  : ComparisonStrength

record StructuralHomologyReceipt : Set where
  constructor structural-homology-receipt
  field
    comparisonReference : String
    terraNulliusSource : Sources.LayeredClaimReceipt
    comparisonStrength : ComparisonStrength
    criticalComparisonAllowed : Bool
    criticalComparisonAllowedIsTrue : criticalComparisonAllowed ≡ true
    literalHistoricalLineage : Bool
    literalHistoricalLineageIsFalse : literalHistoricalLineage ≡ false
    sameDoctrine : Bool
    sameDoctrineIsFalse : sameDoctrine ≡ false
    historicalAmalekLexicalUseInAustraliaEstablished : Bool
    historicalAmalekLexicalUseInAustraliaEstablishedIsFalse :
      historicalAmalekLexicalUseInAustraliaEstablished ≡ false
    courtHoldingSaysIndigenousPeopleLiterallyNonHuman : Bool
    courtHoldingSaysIndigenousPeopleLiterallyNonHumanIsFalse :
      courtHoldingSaysIndigenousPeopleLiterallyNonHuman ≡ false
    humanGroupMayInhabitAmalekPredicate : Bool
    humanGroupMayInhabitAmalekPredicateIsFalse :
      humanGroupMayInhabitAmalekPredicate ≡ false
    dehumanisationIsCriticalInterpretation : Bool
    dehumanisationIsCriticalInterpretationIsTrue :
      dehumanisationIsCriticalInterpretation ≡ true

open StructuralHomologyReceipt public

canonicalTerraNulliusAmalekHomology : StructuralHomologyReceipt
canonicalTerraNulliusAmalekHomology = structural-homology-receipt
  "DASHI/SensibLaw structural comparison: exclusion from the dominant order's legibility can erase antecedent rights/authority; terminalisation is the stronger case where correction itself is closed or converted into fault"
  Sources.maboRejectsEnlargedTerraNullius
  structuralHomologyOnly
  true refl
  false refl
  false refl
  false refl
  false refl
  false refl
  true refl

------------------------------------------------------------------------
-- Existing Amalek and settler boundaries stay authoritative for the comparison.
------------------------------------------------------------------------

amalekClosedLoop : Amalek.ClosedAuthorityLoop
amalekClosedLoop = Amalek.canonicalClosedAuthorityRisk

closedLoopSelfValidatesAuthority :
  Amalek.authoritySelfValidates amalekClosedLoop ≡ true
closedLoopSelfValidatesAuthority = refl

closedLoopDelegitimisesExternalEvidence :
  Amalek.externalEvidenceDelegitimised amalekClosedLoop ≡ true
closedLoopDelegitimisesExternalEvidence = refl

closedLoopHasNoIndependentCorrection :
  Amalek.correctionChannelIndependent amalekClosedLoop ≡ false
closedLoopHasNoIndependentCorrection = refl

australianComparisonPreviouslyStructuralOnly :
  Settler.comparisonAuthority Settler.indigenousAustraliaSettlerStructure
  ≡ Settler.structuralHomologyOnly
australianComparisonPreviouslyStructuralOnly = refl

humanGroupPromotionBlocked :
  Compression.humanGroupMayBePromotedToTerminalEnemyPredicate
    Compression.canonicalTerminalisationRiskBoundary ≡ false
humanGroupPromotionBlocked = refl

------------------------------------------------------------------------
-- Terra-nullius dehumanisation is a critical synthesis receipt, not Mabo text.
------------------------------------------------------------------------

terraNulliusDehumanisationReceipt : Sources.LayeredClaimReceipt
terraNulliusDehumanisationReceipt = Sources.terraNulliusDehumanisationCriticalSynthesis

terraNulliusDehumanisationLayerIsSynthesis :
  Sources.layer terraNulliusDehumanisationReceipt ≡ Sources.dashCriticalSynthesis
terraNulliusDehumanisationLayerIsSynthesis = refl

terraNulliusDehumanisationNotDirectMaboStatement :
  Sources.sourceSaysThisDirectly terraNulliusDehumanisationReceipt ≡ false
terraNulliusDehumanisationNotDirectMaboStatement = refl

------------------------------------------------------------------------
-- Deep distinction: ordinary exclusion/compression != terminalisation.
------------------------------------------------------------------------

record ExclusionTerminalisationBoundary : Set where
  constructor exclusion-terminalisation-boundary
  field
    nonRecognitionCanEraseLegibility : Bool
    nonRecognitionCanEraseLegibilityIsTrue : nonRecognitionCanEraseLegibility ≡ true
    everyLegibilityFailureIsTerminalisation : Bool
    everyLegibilityFailureIsTerminalisationIsFalse : everyLegibilityFailureIsTerminalisation ≡ false
    terminalisationAddsCorrectionClosureRisk : Bool
    terminalisationAddsCorrectionClosureRiskIsTrue : terminalisationAddsCorrectionClosureRisk ≡ true
    structuralHomologyTransfersMoralOrHistoricalIdentity : Bool
    structuralHomologyTransfersMoralOrHistoricalIdentityIsFalse :
      structuralHomologyTransfersMoralOrHistoricalIdentity ≡ false

open ExclusionTerminalisationBoundary public

canonicalExclusionTerminalisationBoundary : ExclusionTerminalisationBoundary
canonicalExclusionTerminalisationBoundary = exclusion-terminalisation-boundary
  true refl false refl true refl false refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data TerraNulliusEqualsAmalekDoctrine : Set where
data TerraNulliusHistoricallyUsedAmalekLexeme : Set where
data MaboHeldIndigenousPeopleNonHuman : Set where
data DehumanisationInterpretationIsCourtAuthorship : Set where
data StructuralHomologyLicencesHumanEnemyPredicate : Set where
data SettlerColonialismEqualsGenocideInEveryInstance : Set where

terraNulliusDoesNotEqualAmalekDoctrine : TerraNulliusEqualsAmalekDoctrine → ⊥
terraNulliusDoesNotEqualAmalekDoctrine ()

noLexicalLineageInvented : TerraNulliusHistoricallyUsedAmalekLexeme → ⊥
noLexicalLineageInvented ()

maboDidNotHoldLiteralNonHumanClaim : MaboHeldIndigenousPeopleNonHuman → ⊥
maboDidNotHoldLiteralNonHumanClaim ()

deHumanisationInterpretationDoesNotBecomeCourtAuthorship :
  DehumanisationInterpretationIsCourtAuthorship → ⊥
deHumanisationInterpretationDoesNotBecomeCourtAuthorship ()

homologyDoesNotLicenceHumanEnemyPredicate :
  StructuralHomologyLicencesHumanEnemyPredicate → ⊥
homologyDoesNotLicenceHumanEnemyPredicate ()

settlerColonialismDoesNotEqualGenocideEverywhere :
  SettlerColonialismEqualsGenocideInEveryInstance → ⊥
settlerColonialismDoesNotEqualGenocideEverywhere ()
