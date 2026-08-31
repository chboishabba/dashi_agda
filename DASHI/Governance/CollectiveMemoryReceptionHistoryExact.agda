module DASHI.Governance.CollectiveMemoryReceptionHistoryExact where

------------------------------------------------------------------------
-- COLLECTIVE MEMORY / INTELLECTUAL RECEPTION HISTORY
--
-- Cross-pollinates the merged collective-threshold owner into a generic
-- reception-history carrier:
--
--   source proposition
--   -> reception
--   -> institutionalisation
--   -> later vocabulary
--   -> present use.
--
-- Transmission can preserve a term, slogan or conceptual marker while changing
-- meaning, authority, institutional carrier or practical role.  Terminological
-- continuity therefore does not prove semantic or institutional continuity.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.SexedHistoricalCollectiveThresholdNetworkExact as Collective

------------------------------------------------------------------------
-- 1. Reception-history carrier.
------------------------------------------------------------------------

data ReceptionMode : Set where
  directReception
  selectiveReception
  criticalReinterpretation
  polemicalReversal
  archivalRecovery
  unresolvedReception
  : ReceptionMode

data InstitutionalisationStatus : Set where
  notInstitutionalised
  locallyInstitutionalised
  broadlyInstitutionalised
  laterDiscontinued
  reintroducedElsewhere
  : InstitutionalisationStatus

data SemanticRelation : Set where
  meaningRetained
  meaningNarrowed
  meaningExpanded
  meaningReversed
  meaningHybridised
  meaningUnresolved
  : SemanticRelation

data AuthorityRelation : Set where
  sourceAuthorityRetained
  sourceAuthorityQualified
  newAuthorityIntroduced
  authorityDisputed
  authorityAbsent
  : AuthorityRelation

record ReceptionHistoryState : Set where
  constructor reception-history-state
  field
    sourceProposition : String
    reception : ReceptionMode
    institutionalisation : InstitutionalisationStatus
    collectiveMemory : Collective.MemoryStatus
    laterVocabulary : String
    semanticRelation : SemanticRelation
    authorityRelation : AuthorityRelation
    presentUse : String

open ReceptionHistoryState public

------------------------------------------------------------------------
-- 2. Same transmitted vocabulary can encode different semantic histories.
------------------------------------------------------------------------

data VocabularyFineState : Set where
  retainedMeaningHistory
  reversedMeaningHistory
  : VocabularyFineState

vocabularySurface : VocabularyFineState → String
vocabularySurface _ = "shared inherited term"

semanticHistory : VocabularyFineState → SemanticRelation
semanticHistory retainedMeaningHistory = meaningRetained
semanticHistory reversedMeaningHistory = meaningReversed

sameVocabularyCannotRecoverSemanticHistory :
  INF.FactorsThrough vocabularySurface semanticHistory → ⊥
sameVocabularyCannotRecoverSemanticHistory =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      retainedMeaningHistory
      reversedMeaningHistory
      refl
      (λ ()))

------------------------------------------------------------------------
-- 3. Same present vocabulary can also arise with different institutional
--    continuity histories.
------------------------------------------------------------------------

data InstitutionalFineState : Set where
  vocabularyWithInstitutionalContinuity
  vocabularyAfterInstitutionalBreak
  : InstitutionalFineState

institutionalVocabularySurface : InstitutionalFineState → String
institutionalVocabularySurface _ = "same present vocabulary"

institutionalHistory : InstitutionalFineState → InstitutionalisationStatus
institutionalHistory vocabularyWithInstitutionalContinuity = broadlyInstitutionalised
institutionalHistory vocabularyAfterInstitutionalBreak = reintroducedElsewhere

sameVocabularyCannotRecoverInstitutionalHistory :
  INF.FactorsThrough institutionalVocabularySurface institutionalHistory → ⊥
sameVocabularyCannotRecoverInstitutionalHistory =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      vocabularyWithInstitutionalContinuity
      vocabularyAfterInstitutionalBreak
      refl
      (λ ()))

------------------------------------------------------------------------
-- 4. Same present use does not recover source authority.
------------------------------------------------------------------------

data PresentUseFineState : Set where
  useWithSourceAuthority
  useWithNewAuthority
  : PresentUseFineState

presentUseSurface : PresentUseFineState → String
presentUseSurface _ = "same present practical use"

authorityHistory : PresentUseFineState → AuthorityRelation
authorityHistory useWithSourceAuthority = sourceAuthorityRetained
authorityHistory useWithNewAuthority = newAuthorityIntroduced

presentUseCannotRecoverAuthorityHistory :
  INF.FactorsThrough presentUseSurface authorityHistory → ⊥
presentUseCannotRecoverAuthorityHistory =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      useWithSourceAuthority
      useWithNewAuthority
      refl
      (λ ()))

------------------------------------------------------------------------
-- 5. Positive transport is possible, but must be receipt-bearing.
------------------------------------------------------------------------

record ReceptionContinuityReceipt : Set where
  constructor reception-continuity-receipt
  field
    sourceLocated : Bool
    transmissionRouteLocated : Bool
    semanticComparisonPerformed : Bool
    institutionalRouteLocated : Bool
    authorityTransportLocated : Bool
    boundedReading : String

open ReceptionContinuityReceipt public

fullContinuityReceipt : ReceptionContinuityReceipt
fullContinuityReceipt =
  reception-continuity-receipt true true true true true
    "A positive continuity claim needs source, transmission, semantic, institutional and authority receipts; this finite object does not assert any named historical continuity by itself."

------------------------------------------------------------------------
-- 6. Retain merged #658's collective-memory boundary directly.
------------------------------------------------------------------------

mergedCollectiveMemoryDoesNotEqualInstitutionalContinuity :
  Collective.transmittedMemoryEqualsInstitutionalContinuity
    Collective.canonicalSexedHistoricalCollectiveThresholdBoundary
  ≡ false
mergedCollectiveMemoryDoesNotEqualInstitutionalContinuity = refl

------------------------------------------------------------------------
-- 7. No-promotion boundary.
------------------------------------------------------------------------

data TransmittedTermPromotesOriginalMeaning : Set where

data SharedVocabularyPromotesInstitutionalContinuity : Set where

data PresentUsePromotesOriginalAuthority : Set where

data ReceptionPromotesSourceEndorsement : Set where

data SemanticResemblancePromotesDirectGenealogy : Set where

transmittedTermDoesNotPromoteOriginalMeaning :
  TransmittedTermPromotesOriginalMeaning → ⊥
transmittedTermDoesNotPromoteOriginalMeaning ()

sharedVocabularyDoesNotPromoteInstitutionalContinuity :
  SharedVocabularyPromotesInstitutionalContinuity → ⊥
sharedVocabularyDoesNotPromoteInstitutionalContinuity ()

presentUseDoesNotPromoteOriginalAuthority :
  PresentUsePromotesOriginalAuthority → ⊥
presentUseDoesNotPromoteOriginalAuthority ()

receptionDoesNotPromoteSourceEndorsement :
  ReceptionPromotesSourceEndorsement → ⊥
receptionDoesNotPromoteSourceEndorsement ()

semanticResemblanceDoesNotPromoteDirectGenealogy :
  SemanticResemblancePromotesDirectGenealogy → ⊥
semanticResemblanceDoesNotPromoteDirectGenealogy ()

record CollectiveMemoryReceptionBoundary : Set where
  constructor collective-memory-reception-boundary
  field
    vocabularyContinuityEqualsMeaningContinuity : Bool
    vocabularyContinuityEqualsInstitutionalContinuity : Bool
    presentUseRecoversOriginalAuthority : Bool
    receptionImpliesEndorsement : Bool
    semanticResemblanceProvesDirectGenealogy : Bool
    positiveContinuityMayBeReceiptBearing : Bool
    collectiveMemoryRetainsInstitutionalNoncollapse : Bool

canonicalCollectiveMemoryReceptionBoundary : CollectiveMemoryReceptionBoundary
canonicalCollectiveMemoryReceptionBoundary =
  collective-memory-reception-boundary false false false false false true true
