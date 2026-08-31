module DASHI.Culture.PhilosophyClaimProvenanceHistoryBidiExact where

------------------------------------------------------------------------
-- PHILOSOPHY CLAIM / PROVENANCE / HISTORY BIDI
--
-- This owner makes the repository source-attribution discipline proof-visible.
-- It consumes canonical merged machinery; it does not create a new doctrine.
--
-- Core invariant:
--
--   primary-source proposition
--   != later interpretation
--   != cross-domain analogy
--   != DASHI formal pattern
--   != finite DASHI theorem
--   != empirical population claim.
--
-- The finite non-factorability witnesses below are DASHI constructions.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.GovernedObservationProvenanceExact as Governed
import DASHI.Core.HistoryQualifiedSelectionTopologyExact as History
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Culture.WittgensteinUsePracticeSourceBridgeExact as Wittgenstein
import DASHI.Culture.HistoricalTotalityCriticalTheoryCrossPollinationExact as Critical
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as Indigenous

------------------------------------------------------------------------
-- 1. Attribution layer and source role are independent coordinates.
------------------------------------------------------------------------

data PhilosophyClaimLayer : Set where
  primarySourceLayer
  secondaryInterpretationLayer
  comparativeBridgeLayer
  reusablePatternLayer
  finiteDASHITheoremLayer
  empiricalClaimLayer
  : PhilosophyClaimLayer

data PhilosophyEvidenceRole : Set where
  primaryTextRole
  secondaryScholarshipRole
  empiricalStudyRole
  historicalArchiveRole
  participantTestimonyRole
  legalAuthorityRole
  repositoryConstructionRole
  unresolvedRole
  : PhilosophyEvidenceRole

record PhilosophyClaimReceipt : Set where
  constructor philosophy-claim-receipt
  field
    authorOrTradition : String
    workOrSource : String
    sourceLocation : String
    naturalLanguageClaim : String
    layer : PhilosophyClaimLayer
    evidenceRole : PhilosophyEvidenceRole
    historicalScope : String
    populationScope : String
    interpretiveScope : String
    provenance : String
    sourceRecovered : Bool
    exactLocationRecovered : Bool
    empiricalAuthority : Bool
    dashITheoremAttributedToSource : Bool

open PhilosophyClaimReceipt public

------------------------------------------------------------------------
-- 2. Same surviving wording cannot recover attribution history.
------------------------------------------------------------------------

data ClaimHistoryState : Set where
  sourceOccurrence
  secondaryParaphrase
  repositoryAnalogy
  repositoryFiniteTheorem
  : ClaimHistoryState

data SharedWordingSurface : Set where sameWording : SharedWordingSurface

data ClaimHistoryCode : Set where
  sourceCode secondaryCode analogyCode theoremCode : ClaimHistoryCode

wordingSurface : ClaimHistoryState → SharedWordingSurface
wordingSurface _ = sameWording

claimHistory : ClaimHistoryState → ClaimHistoryCode
claimHistory sourceOccurrence = sourceCode
claimHistory secondaryParaphrase = secondaryCode
claimHistory repositoryAnalogy = analogyCode
claimHistory repositoryFiniteTheorem = theoremCode

sourceAndTheoremDiffer :
  claimHistory sourceOccurrence ≡ claimHistory repositoryFiniteTheorem → ⊥
sourceAndTheoremDiffer ()

sameWordingCannotRecoverAttributionHistory :
  INF.FactorsThrough wordingSurface claimHistory → ⊥
sameWordingCannotRecoverAttributionHistory =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sourceOccurrence repositoryFiniteTheorem refl sourceAndTheoremDiffer)

------------------------------------------------------------------------
-- 3. Same philosopher keyword cannot recover exact source proposition.
------------------------------------------------------------------------

data KeywordState : Set where
  wittgensteinUse
  badiouCount
  bookchinHierarchy
  irigarayDifference
  : KeywordState

data GenericRelationWord : Set where relationWord : GenericRelationWord

data ExactRegisterCode : Set where
  wittgensteinRegister
  badiouRegister
  bookchinRegister
  irigarayRegister
  : ExactRegisterCode

genericRelationSurface : KeywordState → GenericRelationWord
genericRelationSurface _ = relationWord

exactRegister : KeywordState → ExactRegisterCode
exactRegister wittgensteinUse = wittgensteinRegister
exactRegister badiouCount = badiouRegister
exactRegister bookchinHierarchy = bookchinRegister
exactRegister irigarayDifference = irigarayRegister

wittgensteinAndBadiouDiffer :
  exactRegister wittgensteinUse ≡ exactRegister badiouCount → ⊥
wittgensteinAndBadiouDiffer ()

sameKeywordCannotRecoverPhilosophicalRegister :
  INF.FactorsThrough genericRelationSurface exactRegister → ⊥
sameKeywordCannotRecoverPhilosophicalRegister =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      wittgensteinUse badiouCount refl wittgensteinAndBadiouDiffer)

------------------------------------------------------------------------
-- 4. PNF decomposition for philosophical/historical claims.
--
-- A philosophical claim may be descriptive about a text, interpretive about
-- a concept, historical about uptake, causal about institutions, or empirical
-- about populations.  Those inferential forces must not be silently merged.
------------------------------------------------------------------------

philosophyClaimScope : PNF.AssertionScope
philosophyClaimScope =
  PNF.assertionScope
    "declared author/tradition or target population"
    "declared historical/social setting"
    "textual, interpretive, institutional or practice relation"
    "declared comparison tradition or null comparator"
    "bounded conceptual, historical or empirical conclusion"
    "declared source/historical interval"

philosophyClaimPredicates : List PNF.PredicateAtom
philosophyClaimPredicates =
  PNF.predicateAtom "source-location" PNF.contextPredicate
    "author × work × edition/location"
    "the proposition is tied to an exact recoverable source location"
  ∷ PNF.predicateAtom "attribution-layer" PNF.authorityPredicate
    "source × interpretation × repository"
    "source authorship is kept distinct from later interpretation and DASHI theorem ownership"
  ∷ PNF.predicateAtom "historical-scope" PNF.temporalPredicate
    "claim × historical interval"
    "a proposition about one period is not silently transported to another"
  ∷ PNF.predicateAtom "population-scope" PNF.populationPredicate
    "claim × persons/groups"
    "textual or theoretical material is not automatically a population law"
  ∷ PNF.predicateAtom "causal-force" PNF.causalPredicate
    "institution × practice × outcome"
    "influence, association and causal determination remain distinct"
  ∷ []

canonicalPhilosophyPNF : PNF.PredicateNormalAssertion
canonicalPhilosophyPNF =
  PNF.predicateNormalAssertion
    "philosophy-source-attribution-audit"
    "A source-bounded philosophical proposition is being transported into a later historical or formal claim."
    PNF.boundedUniversalQ
    PNF.descriptiveF
    philosophyClaimScope
    philosophyClaimPredicates
    "DASHI audit specimen; not a proposition attributed to any philosopher"

------------------------------------------------------------------------
-- 5. Philosophy-specific amplification classes map to canonical PNF deltas.
------------------------------------------------------------------------

data PhilosophyPromotionKind : Set where
  sourceToInterpretation
  localTextToWholeDoctrine
  doctrineToPopulationLaw
  historicalPeriodToPresent
  influenceToDetermination
  practiceToPrivateBelief
  formalSimilarityToSameDoctrine
  sourcePropositionToDASHITheorem
  : PhilosophyPromotionKind

promotionDelta : PhilosophyPromotionKind → PNF.PromotionDelta
promotionDelta sourceToInterpretation = PNF.sameAssertionStrength
promotionDelta localTextToWholeDoctrine = PNF.strengthensQuantifier
promotionDelta doctrineToPopulationLaw = PNF.widensPopulation
promotionDelta historicalPeriodToPresent = PNF.widensContext
promotionDelta influenceToDetermination = PNF.strengthensCausalForce
promotionDelta practiceToPrivateBelief = PNF.strengthensCausalForce
promotionDelta formalSimilarityToSameDoctrine = PNF.strengthensComparativeForce
promotionDelta sourcePropositionToDASHITheorem = PNF.strengthensNormativeForce

record PhilosophyPromotionAudit : Set where
  constructor philosophy-promotion-audit
  field
    kind : PhilosophyPromotionKind
    canonicalDelta : PNF.PromotionDelta
    deltaIsCanonical : canonicalDelta ≡ promotionDelta kind
    independentReceiptRequired : Bool
    sourceAttributionPreserved : Bool

canonicalDoctrineToPopulationAudit : PhilosophyPromotionAudit
canonicalDoctrineToPopulationAudit =
  philosophy-promotion-audit
    doctrineToPopulationLaw PNF.widensPopulation refl true true

canonicalInfluenceToDeterminationAudit : PhilosophyPromotionAudit
canonicalInfluenceToDeterminationAudit =
  philosophy-promotion-audit
    influenceToDetermination PNF.strengthensCausalForce refl true true

------------------------------------------------------------------------
-- 6. Governed provenance lineage: erase then re-add is not restoration.
------------------------------------------------------------------------

philosophyEraseThenAddIsIntroduced :
  Governed.applyTwoEffects
    Governed.erasesCoordinate
    Governed.addsCoordinate
    Governed.inheritedCoordinate
  ≡ Governed.introducedCoordinate
philosophyEraseThenAddIsIntroduced =
  Governed.additionAfterErasureIsIntroducedNotInherited

philosophyEraseThenAddDoesNotRestoreSourceLineage :
  Governed.applyTwoEffects
    Governed.erasesCoordinate
    Governed.addsCoordinate
    Governed.inheritedCoordinate
  ≡ Governed.inheritedCoordinate → ⊥
philosophyEraseThenAddDoesNotRestoreSourceLineage =
  Governed.additionAfterErasureDoesNotRestoreInheritedLineage

------------------------------------------------------------------------
-- 7. History-qualified access: shared intellectual root does not transport
-- admission/authority to a later proposition.
------------------------------------------------------------------------

sharedRootDoesNotRecoverPhilosophicalAdmission :
  INF.FactorsThrough History.sharedRoot History.admissionClass → ⊥
sharedRootDoesNotRecoverPhilosophicalAdmission =
  History.sharedRootCannotRecoverAdmission

------------------------------------------------------------------------
-- 8. Direct canonical cross-pollination receipts.
------------------------------------------------------------------------

record PhilosophyCanonicalWeld : Set where
  constructor philosophy-canonical-weld
  field
    wittgensteinBoundary : Wittgenstein.WittgensteinUsePracticeBoundary
    criticalTheoryBoundary : Critical.HistoricalTotalityCriticalTheoryBoundary
    historySelectionBoundary : History.HistoryQualifiedSelectionBoundary
    governedProvenanceBoundary : Governed.GovernedObservationProvenanceBoundary
    predicateNormalBoundary : PNF.PredicateNormalFormBoundary
    indigenousSourceBoundaryReusedOnlyMethodologically : Bool
    noIndigenousTraditionDefinedByPhilosopherAtlas : Bool
    noPhilosopherSourceOwnsFiniteDASHITheorem : Bool
    noTheorySourcePromotedToEmpiricalPopulationLaw : Bool

canonicalPhilosophyCanonicalWeld : PhilosophyCanonicalWeld
canonicalPhilosophyCanonicalWeld =
  philosophy-canonical-weld
    Wittgenstein.canonicalWittgensteinUsePracticeBoundary
    Critical.canonicalHistoricalTotalityCriticalTheoryBoundary
    History.canonicalHistoryQualifiedSelectionBoundary
    Governed.canonicalGovernedObservationProvenanceBoundary
    PNF.canonicalPredicateNormalFormBoundary
    true true true true

------------------------------------------------------------------------
-- 9. Explicit no-promotion gates.
------------------------------------------------------------------------

data SameKeywordPromotesSameDoctrine : Set where
data SourceTextPromotesPopulationLaw : Set where
data LaterInterpretationPromotesPrimaryAuthorship : Set where
data SharedRootPromotesInheritedAuthority : Set where
data PresentPracticePromotesHistoricalContinuity : Set where
data SimilarFormalPatternPromotesSourceTheoremAuthorship : Set where
data PhilosophyAtlasPromotesIndigenousEpistemicEquivalence : Set where

sameKeywordDoesNotPromoteSameDoctrine : SameKeywordPromotesSameDoctrine → ⊥
sameKeywordDoesNotPromoteSameDoctrine ()

sourceTextDoesNotPromotePopulationLaw : SourceTextPromotesPopulationLaw → ⊥
sourceTextDoesNotPromotePopulationLaw ()

laterInterpretationDoesNotPromotePrimaryAuthorship : LaterInterpretationPromotesPrimaryAuthorship → ⊥
laterInterpretationDoesNotPromotePrimaryAuthorship ()

sharedRootDoesNotPromoteInheritedAuthority : SharedRootPromotesInheritedAuthority → ⊥
sharedRootDoesNotPromoteInheritedAuthority ()

presentPracticeDoesNotPromoteHistoricalContinuity : PresentPracticePromotesHistoricalContinuity → ⊥
presentPracticeDoesNotPromoteHistoricalContinuity ()

similarFormalPatternDoesNotPromoteSourceTheoremAuthorship :
  SimilarFormalPatternPromotesSourceTheoremAuthorship → ⊥
similarFormalPatternDoesNotPromoteSourceTheoremAuthorship ()

philosophyAtlasDoesNotPromoteIndigenousEpistemicEquivalence :
  PhilosophyAtlasPromotesIndigenousEpistemicEquivalence → ⊥
philosophyAtlasDoesNotPromoteIndigenousEpistemicEquivalence ()

------------------------------------------------------------------------
-- 10. Canonical boundary.
------------------------------------------------------------------------

record PhilosophyClaimProvenanceHistoryBoundary : Set where
  constructor philosophy-claim-provenance-history-boundary
  field
    sameWordingDeterminesAttributionHistory : Bool
    sameKeywordDeterminesPhilosophicalRegister : Bool
    sourceTextDeterminesPopulationLaw : Bool
    laterInterpretationBecomesPrimaryAuthorship : Bool
    erasedSourceLineageRestoredByLaterCitation : Bool
    sharedIntellectualRootTransportsAuthority : Bool
    presentPracticeProvesHistoricalContinuity : Bool
    formalSimilarityMeansSameDoctrine : Bool
    philosophyAtlasEqualsIndigenousEpistemology : Bool
    strongerClaimRequiresIndependentReceipt : Bool
    sourceAttributionSurvivesCrossPollination : Bool

canonicalPhilosophyClaimProvenanceHistoryBoundary :
  PhilosophyClaimProvenanceHistoryBoundary
canonicalPhilosophyClaimProvenanceHistoryBoundary =
  philosophy-claim-provenance-history-boundary
    false false false false false false false false false true true
