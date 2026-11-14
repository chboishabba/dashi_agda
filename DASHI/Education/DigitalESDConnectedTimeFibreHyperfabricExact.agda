module DASHI.Education.DigitalESDConnectedTimeFibreHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.PNFHyperfabric369 as Fabric
import DASHI.Biology.AliceBrownCorpusLoom as Alice
import DASHI.Biology.AliceBrownTemporalDiagnosisDependencyLineageBidiExact as Lineage
import DASHI.Education.DigitalESDReciprocalBraidExact as ESD
import DASHI.Education.DigitalESDEfSIndependentDerivationExact as EfS
import DASHI.Education.DigitalESDEfSSourceCrossPollinationExact as Cross
import DASHI.Education.DigitalESDPrincipleSurvivalAuditExact as Survival
import DASHI.Education.DigitalESDManuscriptMethodologyExact as Method
import DASHI.Core.QueryFactorisationSufficiency as Sufficiency
import DASHI.Core.IntersectionalNonFactorability as Intersection

-- Thin, source-preserving composition on the existing hyperfabric.
-- A source-bound observation at time t is NOT a truth claim about all later
-- times, other contexts, students, communities or ecological systems.
-- The two manuscript directions are consumers of the same temporal fabric.
-- No new underlying memory/learning/trauma calculus is introduced here.

data InquiryDirection : Set where
  retrospectiveESDAndEfSAudit : InquiryDirection
  prospectiveResearchDesign : InquiryDirection

data SituatedObserver : Set where
  learner : SituatedObserver
  educator : SituatedObserver
  researcher : SituatedObserver
  institution : SituatedObserver
  community : SituatedObserver
  ecologicalIndicator : SituatedObserver

data EvidenceStatus : Set where
  sourceBoundObservation : EvidenceStatus
  crossPaperCandidate : EvidenceStatus
  independentlyReviewed : EvidenceStatus
  unresolved : EvidenceStatus

record TemporalSourceFibre : Set where
  constructor temporal-source-fibre
  field
    sourceIdentity : String
    context : String
    time : Nat
    observer : SituatedObserver
    reportedObservation : String
    role : EvidenceStatus
    claimCeiling : String
    historicalProvenance : String

open TemporalSourceFibre public

-- Reinterpretation never overwrites the original event/source fibre.
-- Revisit by appending a new source-and-time-indexed observation.
record SourcePreservingRevision (original revision : TemporalSourceFibre) : Set where
  constructor source-preserving-revision
  field
    originalSourceRetained : sourceIdentity original ≡ sourceIdentity original
    originalTimeRetained : time original ≡ time original
    revisionIsDistinctObservation : Bool
    revisionIsDistinctObservationIsTrue : revisionIsDistinctObservation ≡ true

canonicalSourcePreservingRevision :
  (original revision : TemporalSourceFibre) →
  SourcePreservingRevision original revision
canonicalSourcePreservingRevision original revision =
  source-preserving-revision refl refl true refl


-- A stronger, evidence-demanding revision relation. Unlike the earlier
-- reflexive SourcePreservingRevision receipt, this cannot be constructed
-- for two arbitrary fibres: source identity must match and time advances.
-- Consequence invalidation remains the responsibility of the existing
-- temporal diagnosis/dependency-lineage owner and must be linked separately.
record HistoricalRevisionDependency
  (original revision : TemporalSourceFibre) : Set where
  constructor historical-revision-dependency
  field
    sameHistoricalSource : sourceIdentity revision ≡ sourceIdentity original
    elapsedAfterOriginal : Nat
    revisionTimeAdvances :
      time revision ≡ suc (time original + elapsedAfterOriginal)

open HistoricalRevisionDependency public

-- A scholarly reader must keep candidate interpretation separate from
-- admitted study findings.  The policy is a typed relation, not a proof that
-- a source is relevant, an intervention effective, or a cohort sampled.
data MayPromoteToReviewed : EvidenceStatus → Set where
  reviewedOnly : MayPromoteToReviewed independentlyReviewed

candidateNotAutomaticallyReviewed :
  MayPromoteToReviewed crossPaperCandidate → ⊥
candidateNotAutomaticallyReviewed ()

unresolvedNotAutomaticallyReviewed :
  MayPromoteToReviewed unresolved → ⊥
unresolvedNotAutomaticallyReviewed ()

record ConnectedDigitalESDTimeHyperfabric : Set₂ where
  constructor connected-digital-esd-time-hyperfabric
  field
    canonicalFabric : Fabric.PNFHyperfabric369Surface
    canonicalAliceSourceLoom : Alice.AliceBrownCorpusLoom
    temporalAliceDiagnosis : Lineage.AliceBrownTemporalDiagnosisBoundary
    canonicalESDReciprocity : ESD.DigitalESDReciprocalBraid

    -- EfS remains independently derived before comparison to digital strands.
    independentEfS : EfS.IndependentThemeReceipt
    efsCandidateSource : Cross.CrossPollinationCase
    principleSurvival : Survival.PrincipleSurvivalReceipt

    -- The five detailed manuscript questions remain canonical; the two
    -- public-facing directions are projections/consumers of that study.
    canonicalResearchQuestion : Method.ManuscriptResearchQuestion
    retrospectiveQuestion : InquiryDirection
    prospectiveQuestion : InquiryDirection

    -- At time t, each observer is an independent fibre; a later observation
    -- is another fibre, not a destructive mutation of the earlier source.
    observationsAt : Nat → SituatedObserver → TemporalSourceFibre

    sourceIdentityAt : Nat → SituatedObserver → String
    sourceIdentityAtPreserved : (t : Nat) (who : SituatedObserver) →
      sourceIdentityAt t who ≡ sourceIdentity (observationsAt t who)

    timeIndexIsPreserved : (t : Nat) (who : SituatedObserver) →
      time (observationsAt t who) ≡ t

    interpretationsAreReviewedFindings : Bool
    interpretationsAreReviewedFindingsIsFalse :
      interpretationsAreReviewedFindings ≡ false

    allObserverFibresInterchangeable : Bool
    allObserverFibresInterchangeableIsFalse :
      allObserverFibresInterchangeable ≡ false

open ConnectedDigitalESDTimeHyperfabric public

-- The canonical evidence objects are supplied from their existing owners.
-- Constructed observations require concrete source/context inputs from the
-- research ledger; this file deliberately does not fabricate them.
canonicalFabricOwner : Fabric.PNFHyperfabric369Surface
canonicalFabricOwner = Fabric.canonicalPNFHyperfabric369Surface

canonicalAliceOwner : Alice.AliceBrownCorpusLoom
canonicalAliceOwner = Alice.canonicalAliceBrownCorpusLoom

canonicalTemporalLineageOwner : Lineage.AliceBrownTemporalDiagnosisBoundary
canonicalTemporalLineageOwner = Lineage.canonicalAliceBrownTemporalDiagnosisBoundary

canonicalReciprocalOwner : ESD.DigitalESDReciprocalBraid
canonicalReciprocalOwner = ESD.canonicalDigitalESDReciprocalBraid

-- Expose existing source-level non-factorability and query sufficiency
-- theorems rather than rebuilding them as ESD-specific mathematics.
querySufficiencyIsRelative :
  {State Surface Query : Set}
  (questions : Sufficiency.InquiryQuestionFamily State Query)
  (projection : State → Surface)
  (question : Query) →
  Sufficiency.FactorsThrough questions projection question →
  Sufficiency.FactorsThrough questions projection question
querySufficiencyIsRelative questions projection question witness = witness

coarseAgendaStillInsufficient :
  Intersection.FactorsThrough ESD.coarseAgendaObservation ESD.braidAdequacy → ⊥
coarseAgendaStillInsufficient =
  ESD.coarseAgendaCannotDetermineReciprocalBraidAdequacy

-- Explicit boundaries: time-indexed composition is not empirical validation.
data FabricImpliesSustainabilityEffect : Set where
data SourceLoomGrantsLearnerAuthority : Set where
data EcologicalIndicatorSpeaksForEcology : Set where

noEffectPromotion : FabricImpliesSustainabilityEffect → ⊥
noEffectPromotion ()

noAuthorityPromotion : SourceLoomGrantsLearnerAuthority → ⊥
noAuthorityPromotion ()

noEcologicalVoicePromotion : EcologicalIndicatorSpeaksForEcology → ⊥
noEcologicalVoicePromotion ()
