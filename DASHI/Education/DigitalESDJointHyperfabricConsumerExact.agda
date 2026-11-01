module DASHI.Education.DigitalESDJointHyperfabricConsumerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Education.DigitalESDSourceAuditAdmissionExact as Admission
import DASHI.Education.DigitalESDSLRSourceReviewBridgeExact as Review
import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Education.DigitalESDEvidenceBraidTensionExact as Braid
import DASHI.Education.DigitalESDEfSPedagogicalReciprocityExact as EfS
import DASHI.Education.DigitalESDEfSSourceCrossPollinationExact as Cases
import DASHI.Education.DigitalESDReciprocalBraidExact as Reciprocal
import DASHI.Education.EducationSituatedInvestmentTrajectoryExact as Trajectory
import DASHI.Cognition.PNF.TrialecticMemoryLearningHyperfabricExact as Learning
import DASHI.Environment.LESSituatedSocioEcologicalHyperfabricExact as LES

------------------------------------------------------------------------
-- A THIN HYPERFABRIC CONSUMER, NOT A SECOND SOURCE/EVIDENCE ONTOLOGY.
--
-- Canonical owners:
--   - source provenance and same-locator #1448 candidate cases;
--   - SourceAuditAdmission (indexed by the exact AttributedSource);
--   - SLR exact source revision/span review packet;
--   - study-specific claim ceiling and context transfer;
--   - source-preserving evidence braid and situated learning/LES donors.
--
-- The candidate is a SOURCE-INDEXED HYPEREDGE (not an empirical result).
-- A later joint review requires distinct *existing* source-indexed objects.
-- Neither row count nor a matching title can manufacture those objects.
------------------------------------------------------------------------

-- Reuse Cases.relationFor and Cases.canonicalBraid: no second mapping.

record CandidateJointHyperedge (case : Cases.CrossPollinationCase) : Set where
  constructor candidate-joint-hyperedge
  field
    sourceRole : Snowball.SourceRoleSnowballReceipt (Cases.attributedSource case)
    bridge : EfS.ReciprocalPedagogicalBridge
    bridgeIsExactlyCase :
      bridge ≡ Cases.candidateBridge case
    sourceLocatorIsExactlyCase :
      EfS.EfSSource.exactLocator (EfS.ReciprocalPedagogicalBridge.source bridge)
      ≡ Attr.canonicalURL (Cases.attributedSource case)
    comparison : Braid.TensionReceipt
    relationMatchesSourceBridge :
      Braid.TensionReceipt.relation comparison ≡
        Cases.relationFor (EfS.ReciprocalPedagogicalBridge.status bridge)
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

open CandidateJointHyperedge public

candidateJointHyperedge :
  (case : Cases.CrossPollinationCase) → CandidateJointHyperedge case
candidateJointHyperedge case =
  candidate-joint-hyperedge
    (Cases.sourceRoleReceipt case)
    (Cases.candidateBridge case)
    refl
    (Cases.sameLocator case)
    (Cases.canonicalBraid case)
    refl
    true refl

-- A real evidence-bearing hyperedge cannot be produced from the candidate
-- constructor: it additionally demands the *same source indexed* review
-- and admission artifacts, a source-welded study claim profile and a
-- conditional context-transport receipt. No generic study JSON is a substitute.
record JointReviewHyperedge (case : Cases.CrossPollinationCase) : Set where
  constructor joint-review-hyperedge
  field
    candidate : CandidateJointHyperedge case
    reviewedSourcePacket :
      Review.SLRSourceReviewPacket (Cases.attributedSource case)
    sourceAuditAdmission :
      Admission.SourceAuditAdmission (Cases.attributedSource case)
    studyClaimProfile : Ceiling.StudyClaimProfile
    studyClaimIsSameSource :
      Ceiling.StudyClaimProfile.source studyClaimProfile ≡
        Cases.attributedSource case
    contextTransfer : Reciprocal.ContextTransferAdmission
    explicitlyRetainedTensions : List Braid.TensionReceipt
    claimCeilingStillLimitsSynthesis : Bool
    claimCeilingStillLimitsSynthesisIsTrue :
      claimCeilingStillLimitsSynthesis ≡ true

open JointReviewHyperedge public

-- The two important donor systems remain independent: a psychological
-- representation or ecological planning theorem is not a new study finding.
learningRepresentationDonor :
  Learning.TrialecticMemoryLearningBoundary
learningRepresentationDonor = Learning.canonicalTrialecticMemoryLearningBoundary

situatedEcologyDonor : LES.LESSituatedSocioEcologicalBoundary
situatedEcologyDonor = LES.canonicalLESSituatedSocioEcologicalBoundary

------------------------------------------------------------------------
-- CONSTRUCTIVE HIGHER-ORDER OBSTRUCTION.
--
-- Four synthetic records in each population. All *three pairwise joint
-- frequency tables* are the same. Their three-way parity differs.
-- Thus *even genuinely complete two-axis tables* are insufficient for every
-- three-axis consumer. This is stronger than a single marginal-score warning.
-- It is finite DASHI mathematics, not empirical learner/trauma/ESD data.
------------------------------------------------------------------------

data Population : Set where evenTriple oddTriple : Population
data Slot : Set where slot0 slot1 slot2 slot3 : Slot

record ThreeAxisEpisode : Set where
  constructor episode
  field
    pedagogyPresent : Bool
    learnerDecisionPower : Bool
    ecologyObserved : Bool

open ThreeAxisEpisode public

row : Population → Slot → ThreeAxisEpisode
row evenTriple slot0 = episode false false false
row evenTriple slot1 = episode false true  true
row evenTriple slot2 = episode true  false true
row evenTriple slot3 = episode true  true  false
row oddTriple slot0  = episode false false true
row oddTriple slot1  = episode false true  false
row oddTriple slot2  = episode true  false false
row oddTriple slot3  = episode true  true  true

data AxisPair : Set where
  pedagogyByAuthority : AxisPair
  pedagogyByEcology : AxisPair
  authorityByEcology : AxisPair

data PairCode : Set where
  pair00 pair01 pair10 pair11 : PairCode

packPair : Bool → Bool → PairCode
packPair false false = pair00
packPair false true  = pair01
packPair true  false = pair10
packPair true  true  = pair11

pairView : AxisPair → ThreeAxisEpisode → PairCode
pairView pedagogyByAuthority e =
  packPair (pedagogyPresent e) (learnerDecisionPower e)
pairView pedagogyByEcology e =
  packPair (pedagogyPresent e) (ecologyObserved e)
pairView authorityByEcology e =
  packPair (learnerDecisionPower e) (ecologyObserved e)

match : PairCode → PairCode → Nat
match pair00 pair00 = suc zero
match pair01 pair01 = suc zero
match pair10 pair10 = suc zero
match pair11 pair11 = suc zero
match _ _ = zero

count : Population → AxisPair → PairCode → Nat
count p axes code =
  match (pairView axes (row p slot0)) code +
  match (pairView axes (row p slot1)) code +
  match (pairView axes (row p slot2)) code +
  match (pairView axes (row p slot3)) code

-- All twelve joint-pair cells match in the two synthetic populations.
everyPairCountMatches :
  (axes : AxisPair) (code : PairCode) →
  count evenTriple axes code ≡ count oddTriple axes code
everyPairCountMatches pedagogyByAuthority pair00 = refl
everyPairCountMatches pedagogyByAuthority pair01 = refl
everyPairCountMatches pedagogyByAuthority pair10 = refl
everyPairCountMatches pedagogyByAuthority pair11 = refl
everyPairCountMatches pedagogyByEcology pair00 = refl
everyPairCountMatches pedagogyByEcology pair01 = refl
everyPairCountMatches pedagogyByEcology pair10 = refl
everyPairCountMatches pedagogyByEcology pair11 = refl
everyPairCountMatches authorityByEcology pair00 = refl
everyPairCountMatches authorityByEcology pair01 = refl
everyPairCountMatches authorityByEcology pair10 = refl
everyPairCountMatches authorityByEcology pair11 = refl

data PairwiseSummary : Set where
  everyPairBalanced : PairwiseSummary

pairwiseSummary : Population → PairwiseSummary
pairwiseSummary evenTriple = everyPairBalanced
pairwiseSummary oddTriple = everyPairBalanced

-- Which three-way parity family the complete episode population occupies:
-- a higher-order interaction, not a causal/ethical outcome.
threeWayPattern : Population → Bool
threeWayPattern evenTriple = false
threeWayPattern oddTriple = true

patternDifferent :
  threeWayPattern evenTriple ≡ threeWayPattern oddTriple → ⊥
patternDifferent ()

pairwiseDoesNotDetermineTriple :
  INF.NonFactorabilityWitness pairwiseSummary threeWayPattern
pairwiseDoesNotDetermineTriple =
  INF.nonFactorabilityWitness evenTriple oddTriple refl patternDifferent

pairwiseTabulationCannotPayThreeWayPattern :
  INF.FactorsThrough pairwiseSummary threeWayPattern → ⊥
pairwiseTabulationCannotPayThreeWayPattern =
  INF.witnessRulesOutEveryFlatFactorisation pairwiseDoesNotDetermineTriple

relabelledPairwiseTablesCannotRecoverThirdOrder :
  ∀ {View : Set} (relabel : PairwiseSummary → View) →
  INF.FactorsThrough (λ p → relabel (pairwiseSummary p)) threeWayPattern → ⊥
relabelledPairwiseTablesCannotRecoverThirdOrder relabel =
  INF.rechartingCannotRecoverErasedPhenomenon
    relabel pairwiseDoesNotDetermineTriple

------------------------------------------------------------------------
-- Scope / authority firewall: no fake constructor from candidate to
-- reviewed source or from pairwise agreement to a universally valid pathway.
------------------------------------------------------------------------

data CandidateCountsAsAdmittedStudy : Set where
data PairwiseCoverageImpliesHigherOrderCoverage : Set where
data HigherOrderPatternEstablishesESDEffect : Set where
data StructuralMemoryOwnerDiagnosesLearners : Set where
data LESDonorConveysCommunityOrCulturalAuthority : Set where

noCandidateAdmission : CandidateCountsAsAdmittedStudy → ⊥
noCandidateAdmission ()
noPairwisePromotion : PairwiseCoverageImpliesHigherOrderCoverage → ⊥
noPairwisePromotion ()
noEffectFromSyntheticPopulation : HigherOrderPatternEstablishesESDEffect → ⊥
noEffectFromSyntheticPopulation ()
noPsychologicalInferenceFromDonor : StructuralMemoryOwnerDiagnosesLearners → ⊥
noPsychologicalInferenceFromDonor ()
noCulturalAuthorityFromStructuralDonor :
  LESDonorConveysCommunityOrCulturalAuthority → ⊥
noCulturalAuthorityFromStructuralDonor ()

jointHyperfabricReading : String
jointHyperfabricReading =
  "Original source, revised source span, study design, learner/community decision power, situated ecology, temporal memory, counterfactual and institutional incidence are a sparse higher-order evidence carrier. Source-to-principle crosswalks and even every pairwise joint frequency are not sufficient for arbitrary three-axis interaction claims. The exact same-source review/admission/profile/context receipts are separate obligations; no candidate citation or formal carrier creates an ESD effect."
