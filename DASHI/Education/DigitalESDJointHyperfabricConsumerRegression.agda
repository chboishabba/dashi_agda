module DASHI.Education.DigitalESDJointHyperfabricConsumerRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Education.DigitalESDJointHyperfabricConsumerExact as Joint
import DASHI.Education.DigitalESDEfSSourceCrossPollinationExact as Sources
import DASHI.Education.DigitalESDEvidenceBraidTensionExact as Braid
import DASHI.Education.DigitalESDPrincipleSurvivalAuditExact as Survival
import DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesExact as Principles

-- Concrete 1 November source case is not a generic evidence source:
-- its original locator, role and braid stay welded through the new view.
sameSourceComparisonUsesCanonicalTension :
  Braid.TensionReceipt.relation
    (Joint.CandidateJointHyperedge.comparison
      (Joint.candidateJointHyperedge Sources.adefilaEcoCOIL))
  ≡ Braid.productiveTension
sameSourceComparisonUsesCanonicalTension = refl

candidateStillCandidate :
  Joint.CandidateJointHyperedge.candidateOnly
    (Joint.candidateJointHyperedge Sources.adefilaEcoCOIL)
  ≡ true
candidateStillCandidate = refl

-- Real pairwise *joint count* equalities, not just equal coarse labels.
pairPedagogyAuthority00 :
  Joint.count Joint.evenTriple Joint.pedagogyByAuthority Joint.pair00
  ≡ Joint.count Joint.oddTriple Joint.pedagogyByAuthority Joint.pair00
pairPedagogyAuthority00 = refl

pairPedagogyEcology11 :
  Joint.count Joint.evenTriple Joint.pedagogyByEcology Joint.pair11
  ≡ Joint.count Joint.oddTriple Joint.pedagogyByEcology Joint.pair11
pairPedagogyEcology11 = refl

pairAuthorityEcology10 :
  Joint.count Joint.evenTriple Joint.authorityByEcology Joint.pair10
  ≡ Joint.count Joint.oddTriple Joint.authorityByEcology Joint.pair10
pairAuthorityEcology10 = refl

allThreeJointMarginsAgree :
  (axes : Joint.AxisPair) (code : Joint.PairCode) →
  Joint.count Joint.evenTriple axes code ≡
  Joint.count Joint.oddTriple axes code
allThreeJointMarginsAgree = Joint.everyPairCountMatches

pairwiseSignatureExactlyAgrees :
  Joint.pairwiseSummary Joint.evenTriple ≡
  Joint.pairwiseSummary Joint.oddTriple
pairwiseSignatureExactlyAgrees = Joint.pairwiseSummariesAgree

tripleDoesNotDescend :
  INF.FactorsThrough Joint.pairwiseSummary Joint.threeWayPattern → ⊥
tripleDoesNotDescend = Joint.pairwiseTabulationCannotPayThreeWayPattern

rechartingDoesNotRepair :
  ∀ {View : Set}
  (relabel : Joint.PairwiseSummary → View) →
  INF.FactorsThrough (λ p → relabel (Joint.pairwiseSummary p))
    Joint.threeWayPattern → ⊥
rechartingDoesNotRepair = Joint.relabelledPairwiseTablesCannotRecoverThirdOrder

noEmpiricalEffectFromParity :
  Joint.HigherOrderPatternEstablishesESDEffect → ⊥
noEmpiricalEffectFromParity = Joint.noEffectFromSyntheticPopulation

noCommunityAuthorityFromEcologyDonor :
  Joint.LESDonorConveysCommunityOrCulturalAuthority → ⊥
noCommunityAuthorityFromEcologyDonor =
  Joint.noCulturalAuthorityFromStructuralDonor

-- The same candidate principle label legitimately answers different
-- research consumers; no global verdict follows from the label alone.
sameAgencyPrincipleAcrossConsumers :
  Joint.agencyPrincipleProjection Joint.learnerVoiceInDigitalCourse ≡
  Joint.agencyPrincipleProjection Joint.communityDecisionRightsInEfS
sameAgencyPrincipleAcrossConsumers = refl

localVoiceCandidateRetained :
  Joint.candidateVerdictForConsumer Joint.learnerVoiceInDigitalCourse ≡
  Survival.provisionallyRetain
localVoiceCandidateRetained = refl

communityAuthorityCandidateNeedsSplit :
  Joint.candidateVerdictForConsumer Joint.communityDecisionRightsInEfS ≡
  Survival.provisionalSplitCandidate
communityAuthorityCandidateNeedsSplit = refl

labelCannotPayEveryConsumer :
  INF.FactorsThrough Joint.agencyPrincipleProjection
    Joint.candidateVerdictForConsumer → ⊥
labelCannotPayEveryConsumer =
  Joint.noUniversalCandidateVerdictFromPrincipleLabel
