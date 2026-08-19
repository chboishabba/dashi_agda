module DASHI.Education.EarlyYearsEmpowermentConnectednessRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Education.CapabilityRecognitionExact as Recognition
import DASHI.Education.CommunityConnectednessTopologyExact as Connectedness
import DASHI.Education.EarlyYearsEmpowermentConnectednessBridgeExact as Bridge
import DASHI.Education.EarlyYearsStakeholderCoverageExact as Coverage

------------------------------------------------------------------------
-- Focused compile/regression surface.  These assertions exercise the exact
-- negative and positive seams added by the empowerment/connectedness tranche.
------------------------------------------------------------------------

professionalSurfaceCannotServeFamilyExperienceRegression :
  Consumer.ConsumerSufficient Coverage.professionalSummary Coverage.familyExperience → ⊥
professionalSurfaceCannotServeFamilyExperienceRegression =
  Coverage.professionalSurfaceCannotServeFamilyExperience

anySufficientFamilyObserverMustSplitRegression :
  ∀ {Surface : Set}
    (observe : Coverage.FamilySituation → Surface) →
  Consumer.ConsumerSufficient observe Coverage.familyExperience →
  observe Coverage.situationA ≡ observe Coverage.situationB → ⊥
anySufficientFamilyObserverMustSplitRegression =
  Coverage.anyFamilyExperienceSufficientObserverMustSplitProfessionalCollision

nonRecognitionCannotDetermineCapabilityRegression :
  NonFactor.FactorsThrough Recognition.recognitionProjection Recognition.capabilityProjection → ⊥
nonRecognitionCannotDetermineCapabilityRegression =
  Recognition.lackOfRecognitionCannotDetermineLackOfCapability

formalConnectionCannotDetermineEffectiveRegression :
  NonFactor.FactorsThrough Connectedness.formalProjection Connectedness.effectiveProjection → ⊥
formalConnectionCannotDetermineEffectiveRegression =
  Connectedness.formalConnectionCannotDetermineEffectiveConnection

effectiveConnectionCannotDetermineAuthorityRegression :
  NonFactor.FactorsThrough Connectedness.effectiveProjection Connectedness.authorityProjection → ⊥
effectiveConnectionCannotDetermineAuthorityRegression =
  Connectedness.effectiveConnectionCannotDetermineAuthority

canonicalStrengthBasedCertificate : Bridge.CapabilityExpandingWithoutDomination
canonicalStrengthBasedCertificate = Bridge.canonicalCapabilityExpandingWithoutDomination

missingActiveStakeholderBlocks :
  Coverage.missingActiveStakeholderBlocksDirectClaim
    Coverage.canonicalStakeholderCoverageBoundary ≡ true
missingActiveStakeholderBlocks = refl

nonRecognitionIsNotDeficitProof :
  Recognition.unrealisedContributionProvesDeficit
    Recognition.canonicalCapabilityRecognitionBoundary ≡ false
nonRecognitionIsNotDeficitProof = refl

formalEdgeIsNotEffectiveConnection :
  Connectedness.formalEdgeEqualsEffectiveConnection
    Connectedness.canonicalCommunityConnectednessBoundary ≡ false
formalEdgeIsNotEffectiveConnection = refl

peerCatalystDoesNotAcquireDecisionAuthority :
  Connectedness.peerInfluenceAutomaticallyConfersDecisionAuthority
    Connectedness.canonicalPeerCatalystBoundary ≡ false
peerCatalystDoesNotAcquireDecisionAuthority = refl

capabilityExpansionStillNeedsSemanticPromotion :
  Bridge.capabilityExpansionRequiresSemanticPromotionWitness
    Bridge.canonicalEmpowermentConnectednessInvariant ≡ true
capabilityExpansionStillNeedsSemanticPromotion = refl
