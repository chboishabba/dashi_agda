module DASHI.Governance.PluralEpistemicRepairMethodologyBidiExact where

open import DASHI.Core.Prelude

import DASHI.Governance.ConsumerAdequacyResidualInterventionCapstoneExact as Governance
import DASHI.Core.ConsumerIndexedTranslationRealisationExact as Adequacy
import DASHI.Core.ResidualObligationPropagationExact as Residual
import DASHI.Governance.InterventionMechanismDecompositionExact as Intervention
import DASHI.Core.PluralEpistemicProgressMethodologyBidiExact as Method
import DASHI.Core.ProvenanceQuorumAdequacyBidiExact as Quorum
import DASHI.Core.ProvenanceSensitiveConsumerAdequacyBidiExact as Provenance
import DASHI.Core.PairIndexedInformationLossLocusBidiExact as Loss

------------------------------------------------------------------------
-- GOVERNANCE / INTERVENTION <-> PLURAL EPISTEMIC REPAIR
------------------------------------------------------------------------

structuralAdequacyStillConsumerRelative :
  Adequacy.ConsumerRelativeAdequacyWitness
    Adequacy.demoSystem
    Adequacy.sourceText
    Adequacy.structuralConsumer
    Adequacy.empiricalConsumer
structuralAdequacyStillConsumerRelative =
  Governance.adequateForStructuralNotEmpirical

semanticResidualStillLivesAtTheorem :
  Residual.carries
    Residual.demoFlow
    Residual.theoremStage
    Residual.missingSemanticBridge
semanticResidualStillLivesAtTheorem =
  Governance.residualSurvivesTheoremProduction

resourceRepairStillDoesNotGuaranteeCapability :
  Intervention.ResourceRepair Intervention.demoMechanisms Intervention.resourceOnly →
  Intervention.CapabilityExpanded Intervention.demoMechanisms Intervention.resourceOnly → ⊥
resourceRepairStillDoesNotGuaranteeCapability =
  Governance.resourceOnlyDoesNotExpandCapability

headcountSupportStillNeedsIndependentRoots :
  Quorum.IndependentProvenanceQuorumTwo
    Provenance.toyPolicy
    Provenance.targetConsumer
    Provenance.firstReport
    Provenance.secondReport → ⊥
headcountSupportStillNeedsIndependentRoots =
  Quorum.toyHeadcountDoesNotCreateIndependentQuorum

deterministicRechartStillCannotRestoreCollapsedPair :
  Loss.toyDownstream (Loss.toyObserve Loss.x)
  ≡ Loss.toyDownstream (Loss.toyObserve Loss.y)
deterministicRechartStillCannotRestoreCollapsedPair =
  Loss.toyCollapsedPairNeverRestored

governanceMayUseProvenanceClarification : Method.EpistemicProgressRoute
governanceMayUseProvenanceClarification = Method.establishIndependentProvenance

governanceMayNeedAddedCoordinate : Method.EpistemicProgressRoute
governanceMayNeedAddedCoordinate = Method.addNewCoordinate

data OneRepairCoordinateClosesAllGovernanceResiduals : Set where
data InstitutionalSupportCountProvesIndependentAuthority : Set where

governanceRepairRemainsCoordinateLocal :
  OneRepairCoordinateClosesAllGovernanceResiduals → ⊥
governanceRepairRemainsCoordinateLocal ()

institutionalMultiplicityDoesNotProveIndependentAuthority :
  InstitutionalSupportCountProvesIndependentAuthority → ⊥
institutionalMultiplicityDoesNotProveIndependentAuthority ()

record GovernancePluralRepairBoundary : Set where
  constructor governance-plural-repair-boundary
  field
    adequacyRemainsConsumerRelative : Bool
    residualMaySurviveFormalPromotion : Bool
    provenanceIndependenceNeedsSeparateReceipt : Bool
    deterministicRechartMayRestoreErasedCoordinate : Bool
    oneRepairCoordinateMeansGlobalRepair : Bool
    repairMethodCreatesNormativeAuthority : Bool

canonicalGovernancePluralRepairBoundary : GovernancePluralRepairBoundary
canonicalGovernancePluralRepairBoundary =
  governance-plural-repair-boundary true true true false false false
