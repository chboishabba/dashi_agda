module DASHI.Governance.PluralEpistemicRepairMethodologyBidiExact where

open import DASHI.Core.Prelude

import DASHI.Governance.ConsumerAdequacyResidualInterventionCapstoneExact as Governance
import DASHI.Core.PluralEpistemicProgressMethodologyBidiExact as Method
import DASHI.Core.ProvenanceQuorumAdequacyBidiExact as Quorum
import DASHI.Core.PairIndexedInformationLossLocusBidiExact as Loss

------------------------------------------------------------------------
-- GOVERNANCE / INTERVENTION <-> PLURAL EPISTEMIC REPAIR
--
-- Governance already separates consumer adequacy, surviving residuals and
-- intervention coordinates.  The plural methodology adds two constraints:
-- visible support multiplicity does not create provenance independence, and a
-- collapsed distinction cannot be repaired by deterministic relabelling alone.
------------------------------------------------------------------------

structuralAdequacyStillConsumerRelative =
  Governance.adequateForStructuralNotEmpirical

semanticResidualStillLivesAtTheorem =
  Governance.residualSurvivesTheoremProduction

resourceRepairStillDoesNotGuaranteeCapability =
  Governance.resourceOnlyDoesNotExpandCapability

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
