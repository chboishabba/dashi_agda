module DASHI.Governance.FederatedGovernanceEvidenceInstantiationRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.FederatedGovernanceEvidenceInstantiationExact as Capstone

sourcesRemainDistinct :
  Capstone.crossSourceAgreementCollapsesProvenance
    Capstone.canonicalFederatedGovernanceEvidenceBoundary
  ≡ false
sourcesRemainDistinct = refl

boloNotAttributedToBookchin :
  Capstone.boloArchitectureAttributedToBookchin
    Capstone.canonicalFederatedGovernanceEvidenceBoundary
  ≡ false
boloNotAttributedToBookchin = refl

bookchinNotAttributedToBolo :
  Capstone.bookchinConfederalismAttributedToPM
    Capstone.canonicalFederatedGovernanceEvidenceBoundary
  ≡ false
bookchinNotAttributedToBolo = refl

ipccNotPoliticalDoctrine :
  Capstone.ipccTransitionEvidenceCreatesPoliticalDoctrine
    Capstone.canonicalFederatedGovernanceEvidenceBoundary
  ≡ false
ipccNotPoliticalDoctrine = refl

occupyEvidenceDoesNotPayScalingLaw :
  Capstone.occupyEvidencePaysQuantitativeScalingLaw
    Capstone.canonicalFederatedGovernanceEvidenceBoundary
  ≡ false
occupyEvidenceDoesNotPayScalingLaw = refl

boundedOccupyInteractionIsPaid :
  Capstone.occupyArchivePaysBoundedNamedInteraction
    Capstone.canonicalFederatedGovernanceEvidenceBoundary
  ≡ true
boundedOccupyInteractionIsPaid = refl

boundedFiniteOccupyGraphIsPaid :
  Capstone.occupyArchivePaysBoundedFiniteIncidenceGraph
    Capstone.canonicalFederatedGovernanceEvidenceBoundary
  ≡ true
boundedFiniteOccupyGraphIsPaid = refl

completeRealIncidenceStillUnpaid :
  Capstone.actualParticipantIssueIncidencePaid
    Capstone.canonicalFederatedGovernanceEvidenceBoundary
  ≡ false
completeRealIncidenceStillUnpaid = refl

coordinationCostStillUnpaid :
  Capstone.empiricalCoordinationCostFunctionalPaid
    Capstone.canonicalFederatedGovernanceEvidenceBoundary
  ≡ false
coordinationCostStillUnpaid = refl
