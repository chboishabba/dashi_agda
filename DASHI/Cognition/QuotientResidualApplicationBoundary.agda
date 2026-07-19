module DASHI.Cognition.QuotientResidualApplicationBoundary where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.QuotientResidualDynamics as QRD
import DASHI.Cognition.QuotientResidualTheoremLadder as Ladder
import DASHI.Cognition.QuotientResidualCategoricalLoom as Categorical

------------------------------------------------------------------------
-- Domain application boundary.
--
-- Quotient-residual geometry may be instantiated in law, politics, family
-- conflict, cognition, medicine, economics, or institutional classification,
-- but a structural receipt never promotes a domain interpretation by itself.
------------------------------------------------------------------------

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ _ = false

data ApplicationDomain : Set where
  discourseDomain : ApplicationDomain
  legalDomain : ApplicationDomain
  institutionalDomain : ApplicationDomain
  economicDomain : ApplicationDomain
  familyConflictDomain : ApplicationDomain
  cognitiveTraceDomain : ApplicationDomain
  medicalObservationDomain : ApplicationDomain
  politicalDiscourseDomain : ApplicationDomain

record DomainApplicationCandidate : Set₁ where
  field
    domain : ApplicationDomain
    structuralReceipt : QRD.QuotientResidualDynamicsReceipt
    theoremReceipt : Ladder.QuotientResidualTheoremLadderReceipt
    categoricalReceipt : Categorical.QuotientResidualCategoricalReceipt

    sourceBound : Bool
    diagnosticOnly : Bool
    independentDomainEvidenceRequired : Bool
    noCausalPromotion : Bool
    noClinicalPromotion : Bool
    noPoliticalProphecyPromotion : Bool
    noIdentityEssentialismPromotion : Bool
    noMoralSuperiorityPromotion : Bool

  structuralKernelAvailable : Bool
  structuralKernelAvailable =
    QRD.QuotientResidualDynamicsReceipt.structuralLayerClosed structuralReceipt
    ∧ Ladder.QuotientResidualTheoremLadderReceipt.promotedKernelClosed theoremReceipt
    ∧ Categorical.QuotientResidualCategoricalReceipt.categoryClosed categoricalReceipt

  domainBoundaryClosed : Bool
  domainBoundaryClosed =
    sourceBound
    ∧ diagnosticOnly
    ∧ independentDomainEvidenceRequired
    ∧ noCausalPromotion
    ∧ noClinicalPromotion
    ∧ noPoliticalProphecyPromotion
    ∧ noIdentityEssentialismPromotion
    ∧ noMoralSuperiorityPromotion

  allClosed : Bool
  allClosed = structuralKernelAvailable ∧ domainBoundaryClosed

  closureStatement : String
  closureStatement =
    "The quotient-residual kernel may organise domain observations, but it "
    ++ "does not diagnose, establish causation, predict politics, essentialise "
    ++ "identity, or confer moral authority. Domain promotion requires separate evidence."

canonicalDiscourseCandidate : DomainApplicationCandidate
canonicalDiscourseCandidate = record
  { domain = discourseDomain
  ; structuralReceipt = QRD.canonicalQuotientResidualDynamicsReceipt
  ; theoremReceipt = Ladder.canonicalTheoremLadderReceipt
  ; categoricalReceipt = Categorical.canonicalCategoricalReceipt
  ; sourceBound = true
  ; diagnosticOnly = true
  ; independentDomainEvidenceRequired = true
  ; noCausalPromotion = true
  ; noClinicalPromotion = true
  ; noPoliticalProphecyPromotion = true
  ; noIdentityEssentialismPromotion = true
  ; noMoralSuperiorityPromotion = true
  }

canonicalLegalCandidate : DomainApplicationCandidate
canonicalLegalCandidate = record
  { domain = legalDomain
  ; structuralReceipt = QRD.canonicalQuotientResidualDynamicsReceipt
  ; theoremReceipt = Ladder.canonicalTheoremLadderReceipt
  ; categoricalReceipt = Categorical.canonicalCategoricalReceipt
  ; sourceBound = true
  ; diagnosticOnly = true
  ; independentDomainEvidenceRequired = true
  ; noCausalPromotion = true
  ; noClinicalPromotion = true
  ; noPoliticalProphecyPromotion = true
  ; noIdentityEssentialismPromotion = true
  ; noMoralSuperiorityPromotion = true
  }

canonicalCognitiveTraceCandidate : DomainApplicationCandidate
canonicalCognitiveTraceCandidate = record
  { domain = cognitiveTraceDomain
  ; structuralReceipt = QRD.canonicalQuotientResidualDynamicsReceipt
  ; theoremReceipt = Ladder.canonicalTheoremLadderReceipt
  ; categoricalReceipt = Categorical.canonicalCategoricalReceipt
  ; sourceBound = true
  ; diagnosticOnly = true
  ; independentDomainEvidenceRequired = true
  ; noCausalPromotion = true
  ; noClinicalPromotion = true
  ; noPoliticalProphecyPromotion = true
  ; noIdentityEssentialismPromotion = true
  ; noMoralSuperiorityPromotion = true
  }

canonicalMedicalObservationCandidate : DomainApplicationCandidate
canonicalMedicalObservationCandidate = record
  { domain = medicalObservationDomain
  ; structuralReceipt = QRD.canonicalQuotientResidualDynamicsReceipt
  ; theoremReceipt = Ladder.canonicalTheoremLadderReceipt
  ; categoricalReceipt = Categorical.canonicalCategoricalReceipt
  ; sourceBound = true
  ; diagnosticOnly = true
  ; independentDomainEvidenceRequired = true
  ; noCausalPromotion = true
  ; noClinicalPromotion = true
  ; noPoliticalProphecyPromotion = true
  ; noIdentityEssentialismPromotion = true
  ; noMoralSuperiorityPromotion = true
  }

discourseBoundaryClosedProof :
  DomainApplicationCandidate.allClosed canonicalDiscourseCandidate ≡ true
discourseBoundaryClosedProof = refl

legalBoundaryClosedProof :
  DomainApplicationCandidate.allClosed canonicalLegalCandidate ≡ true
legalBoundaryClosedProof = refl

cognitiveBoundaryClosedProof :
  DomainApplicationCandidate.allClosed canonicalCognitiveTraceCandidate ≡ true
cognitiveBoundaryClosedProof = refl

medicalBoundaryClosedProof :
  DomainApplicationCandidate.allClosed canonicalMedicalObservationCandidate ≡ true
medicalBoundaryClosedProof = refl
