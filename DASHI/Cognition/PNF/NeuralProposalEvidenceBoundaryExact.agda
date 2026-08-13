module DASHI.Cognition.PNF.NeuralProposalEvidenceBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ; +_)

import DASHI.Cognition.PNF.TypePressure as Pressure

------------------------------------------------------------------------
-- NEURAL PROPOSAL -> TYPE PRESSURE, NOT TRUTH PROMOTION
--
-- A learned score/activation may contribute evidence to the phased relational
-- lattice.  It does not itself inhabit an ontology-promotion authority type.
------------------------------------------------------------------------

data Subject : Set where
  item : Subject

data CandidateType : Set where
  eventLike editionLike : CandidateType

data NeuralEvidence : Set where
  modelProposal : NeuralEvidence

record NeuralProposal : Set where
  constructor neuralProposal
  field
    proposedSubject : Subject
    proposedType : CandidateType
    signedScore : ℤ
    modelProvenance : String
    proposalScope : String

open NeuralProposal public

canonicalProposal : NeuralProposal
canonicalProposal =
  neuralProposal item editionLike (+ 1)
    "neural model proposal"
    "candidate type pressure only"

proposalToTypePressure :
  (proposal : NeuralProposal) →
  Pressure.TypePressureContribution
    {Subject = Subject}
    {CandidateType = CandidateType}
    {Evidence = NeuralEvidence}
    (proposedSubject proposal)
    (proposedType proposal)
proposalToTypePressure proposal =
  Pressure.typePressureContribution
    modelProposal
    (signedScore proposal)
    (modelProvenance proposal)
    (proposalScope proposal)

canonicalProposalProducesPositivePressure :
  Pressure.signedPressure (proposalToTypePressure canonicalProposal) ≡ + 1
canonicalProposalProducesPositivePressure = refl

------------------------------------------------------------------------
-- Authority boundary inherited from the canonical TypePressure module.
------------------------------------------------------------------------

neuralPressureCannotPromoteOntologyType :
  Pressure.TypePressurePromotionPermission → ⊥
neuralPressureCannotPromoteOntologyType = Pressure.pressureAloneCannotAssertType

record NeuralEvidenceBoundary : Set₁ where
  constructor neuralEvidenceBoundary
  field
    contributionExists :
      Pressure.TypePressureContribution
        {Subject = Subject}
        {CandidateType = CandidateType}
        {Evidence = NeuralEvidence}
        item editionLike
    noDirectPromotion : Pressure.TypePressurePromotionPermission → ⊥

open NeuralEvidenceBoundary public

canonicalNeuralEvidenceBoundary : NeuralEvidenceBoundary
canonicalNeuralEvidenceBoundary =
  neuralEvidenceBoundary
    (proposalToTypePressure canonicalProposal)
    neuralPressureCannotPromoteOntologyType

------------------------------------------------------------------------
-- Exact lesson:
--   activation / score -> provenance-bearing evidence contribution;
--   evidence contribution -/-> ontology truth.
------------------------------------------------------------------------
