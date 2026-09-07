module DASHI.Cognition.PNF.SensibLawPabaiTransformationPromotionExact where

------------------------------------------------------------------------
-- PABAI COUNTERFACTUAL: EXECUTABLE REOPENING -> TYPED TRANSFORMATION
--
-- The finite search already finds a supplied reformulation candidate. This file
-- promotes that hit only as far as the universal legal algebra permits:
--
--   executable reopening
--   + typed remove-defeater transformation
--   + proof-relevant derivation in the transformed candidate graph
--
-- It deliberately does NOT prove that Australian law presently authorises that
-- transformation. Legal availability remains a separate source-graph obligation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawFiniteExecutableLegalSearchExact as Search
import DASHI.Cognition.PNF.SensibLawFiniteLegalSearchRegressionExact as Regression
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence

------------------------------------------------------------------------
-- Typed transformation candidate.
------------------------------------------------------------------------

pabaiTypedTransformation : Algebra.LegalTransformation
pabaiTypedTransformation = Algebra.legal-transformation
  Regression.pabaiNarrowedRule
  Algebra.removeDefeater
  Regression.pabaiCorePolicy
  Regression.pabaiSource
  true

------------------------------------------------------------------------
-- Proof-relevant derivation in the transformed candidate graph.
------------------------------------------------------------------------

pabaiForeseeabilityProof :
  Algebra.Reachable Regression.pabaiReformulatedGraph Regression.pabaiFacts
    Regression.pabaiForeseeability
pabaiForeseeabilityProof = Algebra.fromFact Algebra.here

pabaiKnowledgeProof :
  Algebra.Reachable Regression.pabaiReformulatedGraph Regression.pabaiFacts
    Regression.pabaiKnowledge
pabaiKnowledgeProof = Algebra.fromFact (Algebra.there Algebra.here)

pabaiControlProof :
  Algebra.Reachable Regression.pabaiReformulatedGraph Regression.pabaiFacts
    Regression.pabaiControl
pabaiControlProof =
  Algebra.fromFact (Algebra.there (Algebra.there Algebra.here))

pabaiReformulatedDutyProof :
  Algebra.Reachable Regression.pabaiReformulatedGraph Regression.pabaiFacts
    Negligence.dutyProposition
pabaiReformulatedDutyProof =
  Algebra.byRule
    Algebra.here
    tt
    (Algebra._∷_ pabaiForeseeabilityProof
      (Algebra._∷_ pabaiKnowledgeProof
        (Algebra._∷_ pabaiControlProof Algebra.[])))
    Algebra.[]
    Algebra.[]

pabaiTransformationPromotion :
  Search.TransformationPromotion
    1 Negligence.dutyProposition Regression.pabaiReformulationCandidate
pabaiTransformationPromotion = Search.transformation-promotion
  refl
  pabaiTypedTransformation
  pabaiReformulatedDutyProof

------------------------------------------------------------------------
-- Legal availability is its own promotion stage.
------------------------------------------------------------------------

record LegalAvailabilityPromotion
  (transformation : Algebra.LegalTransformation)
  (AvailableUnderControllingAuthorities : Set) : Set where
  constructor legal-availability-promotion
  field
    availabilityWitness : AvailableUnderControllingAuthorities

open LegalAvailabilityPromotion public

-- No constructor: this tranche has not established that the encoded Pabai
-- remove-defeater transformation is available under controlling Australian law.
data PabaiTransformationAvailableUnderControllingAuthorities : Set where

pabaiLegalAvailabilityStillOpen :
  PabaiTransformationAvailableUnderControllingAuthorities → ⊥
pabaiLegalAvailabilityStillOpen ()

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data TypedTransformationCandidateIsCurrentLaw : Set where
data ProofInCounterfactualGraphProvesLegalAvailability : Set where

typedCandidateDoesNotBecomeCurrentLaw :
  TypedTransformationCandidateIsCurrentLaw → ⊥
typedCandidateDoesNotBecomeCurrentLaw ()

counterfactualProofDoesNotProveAvailability :
  ProofInCounterfactualGraphProvesLegalAvailability → ⊥
counterfactualProofDoesNotProveAvailability ()
