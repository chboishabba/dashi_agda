module DASHI.Cognition.Teleodynamics.ScopedVerifierConsumerSufficiencyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Unit using (⊤; tt)

import DASHI.Core.QueryFactorisationSufficiency as Query
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Core.FactorisationSpineCrosswalkExact as Crosswalk
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Cognition.Teleodynamics.ScopedVerifierArchitectureExact as Verify
import DASHI.Cognition.Teleodynamics.ScopedVerifierConcreteInstancesExact as Concrete

------------------------------------------------------------------------
-- CONSUMER-RELATIVE VERIFIER ADEQUACY
--
-- This owner is now deliberately a THIN ADAPTER onto the repo-wide Core spine.
-- It does not own a second factorisation calculus.
--
-- Canonical authority reused here:
--   Query.FactorsThrough                  query-indexed explicit factorisation
--   Descent.FactorsThrough                canonical observer factorisation
--   Descent.ConsumerSufficient            fibre/kernel consumer sufficiency
--   Repair.RefinementRepairs              sufficient local refinement repair
--   MDL.Eligible = Admissible × ConsumerAdequate
--
-- Thus a verifier verdict is never promoted directly to semantic adequacy.
-- Applicability/admissibility and consumer adequacy remain separately typed.
------------------------------------------------------------------------

ConsumerNonDescentWitness :
  ∀ {X O C : Set} →
  (X → O) → (X → C) → Set
ConsumerNonDescentWitness = Descent.ConsumerNonDescentWitness

ConsumerFactorization :
  ∀ {X O C : Set} →
  (X → O) → (X → C) → Set₁
ConsumerFactorization = Descent.FactorsThrough

collisionBlocksFactorization :
  ∀ {X O C : Set}
    {observe : X → O}
    {consumer : X → C} →
  ConsumerNonDescentWitness observe consumer →
  ConsumerFactorization observe consumer →
  ⊥
collisionBlocksFactorization = Descent.nonDescentWitnessBlocksFactorization

-- Compatibility name only: the payload is exactly the canonical Core
-- ConsumerSufficient proposition. The validator parameter carries scope/type
-- provenance but contributes no theorem authority by its mere presence.
ValidatorConsumerAdequacy :
  ∀ {X O C : Set} →
  Verify.ScopedValidator X →
  (X → O) →
  (X → C) →
  Set
ValidatorConsumerAdequacy V observe consumer =
  Descent.ConsumerSufficient observe consumer

validatorCollisionBlocksAdequacy :
  ∀ {X O C : Set}
    {V : Verify.ScopedValidator X}
    {observe : X → O}
    {consumer : X → C} →
  ConsumerNonDescentWitness observe consumer →
  ValidatorConsumerAdequacy V observe consumer →
  ⊥
validatorCollisionBlocksAdequacy =
  Descent.nonDescentWitnessBlocksSufficiency

adequateRefinementMustSeparate :
  ∀ {X O R C : Set}
    {coarse : X → O}
    {consumer : X → C}
    {refine : X → R} →
  (w : ConsumerNonDescentWitness coarse consumer) →
  Repair.RefinementRepairs coarse refine consumer →
  refine (Descent.left w) ≡ refine (Descent.right w) →
  ⊥
adequateRefinementMustSeparate =
  Repair.refinementRepairSeparatesWitness

------------------------------------------------------------------------
-- Literal verifier witness on the canonical factorisation spine.
------------------------------------------------------------------------

syntaxOnlyLeft : Concrete.CandidateArtifact
syntaxOnlyLeft = Concrete.candidate-artifact true true

syntaxOnlyRight : Concrete.CandidateArtifact
syntaxOnlyRight = Concrete.candidate-artifact true false

VerifierSurface : Set
VerifierSurface = Verify.VerificationStatus × Bool

syntaxOnlyView : Concrete.CandidateArtifact → VerifierSurface
syntaxOnlyView x = Verify.status Concrete.syntaxValidator x , false

provenanceAwareView : Concrete.CandidateArtifact → VerifierSurface
provenanceAwareView x =
  Verify.status Concrete.syntaxValidator x , Concrete.provenanceOK x

provenanceConsumer : Concrete.CandidateArtifact → Bool
provenanceConsumer = Concrete.provenanceOK

data VerifierQuery : Set where
  provenanceQuery : VerifierQuery

verifierQuestions :
  Query.InquiryQuestionFamily Concrete.CandidateArtifact VerifierQuery
verifierQuestions = Query.inquiryQuestionFamily (λ _ → Bool) ask
  where
  ask : (query : VerifierQuery) → Concrete.CandidateArtifact → Bool
  ask provenanceQuery = provenanceConsumer

-- The provenance-aware surface literally answers the declared provenance query.
provenanceQueryFactors :
  Query.FactorsThrough
    verifierQuestions
    provenanceAwareView
    provenanceQuery
provenanceQueryFactors = Query.factorsThrough proj₂ proof
  where
  proof :
    (x : Concrete.CandidateArtifact) →
    Query.ask verifierQuestions provenanceQuery x ≡
    proj₂ (provenanceAwareView x)
  proof x = refl

provenanceFactorsCanonically :
  Descent.FactorsThrough provenanceAwareView provenanceConsumer
provenanceFactorsCanonically =
  Crosswalk.queryFactorsToFactorized provenanceQueryFactors

provenanceAwareSufficient :
  Descent.ConsumerSufficient provenanceAwareView provenanceConsumer
provenanceAwareSufficient =
  Descent.fibreConstantIsConsumerSufficient
    (Descent.factorsThroughImpliesFibreConstant provenanceFactorsCanonically)

syntaxViewCollision :
  syntaxOnlyView syntaxOnlyLeft ≡ syntaxOnlyView syntaxOnlyRight
syntaxViewCollision = refl

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

syntaxStatusMissesProvenanceConsumer :
  Descent.ConsumerNonDescentWitness syntaxOnlyView provenanceConsumer
syntaxStatusMissesProvenanceConsumer =
  Descent.consumerNonDescentWitness
    syntaxOnlyLeft
    syntaxOnlyRight
    syntaxViewCollision
    trueNotFalse

syntaxViewNotConsumerSufficient :
  Descent.ConsumerSufficient syntaxOnlyView provenanceConsumer → ⊥
syntaxViewNotConsumerSufficient =
  Descent.nonDescentWitnessBlocksSufficiency
    syntaxStatusMissesProvenanceConsumer

syntaxQueryCannotFactor :
  Query.FactorsThrough verifierQuestions syntaxOnlyView provenanceQuery → ⊥
syntaxQueryCannotFactor factors =
  Descent.nonDescentWitnessBlocksFactorization
    syntaxStatusMissesProvenanceConsumer
    (Crosswalk.queryFactorsToFactorized factors)

------------------------------------------------------------------------
-- Admissible × ConsumerAdequate eligibility.
--
-- Both observation models are in the declared verifier comparison domain.
-- Only the provenance-aware model is adequate for the provenance consumer.
-- This gives an exact witness that admissibility does not imply adequacy and
-- that ranking/selection must occur only after MDL.Eligible is inhabited.
------------------------------------------------------------------------

data VerifierObservationModel : Set where
  syntaxOnlyModel : VerifierObservationModel
  provenanceAwareModel : VerifierObservationModel

observationView :
  VerifierObservationModel →
  Concrete.CandidateArtifact →
  VerifierSurface
observationView syntaxOnlyModel = syntaxOnlyView
observationView provenanceAwareModel = provenanceAwareView

ObservationAdmissible : VerifierObservationModel → Set
ObservationAdmissible model = ⊤

ObservationConsumerAdequate : VerifierObservationModel → Set
ObservationConsumerAdequate model =
  Descent.ConsumerSufficient (observationView model) provenanceConsumer

observationDescriptionLength : VerifierObservationModel → Nat
observationDescriptionLength syntaxOnlyModel = 1
observationDescriptionLength provenanceAwareModel = 2

data ObservationRefines :
    VerifierObservationModel → VerifierObservationModel → Set where
  syntaxSelf : ObservationRefines syntaxOnlyModel syntaxOnlyModel
  provenanceSelf : ObservationRefines provenanceAwareModel provenanceAwareModel
  provenanceRefinesSyntax :
    ObservationRefines syntaxOnlyModel provenanceAwareModel

observationModelReference : VerifierObservationModel → String
observationModelReference syntaxOnlyModel =
  "syntax-validator status with provenance erased"
observationModelReference provenanceAwareModel =
  "syntax-validator status paired with provenance coordinate"

verifierObservationProblem : MDL.ConsumerMDLProblem
verifierObservationProblem =
  MDL.consumerMDLProblem
    VerifierObservationModel
    ObservationAdmissible
    ObservationConsumerAdequate
    observationDescriptionLength
    ObservationRefines
    observationModelReference
    "description length ranks only after admissibility and consumer adequacy"
    "declared provenance consumer"

syntaxModelAdmissible :
  MDL.Admissible verifierObservationProblem syntaxOnlyModel
syntaxModelAdmissible = tt

syntaxModelNotAdequate :
  MDL.ConsumerAdequate verifierObservationProblem syntaxOnlyModel → ⊥
syntaxModelNotAdequate = syntaxViewNotConsumerSufficient

syntaxModelNotEligible :
  MDL.Eligible verifierObservationProblem syntaxOnlyModel → ⊥
syntaxModelNotEligible eligible =
  syntaxModelNotAdequate (proj₂ eligible)

provenanceModelEligible :
  MDL.Eligible verifierObservationProblem provenanceAwareModel
provenanceModelEligible = tt , provenanceAwareSufficient

record ConsumerSufficiencyBoundary : Set where
  constructor consumer-sufficiency-boundary
  field
    consumerRelativeAdequacyRequired : Bool
    canonicalQueryFactorsThroughReused : Bool
    canonicalConsumerSufficientReused : Bool
    admissibilitySeparatedFromConsumerAdequacy : Bool
    eligibilityIsAdmissibleAndConsumerAdequate : Bool
    localFactorisationCalculusRetired : Bool
    coarseCollisionAloneImpliesFailure : Bool
    distinguishingConsumerCollisionBlocksDescent : Bool
    validatorPassImpliesAllConsumerSufficiency : Bool
    refinementRequiresCanonicalConsumerSufficiency : Bool
    adequateRefinementMustSeparateWitness : Bool
    unmergedSiblingTheoremAuthorityRequired : Bool

canonicalConsumerSufficiencyBoundary : ConsumerSufficiencyBoundary
canonicalConsumerSufficiencyBoundary =
  consumer-sufficiency-boundary
    true
    true
    true
    true
    true
    true
    false
    true
    false
    true
    true
    false
