module DASHI.Core.WorldRepresentationSeparationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryFactorisationSufficiency as QFS
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.SituatedFormalisationBoundaryExact as Situated
import DASHI.Core.InterpretiveFormalisationCoreExact as Interpretive
import DASHI.Core.ConsumerRelativeCoarseGrainingBidiExact as Coarse

------------------------------------------------------------------------
-- WORLD / OBSERVATION / THEORY / BELIEF TYPE SEPARATION
--
-- The underlying regularity is not identified with a theory of that
-- regularity.  A theory is a representation whose adequacy is judged relative
-- to declared observations/queries/consumers.  This is deliberately compatible
-- with the repo's existing factorisation, non-factorability, situated-
-- formalisation and admissible-consumer machinery.
------------------------------------------------------------------------

data EpistemicLayer : Set where
  worldLayer : EpistemicLayer
  observationLayer : EpistemicLayer
  theoryLayer : EpistemicLayer
  beliefLayer : EpistemicLayer

record WorldRepresentationSystem : Set₁ where
  constructor world-representation-system
  field
    World : Set
    Observation : Set
    Theory : Set
    Belief : Set
    worldStep : World → World
    observe : World → Observation
    representedPrediction : Theory → World → Observation
    representedByBelief : Belief → Theory

open WorldRepresentationSystem public

record TheoryAdequacy
    (system : WorldRepresentationSystem)
    (theory : Theory system) : Set₁ where
  constructor theory-adequacy
  field
    Domain : Set
    worldAt : Domain → World system
    agreesOnDomain :
      (point : Domain) →
      representedPrediction system theory (worldAt point)
      ≡ observe system (worldAt point)
    domainReference : String

open TheoryAdequacy public

------------------------------------------------------------------------
-- Wrong-type firewalls.
------------------------------------------------------------------------

data WorldRegularityRequiresRepresentationPermission : Set where
data TheoryRevisionRequiresWorldRevisionPermission : Set where
data CouplingRequiresExplicitTheoryPermission : Set where
data ConsumerAdequacyImpliesWorldExhaustionPermission : Set where

worldRegularityDoesNotRequireRepresentation :
  WorldRegularityRequiresRepresentationPermission → ⊥
worldRegularityDoesNotRequireRepresentation ()

theoryRevisionDoesNotRequireWorldRevision :
  TheoryRevisionRequiresWorldRevisionPermission → ⊥
theoryRevisionDoesNotRequireWorldRevision ()

couplingDoesNotRequireExplicitTheory :
  CouplingRequiresExplicitTheoryPermission → ⊥
couplingDoesNotRequireExplicitTheory ()

consumerAdequacyDoesNotImplyWorldExhaustion :
  ConsumerAdequacyImpliesWorldExhaustionPermission → ⊥
consumerAdequacyDoesNotImplyWorldExhaustion ()

------------------------------------------------------------------------
-- Concrete gravity-shaped finite witness.
--
-- Both states produce the same coarse "it falls" observation while a richer
-- world reading distinguishes them.  IntersectionalNonFactorability therefore
-- proves that no post-hoc interpretation of that one coarse observation can
-- recover the erased distinction.
------------------------------------------------------------------------

data GravityWorldState : Set where
  lowCurvatureFall : GravityWorldState
  highCurvatureFall : GravityWorldState

data FallObservation : Set where
  observedFall : FallObservation

coarseFallObservation : GravityWorldState → FallObservation
coarseFallObservation lowCurvatureFall = observedFall
coarseFallObservation highCurvatureFall = observedFall

data GravityRegularityReading : Set where
  lowCurvatureReading : GravityRegularityReading
  highCurvatureReading : GravityRegularityReading

gravityRegularity : GravityWorldState → GravityRegularityReading
gravityRegularity lowCurvatureFall = lowCurvatureReading
gravityRegularity highCurvatureFall = highCurvatureReading

gravityReadingsDiffer :
  gravityRegularity lowCurvatureFall
  ≡ gravityRegularity highCurvatureFall → ⊥
gravityReadingsDiffer ()

gravityObservationNonFactorability :
  INF.NonFactorabilityWitness coarseFallObservation gravityRegularity
gravityObservationNonFactorability =
  INF.nonFactorabilityWitness
    lowCurvatureFall
    highCurvatureFall
    refl
    gravityReadingsDiffer

coarseFallCannotExhaustGravityRegularity :
  INF.FactorsThrough coarseFallObservation gravityRegularity → ⊥
coarseFallCannotExhaustGravityRegularity =
  INF.witnessRulesOutEveryFlatFactorisation
    gravityObservationNonFactorability

rechartingFallObservationStillCannotExhaustGravityRegularity :
  ∀ {Recharted : Set} →
  (rechart : FallObservation → Recharted) →
  INF.FactorsThrough
    (λ state → rechart (coarseFallObservation state))
    gravityRegularity →
  ⊥
rechartingFallObservationStillCannotExhaustGravityRegularity rechart =
  INF.rechartingCannotRecoverErasedPhenomenon
    rechart gravityObservationNonFactorability


------------------------------------------------------------------------
-- The same coarse observation can nevertheless be exactly sufficient for a
-- declared consumer query.  This composes QueryFactorisationSufficiency with
-- the non-factorability witness above:
--
--   query factors through observation
--   does not imply
--   world regularity factors through observation.
------------------------------------------------------------------------

data FallQuery : Set where
  didItFall : FallQuery

fallQuestions : QFS.InquiryQuestionFamily GravityWorldState FallQuery
fallQuestions = QFS.inquiryQuestionFamily (λ query → FallObservation) askFall
  where
    askFall : (query : FallQuery) → GravityWorldState → FallObservation
    askFall didItFall state = coarseFallObservation state

fallQueryFactorsThroughObservation :
  QFS.FactorsThrough fallQuestions coarseFallObservation didItFall
fallQueryFactorsThroughObservation =
  QFS.factorsThrough (λ observation → observation) proof
  where
    proof :
      (state : GravityWorldState) →
      QFS.ask fallQuestions didItFall state
      ≡ coarseFallObservation state
    proof lowCurvatureFall = refl
    proof highCurvatureFall = refl

consumerQueryCanFactorWhileWorldRegularityDoesNot :
  QFS.FactorsThrough fallQuestions coarseFallObservation didItFall
  ×
  (INF.FactorsThrough coarseFallObservation gravityRegularity → ⊥)
consumerQueryCanFactorWhileWorldRegularityDoesNot =
  fallQueryFactorsThroughObservation ,
  coarseFallCannotExhaustGravityRegularity

------------------------------------------------------------------------
-- Theory change while the represented world coordinate is held fixed.
------------------------------------------------------------------------

data GravityTheory : Set where
  preFormalRegularity : GravityTheory
  newtonianRepresentation : GravityTheory
  relativisticRepresentation : GravityTheory

record SameWorldTheoryRevision : Set where
  constructor same-world-theory-revision
  field
    world : GravityWorldState
    beforeTheory : GravityTheory
    afterTheory : GravityTheory
    revisionReference : String

open SameWorldTheoryRevision public

newtonToRelativitySameWorldRevision : SameWorldTheoryRevision
newtonToRelativitySameWorldRevision =
  same-world-theory-revision
    highCurvatureFall
    newtonianRepresentation
    relativisticRepresentation
    "Theory coordinate changes while the represented world coordinate is held fixed."

------------------------------------------------------------------------
-- Organism/world coupling without an explicit symbolic theory coordinate.
-- The absence of a Theory field is intentional: adaptation/control may be
-- constrained by a regularity without representing that regularity propositionally.
------------------------------------------------------------------------

data FlightPhenotype : Set where
  glidingPhenotype : FlightPhenotype
  flappingPhenotype : FlightPhenotype

record WorldCoupling : Set where
  constructor world-coupling
  field
    world : GravityWorldState
    phenotype : FlightPhenotype
    viableInteraction : Bool
    couplingReference : String

open WorldCoupling public

birdLikeGravityCoupling : WorldCoupling
birdLikeGravityCoupling =
  world-coupling
    lowCurvatureFall
    flappingPhenotype
    true
    "Biomechanical coupling can be selected/controlled against world regularities without a symbolic gravity theory."

------------------------------------------------------------------------
-- Existing DASHI boundaries are ancestors, not competitors.
------------------------------------------------------------------------

situatedBoundary : Situated.SituatedFormalisationBoundary
situatedBoundary = Situated.canonicalSituatedFormalisationBoundary

interpretiveBoundary : Interpretive.InterpretiveFormalisationBoundary
interpretiveBoundary = Interpretive.canonicalInterpretiveFormalisationBoundary

coarseGrainingBoundary : Coarse.ConsumerRelativeCoarseGrainingBoundary
coarseGrainingBoundary = Coarse.canonicalConsumerRelativeCoarseGrainingBoundary

mdlBoundary : MDL.AdmissibleConsumerMDLBoundary
mdlBoundary = MDL.canonicalAdmissibleConsumerMDLBoundary

record WorldRepresentationBoundary : Set where
  constructor world-representation-boundary
  field
    worldAndTheoryAreSeparateCoordinates : Bool
    worldAndTheoryAreSeparateCoordinatesIsTrue :
      worldAndTheoryAreSeparateCoordinates ≡ true
    theoryMayChangeWithoutWorldChange : Bool
    theoryMayChangeWithoutWorldChangeIsTrue :
      theoryMayChangeWithoutWorldChange ≡ true
    observationMayEraseWorldDistinctions : Bool
    observationMayEraseWorldDistinctionsIsTrue :
      observationMayEraseWorldDistinctions ≡ true
    rechartingCannotRecoverErasedWorldDistinction : Bool
    rechartingCannotRecoverErasedWorldDistinctionIsTrue :
      rechartingCannotRecoverErasedWorldDistinction ≡ true
    couplingRequiresPropositionalRepresentation : Bool
    couplingRequiresPropositionalRepresentationIsFalse :
      couplingRequiresPropositionalRepresentation ≡ false
    consumerAdequacyMeansWorldExhaustion : Bool
    consumerAdequacyMeansWorldExhaustionIsFalse :
      consumerAdequacyMeansWorldExhaustion ≡ false
    observerRefinementAutomaticallyChangesWorld : Bool
    observerRefinementAutomaticallyChangesWorldIsFalse :
      observerRefinementAutomaticallyChangesWorld ≡ false

open WorldRepresentationBoundary public

canonicalWorldRepresentationBoundary : WorldRepresentationBoundary
canonicalWorldRepresentationBoundary =
  world-representation-boundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
