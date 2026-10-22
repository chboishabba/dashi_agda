module DASHI.WorldModel.VERIDExperimentProofSearchBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.DependencyPullbackCore as Pullback
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Planner
import DASHI.Core.ProofSearchExperimentalParetoCrossPollinationExact as Pareto
import DASHI.Core.ProofExperimentAction369IntegrationExact as Cybernetic
import DASHI.Reasoning.AristotleActiveExperimentalProofSearchLoopExact as Search
import DASHI.WorldModel.ActionConditionedWorldModelCore as World
import DASHI.WorldModel.VERIDLabWorldModelInstanceExact as Lab

------------------------------------------------------------------------
-- Reuse-only bridge: the experiment is a consumer-relative observation,
-- the action is separately admitted, and lab contact additionally needs
-- safety, conformity and reconciliation evidence. No new proof-search
-- kernel or robot semantics is introduced.
------------------------------------------------------------------------

record ExperimentToLabContact (lab : Lab.LabWorldModelInstance) : Set₁ where
  constructor experimentToLabContact
  field
    consumerWorld : Set
    consumer : consumerWorld → Set
    bundle : Synthesis.ExperimentBundle consumerWorld
    compatible : consumerWorld → Set
    plan : Planner.SequentialConsumerPlan consumer compatible
    sourceWorld : consumerWorld
    sourceCompatible : compatible sourceWorld
    observed : Synthesis.Observation bundle
    observedExact : Synthesis.observe bundle sourceWorld ≡ observed
    state : World.State (Lab.world lab)
    dependency : World.Dependency (Lab.world lab)
    contact : Lab.LabExecutionContact lab state dependency
    evidenceReference : String

open ExperimentToLabContact public

experimentContactIsGoverned :
  (lab : Lab.LabWorldModelInstance) →
  (bridge : ExperimentToLabContact lab) →
  World.dependencyStatus (Lab.world lab) (dependency bridge)
    ≡ Pullback.live
experimentContactIsGoverned lab bridge =
  Lab.contactHasLiveDependency lab (state bridge)
    (dependency bridge) (contact bridge)

------------------------------------------------------------------------
-- Finite counterexample: same coarse observation, different downstream
-- decision. A one-bit measurement separates this particular collision.
-- Separation is not a claim of global physical model sufficiency.
------------------------------------------------------------------------

coarse : Bool → Bool
coarse _ = false

fine : Synthesis.ExperimentBundle Bool
fine = Synthesis.experimentBundle Bool
  (λ b → b) 1
  "finite bounded two-world discriminator"
  "symbolic identity fixture; physical calibration not claimed"

collapsed : coarse false ≡ coarse true
collapsed = refl

separated : Synthesis.BundleSeparates fine false true
separated = Synthesis.bundleSeparates (λ ())

finiteCollision :
  Synthesis.CurrentObserverCollision coarse
finiteCollision = Synthesis.currentObserverCollision false true collapsed

finiteDiscriminator :
  Synthesis.DiscriminatingLanguageExtension coarse
finiteDiscriminator =
  Synthesis.discriminatingLanguageExtension
    finiteCollision fine separated

joinedSeparates :
  Synthesis.joinedObservation coarse fine false
    ≡ Synthesis.joinedObservation coarse fine true → ⊥
joinedSeparates =
  Synthesis.extensionJoinSeparates finiteDiscriminator

------------------------------------------------------------------------
-- Existing owners are retained as formal import anchors rather than
-- copied / weakened.
------------------------------------------------------------------------

searchInitialStage : Search.SearchIteration
searchInitialStage = Search.initialIteration

paretoAuthorityBoundary : Pareto.ProofSearchExperimentalParetoBoundary
paretoAuthorityBoundary = Pareto.canonicalProofSearchExperimentalParetoBoundary

cyberneticAuthorityBoundary : Cybernetic.IntegratedCyberneticBoundary
cyberneticAuthorityBoundary = Cybernetic.canonicalIntegratedCyberneticBoundary
