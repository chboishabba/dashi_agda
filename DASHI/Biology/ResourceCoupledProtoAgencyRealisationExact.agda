module DASHI.Biology.ResourceCoupledProtoAgencyRealisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Biology.ResourceCoupledLogisticReplicationExact as Resource
import DASHI.Biology.ResourceCoupledMetabolicOpenBalanceBridgeExact as Balance
import DASHI.Biology.ResourceCoupledMetabolicAdmissibilityExact as Admissibility
import DASHI.Biology.Cell.OpenMetabolicNetwork as OMN
import DASHI.Biology.Cell.MetabolicStoichiometricConservation as MSC
import DASHI.Biology.Cell.MetabolicOpenSystemBalance as MOB
import DASHI.Biology.AgenticMaterialsControlCore as Agentic

------------------------------------------------------------------------
-- RESOURCE-COUPLED PROTO-AGENCY REALISATION
--
-- Metabolic admissibility does not itself create agency.  A proto-agent
-- realisation must additionally ground the existing AgenticMaterial observation,
-- policy and actuation channels in the same resource/population state and prove
-- that the resulting closed-loop step agrees with the underlying coupled
-- dynamics on the realised state.
------------------------------------------------------------------------

record ResourceCoupledProtoAgencyRealisation
    (S : Resource.ResourceCoupledLogisticSystem)
    (M : Agentic.AgenticMaterial) : Set₁ where
  constructor resource-coupled-proto-agency-realisation
  field
    stateMap :
      Resource.ResourcePopulationState S → Agentic.State M

    observationMap :
      Resource.ResourcePopulationState S → Agentic.Observation M

    actionMap :
      Resource.ResourcePopulationState S → Agentic.Action M

    observationCommutes :
      (state : Resource.ResourcePopulationState S) →
      observationMap state
      ≡ Agentic.observe M (stateMap state)

    actionIsPolicy :
      (state : Resource.ResourcePopulationState S) →
      actionMap state
      ≡ Agentic.policy M (observationMap state)

    actuationRealisesCoupledStep :
      (state : Resource.ResourcePopulationState S) →
      stateMap (Resource.coupledStep S state)
      ≡ Agentic.actuate M (actionMap state) (stateMap state)

    resourceTarget : Resource.ResourcePopulationState S

    targetMatches :
      stateMap resourceTarget ≡ Agentic.target M

    observationReference : String
    policyReference : String
    actionReference : String
    targetReference : String
    realisationReference : String

open ResourceCoupledProtoAgencyRealisation public

------------------------------------------------------------------------
-- The closed-loop commuting theorem is derived from the three separate
-- observation / policy / actuation receipts rather than assumed directly.
------------------------------------------------------------------------

closedLoopCommutes :
  ∀ {S M} →
  (R : ResourceCoupledProtoAgencyRealisation S M) →
  (state : Resource.ResourcePopulationState S) →
  stateMap R (Resource.coupledStep S state)
  ≡ Agentic.closedLoopStep M (stateMap R state)
closedLoopCommutes {M = M} R state =
  trans
    (actuationRealisesCoupledStep R state)
    (trans
      (cong
        (λ action → Agentic.actuate M action (stateMap R state))
        (actionIsPolicy R state))
      (cong
        (λ observation →
          Agentic.actuate M
            (Agentic.policy M observation)
            (stateMap R state))
        (observationCommutes R state)))

------------------------------------------------------------------------
-- Target stability is inherited through the realisation, but only in the
-- realised AgenticMaterial fibre.  Injectivity of stateMap is not assumed.
------------------------------------------------------------------------

realisedTargetImageIsStable :
  ∀ {S M} →
  (R : ResourceCoupledProtoAgencyRealisation S M) →
  stateMap R (Resource.coupledStep S (resourceTarget R))
  ≡ stateMap R (resourceTarget R)
realisedTargetImageIsStable {M = M} R =
  trans
    (closedLoopCommutes R (resourceTarget R))
    (trans
      (cong (Agentic.closedLoopStep M) (targetMatches R))
      (trans
        (Agentic.closedLoopTargetFixed M)
        (sym (targetMatches R))))

realisedCorrectionImproves :
  ∀ {S M} →
  (R : ResourceCoupledProtoAgencyRealisation S M) →
  (state : Resource.ResourcePopulationState S) →
  (offTarget : stateMap R state ≡ Agentic.target M → Bool) →
  Agentic.better M
    (Agentic.defect M
      (stateMap R (Resource.coupledStep S state)))
    (Agentic.defect M (stateMap R state))
realisedCorrectionImproves {M = M} R state offTarget =
  subst
    (λ next →
      Agentic.better M
        (Agentic.defect M next)
        (Agentic.defect M (stateMap R state)))
    (sym (closedLoopCommutes R state))
    (Agentic.closedLoopCorrectionImproves M (stateMap R state) offTarget)

------------------------------------------------------------------------
-- Metabolic admissibility on the same resource coordinate remains a separate
-- dynamic receipt.  This joins the already-owned metabolic state to one
-- proto-agency step without identifying the two notions.
------------------------------------------------------------------------

record MetabolicallyAdmissibleProtoAgencyStep
    {S N Sto B}
    (Open : Balance.ResourceMetabolicOpenBalanceRealisation S N Sto B)
    (M : Agentic.AgenticMaterial)
    (Agency : ResourceCoupledProtoAgencyRealisation S M)
    (before : Resource.ResourcePopulationState S) : Set₁ where
  constructor metabolically-admissible-proto-agency-step
  field
    beforeAdmissibility :
      Admissibility.ResourceMetabolicAdmissibilityRealisation
        S N Sto B Open

    resourceMatchesBefore :
      Admissibility.resource beforeAdmissibility
      ≡ Resource.resource before

    metabolicPreservation :
      Admissibility.ResourceMetabolicAdmissibilityStep
        Open
        (Resource.population before)
        beforeAdmissibility

    agencyCorrection :
      (offTarget :
        stateMap Agency before ≡ Agentic.target M → Bool) →
      Agentic.better M
        (Agentic.defect M
          (stateMap Agency (Resource.coupledStep S before)))
        (Agentic.defect M (stateMap Agency before))

    joinReference : String

open MetabolicallyAdmissibleProtoAgencyStep public

canonicalAgencyCorrection :
  ∀ {S N Sto B Open M Agency before} →
  (Step : MetabolicallyAdmissibleProtoAgencyStep Open M Agency before) →
  (offTarget : stateMap Agency before ≡ Agentic.target M → Bool) →
  Agentic.better M
    (Agentic.defect M
      (stateMap Agency (Resource.coupledStep S before)))
    (Agentic.defect M (stateMap Agency before))
canonicalAgencyCorrection {Agency = Agency} {before = before} Step =
  realisedCorrectionImproves Agency before

------------------------------------------------------------------------
-- Authority boundaries.
------------------------------------------------------------------------

data MetabolismMeansObservationPermission : Set where

data MetabolismMeansPolicyPermission : Set where

data MetabolismMeansCorrectiveAgencyPermission : Set where

data ProtoAgencyMeansOpenEndedEvolutionPermission : Set where

data ProtoAgencyMeansAbiogenesisHistoryPermission : Set where

data RealisedTargetImageMeansUniqueResourceTargetPermission : Set where

metabolismDoesNotByItselfSupplyObservation :
  MetabolismMeansObservationPermission → ⊥
metabolismDoesNotByItselfSupplyObservation ()

metabolismDoesNotByItselfSupplyPolicy :
  MetabolismMeansPolicyPermission → ⊥
metabolismDoesNotByItselfSupplyPolicy ()

metabolismDoesNotByItselfSupplyCorrectiveAgency :
  MetabolismMeansCorrectiveAgencyPermission → ⊥
metabolismDoesNotByItselfSupplyCorrectiveAgency ()

protoAgencyDoesNotByItselfSupplyOpenEndedEvolution :
  ProtoAgencyMeansOpenEndedEvolutionPermission → ⊥
protoAgencyDoesNotByItselfSupplyOpenEndedEvolution ()

protoAgencyDoesNotProveUniqueAbiogenesisHistory :
  ProtoAgencyMeansAbiogenesisHistoryPermission → ⊥
protoAgencyDoesNotProveUniqueAbiogenesisHistory ()

realisedTargetImageDoesNotProveUniqueResourceTarget :
  RealisedTargetImageMeansUniqueResourceTargetPermission → ⊥
realisedTargetImageDoesNotProveUniqueResourceTarget ()

record ResourceCoupledProtoAgencyBoundary : Set where
  constructor resource-coupled-proto-agency-boundary
  field
    observationRequiresExplicitRealisation : Bool
    policyRequiresExplicitRealisation : Bool
    actuationRequiresExplicitRealisation : Bool
    closedLoopCommutationIsDerived : Bool
    targetAlignmentRemainsExplicit : Bool
    metabolismAutomaticallyCreatesAgency : Bool
    protoAgencyAutomaticallyCreatesOpenEndedEvolution : Bool
    protoAgencyProvesUniqueAbiogenesisHistory : Bool

canonicalResourceCoupledProtoAgencyBoundary :
  ResourceCoupledProtoAgencyBoundary
canonicalResourceCoupledProtoAgencyBoundary =
  resource-coupled-proto-agency-boundary
    true true true true true false false false
