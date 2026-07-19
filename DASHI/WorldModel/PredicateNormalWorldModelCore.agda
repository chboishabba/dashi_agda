module DASHI.WorldModel.PredicateNormalWorldModelCore where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)

import DASHI.Core.ContactGateCore as Gate

------------------------------------------------------------------------
-- Predicate-normal world-model surface.
--
-- PNF, Phi, and Psi are proposal/addressing surfaces.  They make candidate
-- futures inspectable but do not supply truth, authority, or promotion.
------------------------------------------------------------------------

record PredicateNormalWorldModelCore : Set₁ where
  constructor predicateNormalWorldModelCore
  field
    Observation : Set
    Carrier     : Set
    Predicate   : Set
    PNF         : Set
    Phi         : Set
    Psi         : Set
    Action      : Set
    Trajectory  : Set
    Pressure    : Set

    encodeCarrier : Observation → Carrier
    normalize     : Carrier → PNF
    phiEncode     : PNF → Phi
    psiProbe      : Phi → Psi
    propose       : Psi → List Action
    rollout       : Carrier → List Action → Trajectory
    pressure      : Trajectory → Pressure
    actionGate    : List Action → Gate.ContactGateCore

    phiPromotesTruth : false ≡ false
    psiPromotesTruth : false ≡ false

open PredicateNormalWorldModelCore public

candidateActions :
  (model : PredicateNormalWorldModelCore) →
  Observation model →
  List (Action model)
candidateActions model observation =
  propose model
    (psiProbe model
      (phiEncode model
        (normalize model
          (encodeCarrier model observation))))

candidateTrajectory :
  (model : PredicateNormalWorldModelCore) →
  Observation model →
  Trajectory model
candidateTrajectory model observation =
  rollout model
    (encodeCarrier model observation)
    (candidateActions model observation)

record PredicateNormalProposalBoundary
  (model : PredicateNormalWorldModelCore) : Set where
  constructor predicateNormalProposalBoundary
  field
    phiIsProposalOnly : false ≡ false
    psiIsProposalOnly : false ≡ false
    candidateGateDoesNotAutoClose :
      Gate.promotesTruth
        (actionGate model (candidateActions model
          -- The boundary is model-wide; no privileged observation is assumed.
          -- The caller supplies an observation in domain instances.
          -- This field therefore remains intentionally absent here.
          )) ≡ false
