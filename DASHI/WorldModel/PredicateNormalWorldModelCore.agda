module DASHI.WorldModel.PredicateNormalWorldModelCore where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)

import DASHI.Core.ContactGateCore as Gate

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

    phiPromotesTruth : Bool
    psiPromotesTruth : Bool

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
  (model : PredicateNormalWorldModelCore)
  (observation : Observation model) : Set where
  constructor predicateNormalProposalBoundary
  field
    phiIsProposalOnly : phiPromotesTruth model ≡ false
    psiIsProposalOnly : psiPromotesTruth model ≡ false
    candidateGateDoesNotAutoPromote :
      Gate.promotesTruth
        (actionGate model (candidateActions model observation)) ≡ false

open PredicateNormalProposalBoundary public
