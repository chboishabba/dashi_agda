module DASHI.Biology.BH4ReactionNetworkRunnerReceipt where

open import DASHI.Core.Prelude

import DASHI.Biology.BH4SystemStateExact as System
import DASHI.Biology.Molecular.BH4MolecularStoichiometryExact as Stoich
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- Formal receipt for the executable stoichiometric/topological runner.
------------------------------------------------------------------------

qdprRunnerState : System.BH4SystemState
qdprRunnerState =
  System.bh4SystemState
    "QDPR-RHEA32253-STOICHIOMETRIC-RUNNER"
    []
    []
    "transport not supplied by stoichiometric runner"
    "redox identity present only through reaction participants; no measured redox state"
    "RHEA:32253 exact reaction identity; not a same-time in-vivo measurement"
    false
    false

qdprRunnerPayment : System.BH4SystemPayment
qdprRunnerPayment =
  System.bh4SystemPayment
    qdprRunnerState
    "DASHI.Biology.Molecular.BH4MolecularStoichiometryExact.qdprAtomsConserved / qdprChargeConserved"
    true
    true
    false
    false
    false
    false

qdprRunnerReactionIdentityPaid : System.reactionIdentityPaid qdprRunnerPayment ≡ true
qdprRunnerReactionIdentityPaid = refl

qdprRunnerWholeSystemFluxMeasured : System.wholeSystemFluxMeasured qdprRunnerState ≡ false
qdprRunnerWholeSystemFluxMeasured = refl

qdprRunnerStoichiometryPaid : Stoich.qdprAtomAndChargeBalanced ≡ true
qdprRunnerStoichiometryPaid = refl

record BH4ReactionRunnerBoundary : Set where
  constructor bh4-reaction-runner-boundary
  field
    stoichiometricRunnerCreatesMeasuredFlux : Bool
    stoichiometricRunnerCreatesMeasuredFluxIsFalse : stoichiometricRunnerCreatesMeasuredFlux ≡ false
    topologicalReachabilityCreatesKineticLaw : Bool
    topologicalReachabilityCreatesKineticLawIsFalse : topologicalReachabilityCreatesKineticLaw ≡ false
    reactionGraphCreatesCompartmentState : Bool
    reactionGraphCreatesCompartmentStateIsFalse : reactionGraphCreatesCompartmentState ≡ false
    runnerStateCreatesAllocatorCompetition : Bool
    runnerStateCreatesAllocatorCompetitionIsFalse : runnerStateCreatesAllocatorCompetition ≡ false
    runnerStateCreatesDiseaseMechanism : Bool
    runnerStateCreatesDiseaseMechanismIsFalse : runnerStateCreatesDiseaseMechanism ≡ false

open BH4ReactionRunnerBoundary public

canonicalBH4ReactionRunnerBoundary : BH4ReactionRunnerBoundary
canonicalBH4ReactionRunnerBoundary =
  bh4-reaction-runner-boundary
    false refl false refl false refl false refl false refl

canonicalBH4ReactionNetworkRunnerReceipt : Receipt.GenericReceipt
canonicalBH4ReactionNetworkRunnerReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 biochemical reaction-network runner"
    "DASHI.Biology.BH4ReactionNetworkRunnerReceipt"
    "scripts/run_bh4_reaction_network.py --qdpr; RHEA:32253 atom/charge balance and finite substrate-product graph"
    "projects exact reaction identity and finite stoichiometry into BH4SystemState/BH4SystemPayment with participantIdentityPaid=true and reactionIdentityPaid=true"
    "wholeSystemFluxMeasured=false; kinetics, compartment state, transport, allocator competition and disease mechanism remain unpaid"
    "python3 scripts/run_bh4_reaction_network.py --qdpr --output-prefix artifacts/biology/bh4-qdpr-network"
