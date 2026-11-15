module DASHI.Biology.BH4JointFluxFeasibilityExact where

open import DASHI.Core.Prelude

import DASHI.Biology.BH4SystemStateExact as System
import DASHI.Biology.BH4CompartmentKineticStateExact as Parameters
import DASHI.Biology.Molecular.BH4PanelStoichiometricMatrixExact as Matrix
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- Joint flux feasibility surface.
--
-- This owner records the result of checking one supplied candidate against the
-- finite internal stoichiometric matrix, source-paid flux bounds and explicit
-- environmental/compartment exchange coordinates.  It is a witness checker,
-- not a global optimiser.
------------------------------------------------------------------------

data FluxFeasibilityStatus : Set where
  feasible : FluxFeasibilityStatus
  infeasible : FluxFeasibilityStatus
  underdetermined : FluxFeasibilityStatus

record BH4JointFluxFeasibility : Set where
  constructor bh4-joint-flux-feasibility
  field
    status : FluxFeasibilityStatus
    matrixReference : String
    parameterReference : String
    candidateReference : String
    missingFluxBounds : List String
    missingFluxValues : List String
    missingExternalExchange : List String
    candidateFluxBalanceWitness : Bool
    candidateFluxBalanceWitnessReference : String
    sameStateReference : String
    measuredOrDerivedReference : String

open BH4JointFluxFeasibility public

canonicalUnderdeterminedFluxFeasibility : BH4JointFluxFeasibility
canonicalUnderdeterminedFluxFeasibility =
  bh4-joint-flux-feasibility
    underdetermined
    "BH4 panel stoichiometric matrix; QDPR finite column paid, panel expansion executable"
    "BH4 parameter evidence template; unresolved != zero"
    "no complete same-state candidate supplied"
    ( "reaction-specific quantitative flux bounds remain source-dependent" ∷ [] )
    ( "complete reaction flux vector not supplied" ∷ [] )
    ( "compartment transport/oxidation exchange vector not supplied" ∷ [] )
    false
    "no System.FluxBalanceWitness manufactured while coordinates are unresolved"
    "same-state coordinate unresolved"
    "quantitative evidence incomplete"

candidateSystemFluxWitnessType : System.BH4SystemState → Set
candidateSystemFluxWitnessType = System.FluxBalanceWitness

parameterStateType : Set
parameterStateType = Parameters.BH4QuantitativeState

matrixType : Set
matrixType = Matrix.BH4PanelStoichiometricMatrix

record BH4FluxFeasibilityBoundary : Set where
  constructor bh4-flux-feasibility-boundary
  field
    missingFluxBoundMayBeSubstitutedWithZero : Bool
    missingFluxBoundMayBeSubstitutedWithZeroIsFalse :
      missingFluxBoundMayBeSubstitutedWithZero ≡ false
    candidateInfeasibleProvesNoFeasibleStateExists : Bool
    candidateInfeasibleProvesNoFeasibleStateExistsIsFalse :
      candidateInfeasibleProvesNoFeasibleStateExists ≡ false
    feasibleFluxStateProvesAllocatorCausality : Bool
    feasibleFluxStateProvesAllocatorCausalityIsFalse :
      feasibleFluxStateProvesAllocatorCausality ≡ false
    feasibleFluxStateProvesDiseaseMechanism : Bool
    feasibleFluxStateProvesDiseaseMechanismIsFalse :
      feasibleFluxStateProvesDiseaseMechanism ≡ false
    externalExchangeMayBeCollapsedIntoInternalMatrix : Bool
    externalExchangeMayBeCollapsedIntoInternalMatrixIsFalse :
      externalExchangeMayBeCollapsedIntoInternalMatrix ≡ false
    crossTimeMeasurementsCreateSameStateWitness : Bool
    crossTimeMeasurementsCreateSameStateWitnessIsFalse :
      crossTimeMeasurementsCreateSameStateWitness ≡ false

open BH4FluxFeasibilityBoundary public

canonicalBH4FluxFeasibilityBoundary : BH4FluxFeasibilityBoundary
canonicalBH4FluxFeasibilityBoundary =
  bh4-flux-feasibility-boundary false refl false refl false refl false refl false refl false refl

canonicalBH4JointFluxFeasibilityReceipt : Receipt.GenericReceipt
canonicalBH4JointFluxFeasibilityReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 joint flux feasibility"
    "DASHI.Biology.BH4JointFluxFeasibilityExact"
    "finite internal stoichiometric matrix + source-paid flux bounds + explicit exchange + supplied candidate -> witness check of S*v+e=0"
    "returns feasible, infeasible-for-this-candidate, or underdetermined; only a fully paid balanced candidate can carry a state-indexed FluxBalanceWitness reference"
    "missing bounds are not zero; failed candidate is not global infeasibility; feasible flux is not allocator causality, disease mechanism or clinical prediction"
    "python3 scripts/run_bh4_flux_feasibility.py --matrix MATRIX --parameters PARAMETERS --candidate CANDIDATE"
