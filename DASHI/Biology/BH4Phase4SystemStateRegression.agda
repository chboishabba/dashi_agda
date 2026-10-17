module DASHI.Biology.BH4Phase4SystemStateRegression where

open import DASHI.Core.Prelude

import DASHI.Biology.Molecular.BH4PanelStoichiometricMatrixExact as Matrix
import DASHI.Biology.BH4CompartmentKineticStateExact as Parameters
import DASHI.Biology.BH4NOSCouplingEvidenceExact as Evidence
import DASHI.Biology.BH4NOSCouplingSameObjectExact as NOS
import DASHI.Biology.BH4JointFluxFeasibilityExact as Flux
import DASHI.Biology.BH4OpenMetabolicNetworkAdapterExact as OpenNetwork
import DASHI.Biology.BH4Phase4RoadmapExact as Roadmap

------------------------------------------------------------------------
-- Regression-first contract for the Phase-4 system-state max-cut.
------------------------------------------------------------------------

matrixDoesNotInventMissingChemistry :
  Matrix.BH4PanelMatrixBoundary.formulaIncompleteReactionBecomesZeroColumn
    Matrix.canonicalBH4PanelMatrixBoundary
  ≡ false
matrixDoesNotInventMissingChemistry = refl

unresolvedParameterIsNotZeroMeasurement :
  Parameters.BH4ParameterBoundary.unresolvedParameterMayBeReadAsMeasuredZero
    Parameters.canonicalBH4ParameterBoundary
  ≡ false
unresolvedParameterIsNotZeroMeasurement = refl

compartmentIdentityCannotBeDropped :
  Parameters.BH4ParameterBoundary.sameMoleculeDifferentCompartmentMayBeCollapsed
    Parameters.canonicalBH4ParameterBoundary
  ≡ false
compartmentIdentityCannotBeDropped = refl

nosProteinPresenceDoesNotPayCouplingTransition :
  NOS.BH4NOSSameObjectBoundary.proteinPresencePaysCouplingTransition
    NOS.canonicalBH4NOSSameObjectBoundary
  ≡ false
nosProteinPresenceDoesNotPayCouplingTransition = refl

noAndN2oRemainDistinctAcrossSameObjectBridge :
  NOS.BH4NOSSameObjectBoundary.nitrousOxideMayStandForNitricOxideProduct
    NOS.canonicalBH4NOSSameObjectBoundary
  ≡ false
noAndN2oRemainDistinctAcrossSameObjectBridge = refl

nos3EvidenceDoesNotGlobalizeToNOS1 :
  Evidence.NOS3EvidenceBoundary.nos3EvidenceGlobalizesToNOS1
    Evidence.canonicalNOS3EvidenceBoundary
  ≡ false
nos3EvidenceDoesNotGlobalizeToNOS1 = refl

nos3ExperimentalSystemDoesNotBecomeSameSingleCell :
  NOS.BH4NOSSameObjectBoundary.nos3ExperimentalSystemEvidencePaysSameSingleCellState
    NOS.canonicalBH4NOSSameObjectBoundary
  ≡ false
nos3ExperimentalSystemDoesNotBecomeSameSingleCell = refl

missingBoundsProduceUnderdeterminedNotZeroFlux :
  Flux.BH4FluxFeasibilityBoundary.missingFluxBoundMayBeSubstitutedWithZero
    Flux.canonicalBH4FluxFeasibilityBoundary
  ≡ false
missingBoundsProduceUnderdeterminedNotZeroFlux = refl

feasibleFluxDoesNotProveDiseaseMechanism :
  Flux.BH4FluxFeasibilityBoundary.feasibleFluxStateProvesDiseaseMechanism
    Flux.canonicalBH4FluxFeasibilityBoundary
  ≡ false
feasibleFluxDoesNotProveDiseaseMechanism = refl

exchangeIsNotInternalReaction :
  OpenNetwork.BH4OpenMetabolicBoundary.externalExchangeMayBeCollapsedIntoInternalStoichiometry
    OpenNetwork.canonicalBH4OpenMetabolicBoundary
  ≡ false
exchangeIsNotInternalReaction = refl

wholeSystemFluxAttemptHasOccurred : Roadmap.wholeSystemFluxBalanceAttempted ≡ true
wholeSystemFluxAttemptHasOccurred = refl

firstWholeSystemFluxOutcomeIsUnderdetermined :
  Roadmap.firstJointFluxOutcome ≡ Flux.underdetermined
firstWholeSystemFluxOutcomeIsUnderdetermined = refl

underdeterminedDoesNotMeanMechanismFalse :
  Roadmap.BH4Phase4Boundary.underdeterminedMeansMechanismFalse
    Roadmap.canonicalBH4Phase4Boundary
  ≡ false
underdeterminedDoesNotMeanMechanismFalse = refl
