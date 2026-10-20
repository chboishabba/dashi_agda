module DASHI.Biology.BH4Chemistry369RunnerRegression where

open import DASHI.Core.Prelude

import DASHI.Biology.Molecular.BH4RheaChEBIReactionExact as Reaction
import DASHI.Biology.Molecular.BH4MolecularStoichiometryExact as Stoich
import DASHI.Interop.BH4Atomic369RefinementExact as Refinement
import DASHI.Biology.NonginNangNitrogenOxideRefinementExact as NongNang
import DASHI.Biology.BH4ReactionNetworkRunnerReceipt as Runner
import DASHI.Unified.BH4BiochemicalCrossScaleAdapter as Unified

------------------------------------------------------------------------
-- Regression-first contract for the chemistry / 369 / runner max-cut.
------------------------------------------------------------------------

qdprReactionIsRhea17869 : Reaction.rheaId Reaction.qdprGenericReaction ≡ "RHEA:17869"
qdprReactionIsRhea17869 = refl

qdprReactionCarriesBH4SpecificDirectedChild :
  Reaction.specificDirectedRheaId Reaction.qdprGenericReaction ≡ "RHEA:32253"
qdprReactionCarriesBH4SpecificDirectedChild = refl

qdprStoichiometryBalanced : Stoich.qdprAtomAndChargeBalanced ≡ true
qdprStoichiometryBalanced = refl

stoichiometricBalanceDoesNotCreateKinetics :
  Stoich.BH4StoichiometryBoundary.balancedReactionCreatesKineticLaw
    Stoich.canonicalBH4StoichiometryBoundary
  ≡ false
stoichiometricBalanceDoesNotCreateKinetics = refl

atomicInventoryDoesNotSolveMolecularHamiltonian :
  Refinement.BH4Atomic369Boundary.atomicInventorySolvesMolecularHamiltonian
    Refinement.canonicalBH4Atomic369Boundary
  ≡ false
atomicInventoryDoesNotSolveMolecularHamiltonian = refl

coarseBH4ProjectionDoesNotReconstructFineState :
  Refinement.BH4Atomic369Boundary.coarseBH4AvailabilityReconstructsFineChemicalState
    Refinement.canonicalBH4Atomic369Boundary
  ≡ false
coarseBH4ProjectionDoesNotReconstructFineState = refl

chemistryIsNotLiterally369 :
  Refinement.BH4Atomic369Boundary.chemistryIsLiterally369
    Refinement.canonicalBH4Atomic369Boundary
  ≡ false
chemistryIsNotLiterally369 = refl

coarseNitrogenOxideCannotServeFineChemicalConsumer :
  NongNang.CoarseChemicalDescent → ⊥
coarseNitrogenOxideCannotServeFineChemicalConsumer =
  Refinement.coarseNitrogenOxideCannotServeFineChemicalConsumer

runnerDoesNotInventMeasuredFlux :
  Runner.BH4ReactionRunnerBoundary.stoichiometricRunnerCreatesMeasuredFlux
    Runner.canonicalBH4ReactionRunnerBoundary
  ≡ false
runnerDoesNotInventMeasuredFlux = refl

runnerStateIsNotDiseaseMechanism :
  Runner.BH4ReactionRunnerBoundary.runnerStateCreatesDiseaseMechanism
    Runner.canonicalBH4ReactionRunnerBoundary
  ≡ false
runnerStateIsNotDiseaseMechanism = refl

crossScaleAdapterDoesNotCreateAtomsToCellsDerivation :
  Unified.BH4CrossScaleBoundary.adapterCreatesFirstPrinciplesAtomsToCellsDerivation
    Unified.canonicalBH4CrossScaleBoundary
  ≡ false
crossScaleAdapterDoesNotCreateAtomsToCellsDerivation = refl

crossScaleAdapterDoesNotCreateDiseaseCausation :
  Unified.BH4CrossScaleBoundary.adapterCreatesDiseaseCausation
    Unified.canonicalBH4CrossScaleBoundary
  ≡ false
crossScaleAdapterDoesNotCreateDiseaseCausation = refl
