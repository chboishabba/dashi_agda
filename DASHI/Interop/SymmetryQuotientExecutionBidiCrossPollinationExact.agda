module DASHI.Interop.SymmetryQuotientExecutionBidiCrossPollinationExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.ParetoSymmetryQuotientAdmissionExact as ParetoSymmetry
import DASHI.ComputerScience.RSA260SymmetryCensusOrbitQuotientBidiExact as RSA
import DASHI.Moonshine.Monster369NDimParetoTetrationBridgeExact as MonsterNDim

------------------------------------------------------------------------
-- THIN BIDIRECTIONAL EXECUTION ADAPTER
--
-- Reuse the existing Pareto symmetry-admission ontology.  RSA contributes an
-- execution-level extension:
--
--   semantic/order automorphism
--   + operator equivariance
--   + explicit quotient carrier
--   + explicit lift/reconstruction
--   + execution comparison.
--
-- This is an adapter, not a second planner or a replacement for the owning
-- Pareto/369/Monster/RSA theories.
------------------------------------------------------------------------

record ExecutableSymmetryReducerBoundary : Set where
  constructor executable-symmetry-reducer-boundary
  field
    invertibleCarrierActionRequired : Bool
    consumerOrCostInvarianceRequired : Bool
    eligibilityOrDomainPreservationRequired : Bool
    operatorEquivarianceRequired : Bool
    explicitQuotientRequired : Bool
    exactLiftOrReconstructionRequired : Bool
    measuredReductionRequiredForPerformanceClaim : Bool
    carrierSymmetryAloneSufficient : Bool
open ExecutableSymmetryReducerBoundary public

canonicalExecutableSymmetryReducerBoundary : ExecutableSymmetryReducerBoundary
canonicalExecutableSymmetryReducerBoundary =
  executable-symmetry-reducer-boundary
    true true true true true true true false

paretoBoundary : ParetoSymmetry.ParetoSymmetryQuotientBoundary
paretoBoundary = ParetoSymmetry.canonicalParetoSymmetryQuotientBoundary

rsaExecutionBoundary : RSA.RSA260SymmetryExecutionRoadmapBoundary
rsaExecutionBoundary = RSA.currentRSA260SymmetryExecutionRoadmapBoundary

monsterNDimBoundary : MonsterNDim.Monster369NDimParetoTetrationBoundary
monsterNDimBoundary = MonsterNDim.canonicalMonster369NDimParetoTetrationBoundary

------------------------------------------------------------------------
-- Paid demonstration from RSA synthetic execution.
------------------------------------------------------------------------

record BidiExecutionDemonstration : Set where
  constructor bidi-execution-demonstration
  field
    negativeCensusCanFailClosed : Bool
    commutingActionCanBeAdmitted : Bool
    quotientCanReduceCarrier : Bool
    reducedOperatorCanIntertwineWithLift : Bool
    reducedKernelCanLiftToFullKernel : Bool
    fullCarrierVerificationCanCloseTheLoop : Bool
    demonstrationUsesProductionRSA260 : Bool
open BidiExecutionDemonstration public

canonicalBidiExecutionDemonstration : BidiExecutionDemonstration
canonicalBidiExecutionDemonstration = bidi-execution-demonstration
  true true true true true true false

------------------------------------------------------------------------
-- Return path to 369 / colouring / Monster candidate generation.
--
-- The practical effect is a uniform promotion checklist.  Any proposed signed
-- voxel reflection, cube-face quotient, colouring local reducer, Monster orbit,
-- or N-dimensional symmetry must provide these receipts before it is allowed to
-- erase candidates or claim work reduction.
------------------------------------------------------------------------

data SymmetryPromotionLeaf : Set where
  provideInvertibleAction : SymmetryPromotionLeaf
  proveConsumerInvariantOrCovariant : SymmetryPromotionLeaf
  proveDomainOrEligibilityPreserved : SymmetryPromotionLeaf
  proveOperatorEquivariance : SymmetryPromotionLeaf
  constructQuotientCarrier : SymmetryPromotionLeaf
  constructExactLift : SymmetryPromotionLeaf
  verifyLiftedResultOnOriginalCarrier : SymmetryPromotionLeaf
  measureReduction : SymmetryPromotionLeaf

record CrossLanePromotionChecklist : Set where
  constructor cross-lane-promotion-checklist
  field
    actionPaid : Bool
    consumerInvariantPaid : Bool
    domainPaid : Bool
    operatorEquivariancePaid : Bool
    quotientPaid : Bool
    liftPaid : Bool
    upstairsVerificationPaid : Bool
    measuredReductionPaid : Bool
open CrossLanePromotionChecklist public

rsaPairOrbitChecklist : CrossLanePromotionChecklist
rsaPairOrbitChecklist = cross-lane-promotion-checklist
  true true true true true true true true

base369GenericChecklist : CrossLanePromotionChecklist
base369GenericChecklist = cross-lane-promotion-checklist
  true false false false false false false false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data ParetoAutomorphismImpliesOperatorEquivariance : Set where
data OperatorEquivarianceImpliesSemanticAdmissibility : Set where
data QuotientExistsImpliesResultLifts : Set where
data ExactLiftImpliesMeasuredSpeedup : Set where

data RSAExecutionImpliesMonsterExecution : Set where

paretoAutomorphismDoesNotCreateOperatorEquivariance :
  ParetoAutomorphismImpliesOperatorEquivariance → ⊥
paretoAutomorphismDoesNotCreateOperatorEquivariance ()

operatorEquivarianceDoesNotCreateSemanticAdmissibility :
  OperatorEquivarianceImpliesSemanticAdmissibility → ⊥
operatorEquivarianceDoesNotCreateSemanticAdmissibility ()

quotientDoesNotCreateLift : QuotientExistsImpliesResultLifts → ⊥
quotientDoesNotCreateLift ()

exactLiftDoesNotCreateMeasuredSpeedup : ExactLiftImpliesMeasuredSpeedup → ⊥
exactLiftDoesNotCreateMeasuredSpeedup ()

rsaExecutionDoesNotCreateMonsterExecution : RSAExecutionImpliesMonsterExecution → ⊥
rsaExecutionDoesNotCreateMonsterExecution ()
