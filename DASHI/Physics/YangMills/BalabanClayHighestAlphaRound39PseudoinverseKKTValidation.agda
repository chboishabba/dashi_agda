module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound39PseudoinverseKKTValidation where

------------------------------------------------------------------------
-- Cumulative Round Thirty Nine validation root.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound37ProjectorResidualValidation

import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanSelectedVariationKKTMultiplierExact as Stationary
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanWilsonMobiusAtomDecompositionExact as Mobius
import DASHI.Physics.YangMills.BalabanWilsonD4SubsetCharacterExact as D4
import DASHI.Physics.YangMills.BalabanP33OrientedWilsonD4TransportExact as Oriented
import DASHI.Physics.YangMills.BalabanSelectedVariationResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanP33ReducedPhysicalHessianExact as Reduced

import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanSelectedConstraintAnnihilatorKKTExact as Annihilator
import DASHI.Physics.YangMills.BalabanSelectedRawExtractorConstraintDefectExact as RawDefect
import DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact as Boundary
import DASHI.Physics.YangMills.BalabanP33SingletonBudgetFeasibilityExact as Budget
import DASHI.Physics.YangMills.BalabanP33NonorthogonalPhysicalFrameExact as Frame
import DASHI.Physics.YangMills.BalabanP33FiniteKKTBlockGreenExact as BlockGreen
import DASHI.Physics.YangMills.BalabanP33FiniteKKTBlockTiltExact as BlockTilt
import DASHI.Physics.YangMills.BalabanP33CovariantD4TransportCocycleBoundaryExact as CovariantD4
import DASHI.Physics.YangMills.BalabanP33PhysicalFactorRoleDeepEnvelopeExact as Roles
import DASHI.Physics.YangMills.BalabanYangMillsGapAuthorityHierarchyExact as Gap

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.List.Base using (length)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _≤_)

fullInversePromotesToPseudoinverse :
  ∀ {Multiplier} →
  KKT.FiniteKKTProjectorData Multiplier →
  Pseudo.FiniteKKTPseudoinverseData Multiplier
fullInversePromotesToPseudoinverse = Pseudo.fullInverseToPseudoinverse

pseudoinverseProjectorIdempotenceRegression :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    vector coordinate →
  Pseudo.admissibleProject pseudoData
    (Pseudo.admissibleProject pseudoData vector) coordinate
  ≡ Pseudo.admissibleProject pseudoData vector coordinate
pseudoinverseProjectorIdempotenceRegression = Pseudo.projectIdempotent

annihilatorProducesKKTMultiplierRegression :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    covector →
  Annihilator.AnnihilatesConstraintKernel pseudoData covector →
  Annihilator.KKTMultiplierWitness pseudoData covector
annihilatorProducesKKTMultiplierRegression =
  Annihilator.selectedKKTMultiplierExistence

rawExtractorDefectPairingRegression :
  ∀ {Multiplier}
    (stationaryData : Stationary.SelectedKKTStationaryData Multiplier)
    bondField plaquette →
  Stationary.firstVariation stationaryData
    (KKT.selectedConstraintRepair
      (Stationary.projectorData stationaryData)
      (Boundary.rawPlaquetteSingletonExtractor bondField plaquette))
  ≡ KKT.multiplierDot
      (Stationary.projectorData stationaryData)
      (Stationary.kktMultiplier stationaryData)
      (RawDefect.rawExtractorConstraintDefect
        (Stationary.projectorData stationaryData) bondField plaquette)
rawExtractorDefectPairingRegression =
  RawDefect.rawExtractorProjectorDefectPairingExact

balancedSingletonBudgetRegression :
  Budget.balancedAlpha + Budget.balancedBeta
  ≡ Budget.singletonBudget
balancedSingletonBudgetRegression = Budget.balancedSplitExact

physicalRoleCountRegression : ∀ placement →
  length (Roles.placementRoles placement) ≡ 4
physicalRoleCountRegression = Roles.placementRoleCountExact

finiteGaussianIsNotOSRegression :
  Gap.finiteBackgroundGaussian ≡ Gap.osHamiltonianSpectral → ⊥
finiteGaussianIsNotOSRegression = Gap.finiteIsNotOS
