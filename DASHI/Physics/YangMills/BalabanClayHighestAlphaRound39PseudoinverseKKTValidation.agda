module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound39PseudoinverseKKTValidation where

------------------------------------------------------------------------
-- Cumulative Round Thirty Nine validation root.
--
-- Round 39 repairs the invalid exploratory reduced-frame proof, imports the
-- complete Round-38 finite KKT/Mobius/D4 algebra, and adds:
--
-- * a redundancy-safe Moore--Penrose projector surface;
-- * the finite annihilator/kernel = adjoint-image KKT theorem;
-- * literal raw-extractor constraint-defect and multiplier pairing;
-- * exact singleton-budget feasibility and cancellation-before-norm;
-- * rational nonorthogonal physical frames and generalized coercivity;
-- * an exact finite KKT block solve and full-block tilt algebra;
-- * typed geometric/covariant D4 cocycle separation;
-- * a physical four-role deep-envelope enumeration;
-- * a fail-closed hierarchy from finite Gaussian stability to OS mass gap.
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
    (data : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    vector coordinate →
  Pseudo.admissibleProject data
    (Pseudo.admissibleProject data vector) coordinate
  ≡ Pseudo.admissibleProject data vector coordinate
pseudoinverseProjectorIdempotenceRegression = Pseudo.projectIdempotent

annihilatorProducesKKTMultiplierRegression :
  ∀ {Multiplier}
    (data : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    covector →
  Annihilator.AnnihilatesConstraintKernel data covector →
  Annihilator.KKTMultiplierWitness data covector
annihilatorProducesKKTMultiplierRegression =
  Annihilator.selectedKKTMultiplierExistence

rawExtractorDefectPairingRegression :
  ∀ {Multiplier}
    (data : Stationary.SelectedKKTStationaryData Multiplier)
    field plaquette →
  Stationary.firstVariation data
    (KKT.selectedConstraintRepair
      (Stationary.projectorData data)
      (Boundary.rawPlaquetteSingletonExtractor field plaquette))
  ≡ KKT.multiplierDot
      (Stationary.projectorData data)
      (Stationary.kktMultiplier data)
      (RawDefect.rawExtractorConstraintDefect
        (Stationary.projectorData data) field plaquette)
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
