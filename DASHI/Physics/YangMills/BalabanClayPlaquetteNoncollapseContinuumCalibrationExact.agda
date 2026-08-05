module DASHI.Physics.YangMills.BalabanClayPlaquetteNoncollapseContinuumCalibrationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions", Communications in Mathematical
-- Physics 31 (1973), 83--112. DOI: 10.1007/BF01645738.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II", Communications in
-- Mathematical Physics 42 (1975), 281--305. DOI: 10.1007/BF01608978.
--
-- Pietro Menotti and Andrea Pelissetto,
-- "General proof of Osterwalder-Schrader positivity for the Wilson action",
-- Communications in Mathematical Physics 113 (1987), 369--373.
-- DOI: 10.1007/BF01221251.
--
-- DASHI CONTRIBUTION
--
-- Fix a concrete noncollapse budget for a centred local plaquette/curvature
-- observable.  If its leading Gaussian OS norm is at least 1/16, the full
-- interacting correction is no worse than -1/32, and continuum cutoff removal
-- changes the OS norm by at most 1/64 in the adverse direction, then
--
--   lattice OS norm   >= 1/32,
--   continuum OS norm >= 1/64 > 0.
--
-- This cleanly separates the three physical estimates that must be proved:
-- the Gaussian covariance lower bound, the interacting cumulant error, and the
-- cutoff-removal error.  Once supplied, local noncollapse is numerical rather
-- than merely existential.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; -_; _≤_; _<_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

leadingFloor interactionLoss latticeFloor cutoffLoss continuumFloor : ℚ
leadingFloor = + 1 / 16
interactionLoss = + 1 / 32
latticeFloor = + 1 / 32
cutoffLoss = + 1 / 64
continuumFloor = + 1 / 64

leadingMinusInteractionIsLatticeFloor :
  leadingFloor - interactionLoss ≡ latticeFloor
leadingMinusInteractionIsLatticeFloor = ℚRing.solve []

latticeMinusCutoffIsContinuumFloor :
  latticeFloor - cutoffLoss ≡ continuumFloor
latticeMinusCutoffIsContinuumFloor = ℚRing.solve []

continuumFloorPositive : 0ℚ < continuumFloor
continuumFloorPositive = ℚP.positive⁻¹ continuumFloor

record PlaquetteOSNoncollapseEstimate : Set₁ where
  field
    gaussianOSNorm interactionCorrection latticeOSNorm continuumOSNorm : ℚ

    latticeDecomposition :
      latticeOSNorm ≡ gaussianOSNorm + interactionCorrection

    gaussianLower : leadingFloor ≤ gaussianOSNorm

    interactionLower : - interactionLoss ≤ interactionCorrection

    cutoffRemovalLower :
      latticeOSNorm - cutoffLoss ≤ continuumOSNorm

open PlaquetteOSNoncollapseEstimate public

latticeOSNormAtLeastOneThirtySecond :
  (dataSet : PlaquetteOSNoncollapseEstimate) →
  latticeFloor ≤ latticeOSNorm dataSet
latticeOSNormAtLeastOneThirtySecond dataSet =
  subst
    (λ right → latticeFloor ≤ right)
    (sym (latticeDecomposition dataSet))
    (subst
      (λ left → left
        ≤ gaussianOSNorm dataSet + interactionCorrection dataSet)
      leadingMinusInteractionIsLatticeFloor
      (ℚP.+-mono-≤
        (gaussianLower dataSet)
        (interactionLower dataSet)))

continuumOSNormAtLeastOneSixtyFourth :
  (dataSet : PlaquetteOSNoncollapseEstimate) →
  continuumFloor ≤ continuumOSNorm dataSet
continuumOSNormAtLeastOneSixtyFourth dataSet =
  ℚP.≤-trans
    (subst
      (λ left → left ≤ latticeOSNorm dataSet - cutoffLoss)
      latticeMinusCutoffIsContinuumFloor
      (ℚP.+-monoʳ-≤ (- cutoffLoss)
        (latticeOSNormAtLeastOneThirtySecond dataSet)))
    (cutoffRemovalLower dataSet)

continuumOSNormStrictlyPositive :
  (dataSet : PlaquetteOSNoncollapseEstimate) →
  0ℚ < continuumOSNorm dataSet
continuumOSNormStrictlyPositive dataSet =
  ℚP.<-≤-trans continuumFloorPositive
    (continuumOSNormAtLeastOneSixtyFourth dataSet)

record ReconstructedPlaquetteVector
    (Vector : Set)
    (dataSet : PlaquetteOSNoncollapseEstimate) : Set₁ where
  field
    zeroVector plaquetteVector : Vector
    zeroVectorHasZeroOSNorm :
      plaquetteVector ≡ zeroVector → continuumOSNorm dataSet ≡ 0ℚ

open ReconstructedPlaquetteVector public

data Empty : Set where

positiveRationalNotZero : ∀ value →
  0ℚ < value → value ≡ 0ℚ → Empty
positiveRationalNotZero value positive refl =
  ℚP.<-irrefl ℚP.≃-refl positive

continuumPlaquetteVectorNonzero :
  ∀ {Vector dataSet}
    (reconstruction : ReconstructedPlaquetteVector Vector dataSet) →
  plaquetteVector reconstruction ≡ zeroVector reconstruction → Empty
continuumPlaquetteVectorNonzero {dataSet = dataSet} reconstruction vectorZero =
  positiveRationalNotZero
    (continuumOSNorm dataSet)
    (continuumOSNormStrictlyPositive dataSet)
    (zeroVectorHasZeroOSNorm reconstruction vectorZero)

plaquetteLatticeNoncollapseCalibrationLevel : ProofLevel
plaquetteLatticeNoncollapseCalibrationLevel = machineChecked

plaquetteContinuumNoncollapseCalibrationLevel : ProofLevel
plaquetteContinuumNoncollapseCalibrationLevel = machineChecked

physicalPlaquetteGaussianLowerInputLevel : ProofLevel
physicalPlaquetteGaussianLowerInputLevel = conditional

physicalPlaquetteInteractionErrorInputLevel : ProofLevel
physicalPlaquetteInteractionErrorInputLevel = conditional

physicalPlaquetteCutoffRemovalInputLevel : ProofLevel
physicalPlaquetteCutoffRemovalInputLevel = conditional
