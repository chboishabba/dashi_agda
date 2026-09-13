{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFiniteVolumeReopeningPresentationRound283Exact where

------------------------------------------------------------------------
-- ROUND283 / PRESENT THE SAME FINITE T5 MEASURE BY THE RG REOPENING LAW
--
-- R280 reduced the finite covariance weld to three moment identities for
-- F, G and FG.  That is still stronger than the representation work actually
-- needed if all three expectations come from one and the same finite measure.
--
-- The preferred T5 producer already defines its selected diagonal measure
-- literally as the finite-volume family at `diagonalVolume cutoff`.
-- The finite-RG lane computes expectation from an explicit weighted state list.
-- Therefore the least-privilege same-object payment is one presentation theorem:
--
--   E_T5,n[O] = E_RG,n[O]
--
-- for every selected finite observable O on the exact reopening state carrier.
-- F, G and FG then follow by specialization, and R280 compiles covariance.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _*_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5PreferredDiagonalExpectationProducerExact as Preferred
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanFiniteRGExpectationCovarianceSameObjectRound280Exact as R280

record FiniteVolumeReopeningPresentation
    (Measure Fine Coarse : Set)
    (thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ) : Set₁ where
  field
    stepAt : Nat → Reopen.FiniteRGReopeningStep Fine Coarse

    -- Exact representation statement.  This is the only physical/provenance
    -- weld in the compiler: the preferred finite-volume expectation is the
    -- same weighted finite law as the reopening step.
    finiteVolumeExpectationIsReopeningExpectation : ∀ cutoff observable →
      Gram.expectation (T5.operations thermodynamic)
        (Preferred.selectedFiniteVolumeSequence thermodynamic cutoff)
        observable
      ≡ Reopen.fineExpectation (stepAt cutoff) observable

open FiniteVolumeReopeningPresentation public

selectedFiniteExpectation :
  ∀ {Measure Fine Coarse}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ} →
  FiniteVolumeReopeningPresentation Measure Fine Coarse thermodynamic →
  Nat → Reopen.Observable Fine → ℚ
selectedFiniteExpectation {thermodynamic = thermodynamic} presentation cutoff observable =
  Gram.expectation (T5.operations thermodynamic)
    (Preferred.selectedFiniteVolumeSequence thermodynamic cutoff)
    observable

record SelectedFiniteObservablePair
    {Measure Fine Coarse : Set}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ}
    (presentation :
      FiniteVolumeReopeningPresentation Measure Fine Coarse thermodynamic) : Set₁ where
  field
    left right : Nat → Reopen.Observable Fine

open SelectedFiniteObservablePair public

asRound280MomentWeld :
  ∀ {Measure Fine Coarse}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ}
    (presentation :
      FiniteVolumeReopeningPresentation Measure Fine Coarse thermodynamic)
    (pair : SelectedFiniteObservablePair presentation) →
  R280.FiniteRGExpectationMomentWeld Fine Coarse
asRound280MomentWeld {thermodynamic = thermodynamic} presentation pair = record
  { R280.FiniteRGExpectationMomentWeld.stepAt = stepAt presentation
  ; R280.FiniteRGExpectationMomentWeld.left = left pair
  ; R280.FiniteRGExpectationMomentWeld.right = right pair
  ; R280.FiniteRGExpectationMomentWeld.selectedExpectation =
      selectedFiniteExpectation presentation
  ; R280.FiniteRGExpectationMomentWeld.leftExpectationSameObject =
      λ cutoff →
        finiteVolumeExpectationIsReopeningExpectation presentation cutoff
          (left pair cutoff)
  ; R280.FiniteRGExpectationMomentWeld.rightExpectationSameObject =
      λ cutoff →
        finiteVolumeExpectationIsReopeningExpectation presentation cutoff
          (right pair cutoff)
  ; R280.FiniteRGExpectationMomentWeld.productExpectationSameObject =
      λ cutoff →
        finiteVolumeExpectationIsReopeningExpectation presentation cutoff
          (λ fine → left pair cutoff fine * right pair cutoff fine)
  }

finiteVolumePresentationCompilesCovarianceIdentity :
  ∀ {Measure Fine Coarse}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ}
    (presentation :
      FiniteVolumeReopeningPresentation Measure Fine Coarse thermodynamic)
    (pair : SelectedFiniteObservablePair presentation)
    (cutoff : Nat) →
  R280.selectedCovariance (asRound280MomentWeld presentation pair) cutoff
  ≡ R280.finiteRGCovariance (asRound280MomentWeld presentation pair) cutoff
finiteVolumePresentationCompilesCovarianceIdentity presentation pair cutoff =
  R280.selectedCovarianceIsFiniteRG
    (asRound280MomentWeld presentation pair) cutoff

record Round283Boundary : Set where
  constructor round283-boundary
  field
    separateFGProductMomentWeldsPrimitive : Bool
    separateFGProductMomentWeldsPrimitiveIsFalse :
      separateFGProductMomentWeldsPrimitive ≡ false

    oneFiniteMeasurePresentationRequired : Bool
    oneFiniteMeasurePresentationRequiredIsTrue :
      oneFiniteMeasurePresentationRequired ≡ true

    covarianceIdentityCompilerOwned : Bool
    covarianceIdentityCompilerOwnedIsTrue :
      covarianceIdentityCompilerOwned ≡ true

    t5PreferredDiagonalMeasureAlreadyDefinitional : Bool
    t5PreferredDiagonalMeasureAlreadyDefinitionalIsTrue :
      t5PreferredDiagonalMeasureAlreadyDefinitional ≡ true

canonicalRound283Boundary : Round283Boundary
canonicalRound283Boundary =
  round283-boundary false refl true refl true refl true refl

round283PresentationToMomentWeldCompilerLevel : ProofLevel
round283PresentationToMomentWeldCompilerLevel = machineChecked

round283FiniteVolumeReopeningPresentationLevel : ProofLevel
round283FiniteVolumeReopeningPresentationLevel = conditional
