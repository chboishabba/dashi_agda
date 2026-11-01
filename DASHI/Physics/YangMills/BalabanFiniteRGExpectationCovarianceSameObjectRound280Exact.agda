{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFiniteRGExpectationCovarianceSameObjectRound280Exact where

------------------------------------------------------------------------
-- ROUND280 / FACTOR THE FIRST R279 SAME-OBJECT WELD
--
-- R279 previously asked directly for
--
--   |Cov_expectation,n(F,G)| = embed |Cov_RG,n(F,G)|.
--
-- That is too coarse for source/provenance auditing.  The older finite-RG
-- owner already DEFINES its covariance by the same three moments
--
--   E[FG] - E[F]E[G].
--
-- Therefore the shortest honest payment is not a fresh covariance theorem.
-- It is three same-cutoff observation identities:
--
--   E_T5,n[F]  = E_RG,n[F],
--   E_T5,n[G]  = E_RG,n[G],
--   E_T5,n[FG] = E_RG,n[FG].
--
-- Once those identities are supplied on the exact selected observable pair,
-- covariance equality is finite rational algebra/compiler output.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _-_; ∣_∣)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanFiniteRGTotalCovarianceExact as RG

------------------------------------------------------------------------
-- Minimal same-cutoff moment carrier.
------------------------------------------------------------------------

record FiniteRGExpectationMomentWeld (Fine Coarse : Set) : Set₁ where
  field
    stepAt : Nat → Reopen.FiniteRGReopeningStep Fine Coarse

    left right : Nat → Reopen.Observable Fine

    -- The external/continuum-lane finite expectation is kept as a rational
    -- scalar here.  A later R279 adapter may embed this rational scalar into a
    -- different spectral Scalar; this owner does not collapse those carriers.
    selectedExpectation : Nat → Reopen.Observable Fine → ℚ

    leftExpectationSameObject : ∀ cutoff →
      selectedExpectation cutoff (left cutoff)
      ≡ Reopen.fineExpectation (stepAt cutoff) (left cutoff)

    rightExpectationSameObject : ∀ cutoff →
      selectedExpectation cutoff (right cutoff)
      ≡ Reopen.fineExpectation (stepAt cutoff) (right cutoff)

    productExpectationSameObject : ∀ cutoff →
      selectedExpectation cutoff
        (λ fine → left cutoff fine * right cutoff fine)
      ≡ Reopen.fineExpectation (stepAt cutoff)
          (λ fine → left cutoff fine * right cutoff fine)

open FiniteRGExpectationMomentWeld public

selectedCovariance :
  ∀ {Fine Coarse} →
  FiniteRGExpectationMomentWeld Fine Coarse → Nat → ℚ
selectedCovariance weld cutoff =
  selectedExpectation weld cutoff
      (λ fine → left weld cutoff fine * right weld cutoff fine)
  - selectedExpectation weld cutoff (left weld cutoff)
      * selectedExpectation weld cutoff (right weld cutoff)

finiteRGCovariance :
  ∀ {Fine Coarse} →
  FiniteRGExpectationMomentWeld Fine Coarse → Nat → ℚ
finiteRGCovariance weld cutoff =
  RG.fineCovariance (stepAt weld cutoff)
    (left weld cutoff) (right weld cutoff)

-- Tiny congruence compiler.  No probability theorem is used here: after the
-- three moments are identified, the two covariance expressions are the same
-- rational expression.
selectedCovarianceIsFiniteRG :
  ∀ {Fine Coarse}
    (weld : FiniteRGExpectationMomentWeld Fine Coarse)
    (cutoff : Nat) →
  selectedCovariance weld cutoff ≡ finiteRGCovariance weld cutoff
selectedCovarianceIsFiniteRG weld cutoff
  rewrite leftExpectationSameObject weld cutoff
        | rightExpectationSameObject weld cutoff
        | productExpectationSameObject weld cutoff = refl

selectedCovarianceMagnitudeIsFiniteRG :
  ∀ {Fine Coarse}
    (weld : FiniteRGExpectationMomentWeld Fine Coarse)
    (cutoff : Nat) →
  ∣ selectedCovariance weld cutoff ∣
  ≡ ∣ finiteRGCovariance weld cutoff ∣
selectedCovarianceMagnitudeIsFiniteRG weld cutoff =
  cong ∣_∣ (selectedCovarianceIsFiniteRG weld cutoff)

------------------------------------------------------------------------
-- Introspective boundary.
------------------------------------------------------------------------

record Round280Boundary : Set where
  constructor round280-boundary
  field
    freshFiniteCovarianceTheoremRequired : Bool
    freshFiniteCovarianceTheoremRequiredIsFalse :
      freshFiniteCovarianceTheoremRequired ≡ false

    sameFiniteMeasureAndObservableMomentIdentitiesRequired : Bool
    sameFiniteMeasureAndObservableMomentIdentitiesRequiredIsTrue :
      sameFiniteMeasureAndObservableMomentIdentitiesRequired ≡ true

    covarianceIdentityCompilerOwned : Bool
    covarianceIdentityCompilerOwnedIsTrue :
      covarianceIdentityCompilerOwned ≡ true

    continuumSpectrumIdentityPaidHere : Bool
    continuumSpectrumIdentityPaidHereIsFalse :
      continuumSpectrumIdentityPaidHere ≡ false

    spectralPositiveGapPaidHere : Bool
    spectralPositiveGapPaidHereIsFalse :
      spectralPositiveGapPaidHere ≡ false

canonicalRound280Boundary : Round280Boundary
canonicalRound280Boundary =
  round280-boundary false refl true refl true refl false refl false refl

round280FiniteMomentToCovarianceCompilerLevel : ProofLevel
round280FiniteMomentToCovarianceCompilerLevel = machineChecked

-- Physical/source payment: identify the exact T5 finite measure/selected tests
-- with the exact finite-RG reopening expectation for F, G and FG at each cutoff.
round280FiniteExpectationMomentSameObjectLevel : ProofLevel
round280FiniteExpectationMomentSameObjectLevel = conditional
