{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRLiteralRecoveryRealizationFrontierExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.DiscreteToSmoothEinsteinLimitReceipt as Smooth
import DASHI.Physics.Closure.SchwarzschildLimitCandidate as Schwarz

data GRLiteralRecoveryRealizationStatus : Set where
  finiteSourcedLawClosedContinuumRealizationOpen :
    GRLiteralRecoveryRealizationStatus

record GRLiteralRecoveryRealizationFrontier : Set where
  constructor grLiteralRecoveryRealizationFrontier
  field
    status : GRLiteralRecoveryRealizationStatus
    finiteSourcedEinsteinLawClosed : Bool
    finiteSourcedEinsteinLawClosedIsTrue :
      finiteSourcedEinsteinLawClosed ≡ true
    discreteToSmoothFirstMissing :
      Smooth.DiscreteToSmoothEinsteinLimitFirstMissing
    discreteToSmoothFirstMissingIsCurvatureConvergence :
      discreteToSmoothFirstMissing
      ≡ Smooth.missingDiscreteToSmoothCurvatureConvergence
    schwarzschildFirstMissing :
      Schwarz.SchwarzschildLimitFirstMissingPrimitive
    schwarzschildFirstMissingIsRadialValuation :
      schwarzschildFirstMissing ≡ Schwarz.missingRadialValuation
    literalGRRecoveredEqualityConstructed : Bool
    literalGRRecoveredEqualityConstructedIsFalse :
      literalGRRecoveredEqualityConstructed ≡ false
    remainingAnalyticLeaves : List String

open GRLiteralRecoveryRealizationFrontier public

canonicalGRLiteralRecoveryRealizationFrontier :
  GRLiteralRecoveryRealizationFrontier
canonicalGRLiteralRecoveryRealizationFrontier =
  grLiteralRecoveryRealizationFrontier
    finiteSourcedLawClosedContinuumRealizationOpen
    true refl
    Smooth.DiscreteToSmoothEinsteinLimitReceipt.firstMissing
      Smooth.canonicalDiscreteToSmoothEinsteinLimitReceipt
    (Smooth.DiscreteToSmoothEinsteinLimitReceipt.firstMissingIsCurvatureConvergence
      Smooth.canonicalDiscreteToSmoothEinsteinLimitReceipt)
    Schwarz.SchwarzschildLimitCandidateDiagnostic.firstMissing
      Schwarz.canonicalSchwarzschildLimitCandidateDiagnostic
    refl
    false refl
    ( "prove discrete curvature convergence on the literal non-flat family"
    ∷ "identify the continuum Ricci/Einstein contractions with that same limit"
    ∷ "prove stress-energy convergence on the same calibrated family"
    ∷ "pay the radial valuation / weak-field Schwarzschild identification"
    ∷ "then instantiate RecoveredGRAttachmentExact rather than postulating target equality"
    ∷ [] )

grRecoveryGapIsAnalyticRealizationNotFiniteEquation :
  finiteSourcedEinsteinLawClosed canonicalGRLiteralRecoveryRealizationFrontier ≡ true
grRecoveryGapIsAnalyticRealizationNotFiniteEquation = refl
