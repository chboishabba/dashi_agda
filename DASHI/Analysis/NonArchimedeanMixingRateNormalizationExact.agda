module DASHI.Analysis.NonArchimedeanMixingRateNormalizationExact where

------------------------------------------------------------------------
-- MIXING RATE NORMALIZATION
--
-- The dedicated mixing document states the intended decay factor as
--
--   (sqrt 2 / 2)^t = 2^(-t/2),
--
-- while one broader prose summary writes O((sqrt 2)^t), which would grow.
-- This module records the source-normalization correction separately from the
-- proof-strength question.  The corresponding Lean L2 bound remains stored in
-- L2MixingAssumptions rather than derived unconditionally.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record MixingRateAudit : Set where
  constructor mixingRateAudit
  field
    dedicatedDocumentUsesInverseSqrtTwoDecay : Bool
    dedicatedDocumentUsesTwoPowMinusHalfT : Bool
    proseSqrtTwoPowTWouldBeDecay : Bool
    intendedLyapunovExponentPositiveHalfLogTwo : Bool
    leanOneStepRateIsAssumptionBacked : Bool
    normalizationCorrectionPromotesLeanProof : Bool

canonicalMixingRateAudit : MixingRateAudit
canonicalMixingRateAudit =
  mixingRateAudit true true false true true false

growingSqrtTwoPowerIsNotDecay :
  MixingRateAudit.proseSqrtTwoPowTWouldBeDecay canonicalMixingRateAudit ≡ false
growingSqrtTwoPowerIsNotDecay = refl

normalizationFixDoesNotUpgradeProof :
  MixingRateAudit.normalizationCorrectionPromotesLeanProof canonicalMixingRateAudit ≡ false
normalizationFixDoesNotUpgradeProof = refl
