module DASHI.Analysis.NonArchimedeanTransferRadiusAnchorNoGoExact where

------------------------------------------------------------------------
-- FULL TRANSFER RADIUS / TWISTED CIRCLE RADIUS NO-GO
--
-- `ContinuousTransfer.lean` defines
--
--   spectralRadius n = 2^(1 / 2^(n-1))
--
-- as the concentric twisted-circle radius sequence and proves
-- `spectralRadius_two = sqrt 2`.  The same file independently proves
--
--   transferOp 1 = 2 * 1
--   markovTransferOp 1 = 1.
--
-- Hence the quantity named `spectralRadius` in that file is not by itself a
-- theorem identifying the functional-analytic spectral radius of transferOp.
-- In particular, the unnormalised transfer operator has eigenvalue 2, so its
-- genuine spectral radius cannot be sqrt 2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record TransferRadiusSourceAudit : Set where
  constructor transferRadiusSourceAudit
  field
    circleRadiusSequenceDefined : Bool
    circleRadiusAtTwoIsSqrtTwoOwned : Bool
    circleRadiusBridgedToTwistedSectorMagnitude : Bool
    twistedMagnitudeBridgeConditionalOnFinalMagnitudeHypothesis : Bool

    fullTransferConstantEigenvalueTwoOwned : Bool
    normalizedMarkovConstantEigenvalueOneOwned : Bool

    sourceProvesCircleRadiusIsFullTransferSpectralRadius : Bool
    sourceProvesFullTransferRadiusEqualsSqrtTwo : Bool
    monographUsesRhoL2EqualsSqrtTwo : Bool

canonicalTransferRadiusSourceAudit : TransferRadiusSourceAudit
canonicalTransferRadiusSourceAudit =
  transferRadiusSourceAudit
    true true true true
    true true
    false false true

circleRadiusIsNotFullOperatorRadiusReceipt :
  TransferRadiusSourceAudit.sourceProvesCircleRadiusIsFullTransferSpectralRadius
    canonicalTransferRadiusSourceAudit
  ≡ false
circleRadiusIsNotFullOperatorRadiusReceipt = refl

rhoL2SqrtTwoNotLeanBacked :
  TransferRadiusSourceAudit.sourceProvesFullTransferRadiusEqualsSqrtTwo
    canonicalTransferRadiusSourceAudit
  ≡ false
rhoL2SqrtTwoNotLeanBacked = refl

record RadiusNameFirewall : Set where
  constructor radiusNameFirewall
  field
    sameIdentifierWordSpectralRadiusImpliesSameObject : Bool
    twistedSectorRadiusMayReplaceFullOperatorRadius : Bool
    constantEigenvalueMayBeIgnoredInFullRadius : Bool
    repairedAnchorShouldUsePrimitiveTwistedRadius : Bool

canonicalRadiusNameFirewall : RadiusNameFirewall
canonicalRadiusNameFirewall =
  radiusNameFirewall false false false true

primitiveTwistedRadiusIsCorrectAnchorCandidate :
  RadiusNameFirewall.repairedAnchorShouldUsePrimitiveTwistedRadius
    canonicalRadiusNameFirewall
  ≡ true
primitiveTwistedRadiusIsCorrectAnchorCandidate = refl
