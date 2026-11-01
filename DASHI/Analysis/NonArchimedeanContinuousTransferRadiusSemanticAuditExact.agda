module DASHI.Analysis.NonArchimedeanContinuousTransferRadiusSemanticAuditExact where

------------------------------------------------------------------------
-- CONTINUOUS TRANSFER RADIUS / RATE SEMANTIC AUDIT
--
-- The source currently contains four distinct numerical objects that must not
-- be collapsed:
--
--   r_n = 2^(1/2^(n-1))      twisted-circle radius sequence;
--   2                        eigenvalue of the unnormalised transfer operator
--                            on constants;
--   1                        eigenvalue of the normalised Markov operator on
--                            constants;
--   1/sqrt 2                 mean-zero L2 contraction constant stored inside
--                            L2MixingAssumptions.
--
-- Only the first object has base value sqrt 2.  The L2 contraction theorem is
-- conditional and does not identify the full operator spectral radius.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)


data TransferQuantity : Set where
  twistedCircleRadiusSequence : TransferQuantity
  unnormalisedConstantEigenvalue : TransferQuantity
  normalisedConstantEigenvalue : TransferQuantity
  conditionalMeanZeroL2Contraction : TransferQuantity
  fullContinuousOperatorSpectralRadius : TransferQuantity

record TransferQuantityStatus : Set where
  constructor transferQuantityStatus
  field
    quantity : TransferQuantity
    sourceDefined : Bool
    sourceTheoremOwned : Bool
    conditionalOnAssumptionStructure : Bool
    numericallySqrtTwoAtBase : Bool

circleStatus : TransferQuantityStatus
circleStatus =
  transferQuantityStatus twistedCircleRadiusSequence true true false true

unnormalisedConstantStatus : TransferQuantityStatus
unnormalisedConstantStatus =
  transferQuantityStatus unnormalisedConstantEigenvalue true true false false

normalisedConstantStatus : TransferQuantityStatus
normalisedConstantStatus =
  transferQuantityStatus normalisedConstantEigenvalue true true false false

meanZeroL2Status : TransferQuantityStatus
meanZeroL2Status =
  transferQuantityStatus conditionalMeanZeroL2Contraction true true true false

fullOperatorRadiusStatus : TransferQuantityStatus
fullOperatorRadiusStatus =
  transferQuantityStatus fullContinuousOperatorSpectralRadius false false false false

record TransferSemanticFirewall : Set where
  constructor transferSemanticFirewall
  field
    twistedCircleRadiusIsFullOperatorRadius : Bool
    conditionalL2BoundIsUnconditionalSpectralRadius : Bool
    normalizedConstantEigenvalueIsTwistedRadius : Bool
    unnormalizedConstantEigenvalueMayBeDroppedFromFullSpectrum : Bool
    monographRhoNeedsExplicitSectorDefinition : Bool

canonicalTransferSemanticFirewall : TransferSemanticFirewall
canonicalTransferSemanticFirewall =
  transferSemanticFirewall false false false false true

twistedCircleCannotAutoPromoteToFullRadius :
  TransferSemanticFirewall.twistedCircleRadiusIsFullOperatorRadius
    canonicalTransferSemanticFirewall
  ≡ false
twistedCircleCannotAutoPromoteToFullRadius = refl

conditionalMixingCannotAutoPromote :
  TransferSemanticFirewall.conditionalL2BoundIsUnconditionalSpectralRadius
    canonicalTransferSemanticFirewall
  ≡ false
conditionalMixingCannotAutoPromote = refl

rhoNotationNeedsSectorReceipt :
  TransferSemanticFirewall.monographRhoNeedsExplicitSectorDefinition
    canonicalTransferSemanticFirewall
  ≡ true
rhoNotationNeedsSectorReceipt = refl
