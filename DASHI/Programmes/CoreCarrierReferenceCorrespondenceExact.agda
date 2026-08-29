module DASHI.Programmes.CoreCarrierReferenceCorrespondenceExact where

open import DASHI.Core.Prelude
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic

------------------------------------------------------------------------
-- Literal first same-object bridge for dashiCORE.
--
-- Python `Carrier.from_signed` represents balanced ternary values by support
-- plus sign:
--   -1 -> active negative
--    0 -> inactive
--   +1 -> active positive
-- and `to_signed` reverses that representation.  The existing Agda owner
-- `TriadicKernelLiftQuotientExact` already has exactly this finite carrier as
-- `KernelTrit <-> FoldedTrit`, with both round trips proved.
--
-- Keep the Python-facing representation named separately so equality is earned
-- by explicit encode/decode maps rather than by pretending two source files are
-- definitionally the same object.
------------------------------------------------------------------------

data ReferenceSupportSign : Set where
  referenceInactive : ReferenceSupportSign
  referenceNegative : ReferenceSupportSign
  referencePositive : ReferenceSupportSign

referenceFromTrit : Triadic.KernelTrit → ReferenceSupportSign
referenceFromTrit Triadic.negativeTrit = referenceNegative
referenceFromTrit Triadic.zeroTrit = referenceInactive
referenceFromTrit Triadic.positiveTrit = referencePositive

referenceToTrit : ReferenceSupportSign → Triadic.KernelTrit
referenceToTrit referenceInactive = Triadic.zeroTrit
referenceToTrit referenceNegative = Triadic.negativeTrit
referenceToTrit referencePositive = Triadic.positiveTrit

referenceRoundTripSigned :
  (t : Triadic.KernelTrit) →
  referenceToTrit (referenceFromTrit t) ≡ t
referenceRoundTripSigned Triadic.negativeTrit = refl
referenceRoundTripSigned Triadic.zeroTrit = refl
referenceRoundTripSigned Triadic.positiveTrit = refl

referenceRoundTripSupportSign :
  (r : ReferenceSupportSign) →
  referenceFromTrit (referenceToTrit r) ≡ r
referenceRoundTripSupportSign referenceInactive = refl
referenceRoundTripSupportSign referenceNegative = refl
referenceRoundTripSupportSign referencePositive = refl

referenceToFormalFold :
  ReferenceSupportSign → Triadic.FoldedTrit
referenceToFormalFold referenceInactive = Triadic.inactiveTrit
referenceToFormalFold referenceNegative =
  Triadic.activeTrit Triadic.negativeOrientation
referenceToFormalFold referencePositive =
  Triadic.activeTrit Triadic.positiveOrientation

formalFoldToReference :
  Triadic.FoldedTrit → ReferenceSupportSign
formalFoldToReference Triadic.inactiveTrit = referenceInactive
formalFoldToReference
  (Triadic.activeTrit Triadic.negativeOrientation) = referenceNegative
formalFoldToReference
  (Triadic.activeTrit Triadic.positiveOrientation) = referencePositive

referenceFoldCommutes :
  (t : Triadic.KernelTrit) →
  referenceToFormalFold (referenceFromTrit t)
  ≡ Triadic.foldTrit t
referenceFoldCommutes Triadic.negativeTrit = refl
referenceFoldCommutes Triadic.zeroTrit = refl
referenceFoldCommutes Triadic.positiveTrit = refl

referenceUnfoldCommutes :
  (r : ReferenceSupportSign) →
  Triadic.unfoldTrit (referenceToFormalFold r)
  ≡ referenceToTrit r
referenceUnfoldCommutes referenceInactive = refl
referenceUnfoldCommutes referenceNegative = refl
referenceUnfoldCommutes referencePositive = refl

record CoreCarrierReferenceBoundary : Set where
  constructor coreCarrierReferenceBoundary
  field
    supportSignCarrierHasLiteralFormalCorrespondence : Bool
    supportSignCarrierHasLiteralFormalCorrespondenceIsTrue :
      supportSignCarrierHasLiteralFormalCorrespondence ≡ true

    fingerprintNeededForThisFiniteSemanticSquare : Bool
    fingerprintNeededForThisFiniteSemanticSquareIsFalse :
      fingerprintNeededForThisFiniteSemanticSquare ≡ false

    thisOneCarrierSquareProvesEveryCOREOperationCorrect : Bool
    thisOneCarrierSquareProvesEveryCOREOperationCorrectIsFalse :
      thisOneCarrierSquareProvesEveryCOREOperationCorrect ≡ false

canonicalCoreCarrierReferenceBoundary : CoreCarrierReferenceBoundary
canonicalCoreCarrierReferenceBoundary =
  coreCarrierReferenceBoundary
    true refl
    false refl
    false refl
