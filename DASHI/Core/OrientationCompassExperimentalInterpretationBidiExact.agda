module DASHI.Core.OrientationCompassExperimentalInterpretationBidiExact where

open import DASHI.Core.Prelude

import DASHI.Biology.SignedMultiplicityObstructionExact as Signed
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Backprop

------------------------------------------------------------------------
-- ORIENTATION COMPASS, NOT VERDICT
--
-- The exact signed-multiplicity donor already owns a three-way orientation and
-- proves that swapping the ordered comparison reverses that orientation.  This
-- module uses that algebra as the bounded determinant-style compass analogy for
-- experiment interpretation.  It does not claim the multiplicity defect is a
-- literal determinant, and sign reversal does not become semantic negation.
------------------------------------------------------------------------

outcomeOfDefectOrientation : Signed.DefectOrientation → Backprop.ExperimentalOutcome
outcomeOfDefectOrientation Signed.negativeDefect = Backprop.adverse
outcomeOfDefectOrientation Signed.balancedDefect = Backprop.indeterminate
outcomeOfDefectOrientation Signed.positiveDefect = Backprop.supportive

backpropOrientationOfDefect : Signed.DefectOrientation → Backprop.OrientationReading
backpropOrientationOfDefect orientation =
  Backprop.orientationOf (outcomeOfDefectOrientation orientation)

negativeDefectReadsAdverse :
  outcomeOfDefectOrientation Signed.negativeDefect ≡ Backprop.adverse
negativeDefectReadsAdverse = refl

balancedDefectReadsIndeterminate :
  outcomeOfDefectOrientation Signed.balancedDefect ≡ Backprop.indeterminate
balancedDefectReadsIndeterminate = refl

positiveDefectReadsSupportive :
  outcomeOfDefectOrientation Signed.positiveDefect ≡ Backprop.supportive
positiveDefectReadsSupportive = refl

balancedDefectReadsDegenerateOrientation :
  backpropOrientationOfDefect Signed.balancedDefect
  ≡ Backprop.degenerateOrientation
balancedDefectReadsDegenerateOrientation = refl

------------------------------------------------------------------------
-- Ordered-comparison reversal is exact at the orientation level.
------------------------------------------------------------------------

comparisonSwapReversesDefectOrientation :
  ∀ {I} (A B : Signed.Multiplicity I) (i : I) →
  Signed.orientationOfInteger (Signed.delta B A i)
  ≡ Signed.reverseOrientation (Signed.orientationOfInteger (Signed.delta A B i))
comparisonSwapReversesDefectOrientation = Signed.orientationSwap

orientationReversalIsInvolutive :
  (orientation : Signed.DefectOrientation) →
  Signed.reverseOrientation (Signed.reverseOrientation orientation) ≡ orientation
orientationReversalIsInvolutive = Signed.reverseOrientationInvolutive

------------------------------------------------------------------------
-- But changing ordered comparison / frame is not the same thing as proving the
-- semantic opposite claim.  A negative reading only orients the comparison;
-- diagnosis and dependency structure determine what should reopen.
------------------------------------------------------------------------

data ReverseOrientationNegatesConclusion : Set where
data BalancedOrientationMeansFalse : Set where
data SignedComparisonIsLiteralDeterminant : Set where
data SwapComparisonIdentifiesGeometricAntipode : Set where

orientationReversalDoesNotNegateConclusion :
  ReverseOrientationNegatesConclusion → ⊥
orientationReversalDoesNotNegateConclusion ()

balancedOrientationDoesNotMeanFalse : BalancedOrientationMeansFalse → ⊥
balancedOrientationDoesNotMeanFalse ()

signedComparisonIsNotPromotedToLiteralDeterminant :
  SignedComparisonIsLiteralDeterminant → ⊥
signedComparisonIsNotPromotedToLiteralDeterminant ()

swapDoesNotIdentifyGeometricAntipode :
  SwapComparisonIdentifiesGeometricAntipode → ⊥
swapDoesNotIdentifyGeometricAntipode ()

record OrientationCompassBoundary : Set where
  constructor orientation-compass-boundary
  field
    signActsAsOrderedComparisonOrientation : Bool
    balancedCaseMapsToIndeterminate : Bool
    swappingComparisonReversesOrientation : Bool
    reversedOrientationNegatesSemanticConclusion : Bool
    signedMultiplicityClaimedAsLiteralDeterminant : Bool
    resultStillNeedsDiagnosisForBackpropagation : Bool

canonicalOrientationCompassBoundary : OrientationCompassBoundary
canonicalOrientationCompassBoundary =
  orientation-compass-boundary true true true false false true
