module DASHI.Learning.GrokkingCircuitTemporalAlignmentRegression where

open import DASHI.Core.Prelude
import DASHI.Learning.GrokkingCircuitTemporalAlignmentExact as Align

betaBeforeTest95IsClassified :
  Align.temporalClassification Align.syntheticBeforeReceipt ≡ Align.betaBeforeTest95
betaBeforeTest95IsClassified = refl

betaCoincidentWithinCadenceIsClassified :
  Align.temporalClassification Align.syntheticCoincidentReceipt ≡ Align.betaCoincidentWithTest95
betaCoincidentWithinCadenceIsClassified = refl

betaAfterTest95IsClassified :
  Align.temporalClassification Align.syntheticAfterReceipt ≡ Align.betaAfterTest95
betaAfterTest95IsClassified = refl

unobservedBetaTransitionStaysUnobserved :
  Align.temporalClassification Align.syntheticUnobservedReceipt ≡ Align.betaTransitionUnobserved
unobservedBetaTransitionStaysUnobserved = refl

rightCensoredTest95StaysRightCensored :
  Align.temporalClassification Align.syntheticRightCensoredReceipt ≡ Align.firstPassageRightCensored
rightCensoredTest95StaysRightCensored = refl

mismatchedRunIdentityFailsClosed :
  Align.alignmentPromotionPaid Align.syntheticMismatchedRunReceipt ≡ false
mismatchedRunIdentityFailsClosed = refl

ruleDriftFailsClosed :
  Align.alignmentPromotionPaid Align.syntheticRuleDriftReceipt ≡ false
ruleDriftFailsClosed = refl

unpaidBetaFailsClosed :
  Align.alignmentPromotionPaid Align.syntheticUnpaidBetaReceipt ≡ false
unpaidBetaFailsClosed = refl

heldOutOutcomeDoesNotSelectCircuitRule :
  Align.heldOutOutcomeUsedForSelection Align.syntheticBeforeReceipt ≡ false
heldOutOutcomeDoesNotSelectCircuitRule = refl

admissibleAlignmentDoesNotPayMechanism :
  Align.alignmentPaysGrokkingMechanismWitness ≡ false
admissibleAlignmentDoesNotPayMechanism = refl
