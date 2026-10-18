{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyFiveSourcePhysicsTypedReceiptsTest where

import DASHI.Physics.Foundations.CMP119CosmologyFiveSourcePhysicsTypedReceiptsExact as Subject

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

fiveReceiptsTyped : Subject.typedSourcePhysicsReceiptCount ≡ 5
fiveReceiptsTyped = refl

genericSetSocketsGone : Subject.genericSetValuedReceiptSocketsRemain ≡ false
genericSetSocketsGone = refl

a1IsExactCovarianceLaw : Subject.a1ReceiptIsExactSignedB4Covariance ≡ true
a1IsExactCovarianceLaw = refl

a2MeaningIsExternallyFixed : Subject.a2MeaningRelationIsExternalParameter ≡ true
a2MeaningIsExternallyFixed = refl

b1ReusesCanonicalDirectTail : Subject.b1ReceiptReusesCanonicalDirectTailAnchor ≡ true
b1ReusesCanonicalDirectTail = refl

b2IsStrictSourceEnvelope : Subject.b2ReceiptIsStrictCombinedVacuumTailEnvelope ≡ true
b2IsStrictSourceEnvelope = refl

cIsOneSidedDominance : Subject.cReceiptIsOneSidedAnomalyDominance ≡ true
cIsOneSidedDominance = refl

noFalsePayment : Subject.currentSafeTheoryPaysAllFiveTypedReceipts ≡ false
noFalsePayment = refl
