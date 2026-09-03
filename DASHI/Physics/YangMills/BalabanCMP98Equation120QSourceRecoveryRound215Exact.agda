{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation120QSourceRecoveryRound215Exact where

------------------------------------------------------------------------
-- ROUND215 BIDI: RECOVER Q(V0) DIRECTLY FROM THE LINEAR CONTENT OF CMP98 (120).
--
-- Source audit correction:
-- Eq. (119) supplies the intermediate primed operator.  Eq. (120), followed by
-- the definition (121), already determines the first-order linear form Q(V0)A
-- before the five-term rearrangement (124):
--
--   Q(V0)A = L^-1 [ - Avg_-(R0 A)(F_{c-,x})
--                    + Q'(V0)A
--                    + Avg_+(R0,c R0,c+ A)(F_{c+,x'}) ].
--
-- R147 already owns the exact finite block, path words, R0 recursion,
-- L^-d = 1/28561 weight (for L=13,d=4), and the constructed Eq. (119) term.
-- This module therefore removes the remaining arbitrary qSource authority by
-- defining it from those already-owned objects on the SAME carrier.
--
-- No claim is needed that the current `BalabanSU2LinearizedAverage` executable
-- already contains all four printed correction families of (124).  That later
-- five-term rearrangement becomes a diagnostic/equivalence problem, not the
-- authority for qSource.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (map)
open import Data.Rational.Base as ℚ using (ℚ; _/_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralPathRound147Exact as R147
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Blocks
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word

sourceInverseLℚ : ℚ
sourceInverseLℚ = + 1 / 13

-- Transport a Lie vector based at the end of a signed bond word back to the
-- word's source, using exactly the same `adjointLink` convention as R147's R0
-- recursion.  This is the operator part of R_{0,c} applied to a path integral
-- already based at a later point.
transportAlongWord :
  ∀ {C n Value group} →
  R147.LiteralEquation119PathData C n Value group →
  Nat → Blocks.PeriodicBlock n → List Word.SignedAxis4 →
  R126.Vector (R146.additive C) →
  R126.Vector (R146.additive C)
transportAlongWord dataSet step site [] value = value
transportAlongWord dataSet step site (direction ∷ directions) value =
  R147.adjointLink dataSet step
    (Bond.orientedLink (R147.realization dataSet step) site direction)
    (transportAlongWord dataSet step
      (Bond.walkStep site direction) directions value)

minusCentre :
  ∀ {C n Value group} →
  R147.LiteralEquation119PathData C n Value group →
  Nat → Blocks.PeriodicBlock n
minusCentre dataSet step =
  Embed.embeddingCentre (R147.minusEmbedding dataSet step)

plusCentre :
  ∀ {C n Value group} →
  R147.LiteralEquation119PathData C n Value group →
  Nat → Blocks.PeriodicBlock n
plusCentre dataSet step =
  Embed.embeddingCentre (R147.plusEmbedding dataSet step)

minusFaceValue :
  ∀ {C n Value group} →
  R147.LiteralEquation119PathData C n Value group →
  Nat → R126.Vector (R146.additive C) →
  Centered.CenteredBlockPoint4 6 →
  R126.Vector (R146.additive C)
minusFaceValue dataSet step A point =
  R147.r0Path dataSet step A (minusCentre dataSet step)
    (Embed.canonicalCenteredContourWord point)

-- Literal (R_{0,c-} A)([x,x']).  Compute the coarse crossing segment at x and
-- transport its result back along F_{c-,x} to c-.
minusBondValue :
  ∀ {C n Value group} →
  R147.LiteralEquation119PathData C n Value group →
  Nat → R126.Vector (R146.additive C) →
  Centered.CenteredBlockPoint4 6 →
  R126.Vector (R146.additive C)
minusBondValue dataSet step A point =
  transportAlongWord dataSet step (minusCentre dataSet step)
    (Embed.canonicalCenteredContourWord point)
    (R147.r0Path dataSet step A
      (Embed.embed (R147.minusEmbedding dataSet step) point)
      (R147.coarseWord dataSet step))

-- Literal R_{0,c}(R_{0,c+} A)(F_{c+,x'}).  The plus-block path integral is
-- computed at c+ and then transported through the coarse bond c back to c-.
plusFaceValue :
  ∀ {C n Value group} →
  R147.LiteralEquation119PathData C n Value group →
  Nat → R126.Vector (R146.additive C) →
  Centered.CenteredBlockPoint4 6 →
  R126.Vector (R146.additive C)
plusFaceValue dataSet step A point =
  transportAlongWord dataSet step (minusCentre dataSet step)
    (R147.coarseWord dataSet step)
    (R147.r0Path dataSet step A (plusCentre dataSet step)
      (Embed.canonicalCenteredContourWord
        (R147.plusOffset dataSet step point)))

coarseBondValue :
  ∀ {C n Value group} →
  R147.LiteralEquation119PathData C n Value group →
  Nat → R126.Vector (R146.additive C) →
  R126.Vector (R146.additive C)
coarseBondValue dataSet step A =
  R147.r0Path dataSet step A (minusCentre dataSet step)
    (R147.centreWord dataSet step)

weightedPointSum :
  ∀ {C n Value group} →
  R147.LiteralEquation119PathData C n Value group →
  (Centered.CenteredBlockPoint4 6 → R126.Vector (R146.additive C)) →
  R126.Vector (R146.additive C)
weightedPointSum {C} dataSet term =
  R146.sumV
    (map
      (λ point → R147.scaleV dataSet R147.siteWeightℚ (term point))
      (Carrier.elements (Centered.centeredBlockFinite 6)))

minusFaceAverage :
  ∀ {C n Value group} →
  R147.LiteralEquation119PathData C n Value group →
  Nat → R126.Vector (R146.additive C) →
  R126.Vector (R146.additive C)
minusFaceAverage dataSet step A =
  weightedPointSum dataSet (minusFaceValue dataSet step A)

plusFaceAverage :
  ∀ {C n Value group} →
  R147.LiteralEquation119PathData C n Value group →
  Nat → R126.Vector (R146.additive C) →
  R126.Vector (R146.additive C)
plusFaceAverage dataSet step A =
  weightedPointSum dataSet (plusFaceValue dataSet step A)

-- First-order coefficient read directly from (120)+(121).  R147's averages
-- carry L^-d; the final scaleV by 1/13 supplies the outer L^-1.
equation120LinearQSource :
  ∀ {C n Value group} →
  R147.LiteralEquation119PathData C n Value group →
  Nat → R126.Operator (R146.additive C)
equation120LinearQSource {C} dataSet step A =
  R147.scaleV dataSet sourceInverseLℚ
    (R126.addV (R146.additive C)
      (R146.negV C (minusFaceAverage dataSet step A))
      (R126.addV (R146.additive C)
        (R147.literalEquation119QPrime dataSet step A)
        (plusFaceAverage dataSet step A)))

-- Replace only qSource; every background, path, projection, scalar, and dexp
-- field is definitionally the same object as in the input R147 source.
recoverEquation120QSource :
  ∀ {C n Value group} →
  R147.LiteralEquation119PathData C n Value group →
  R147.LiteralEquation119PathData C n Value group
recoverEquation120QSource dataSet = record
  { R147.LiteralEquation119PathData.realization = R147.realization dataSet
  ; R147.LiteralEquation119PathData.bondComponent = R147.bondComponent dataSet
  ; R147.LiteralEquation119PathData.adjointLink = R147.adjointLink dataSet
  ; R147.LiteralEquation119PathData.scaleV = R147.scaleV dataSet
  ; R147.LiteralEquation119PathData.qSource = equation120LinearQSource dataSet
  ; R147.LiteralEquation119PathData.minusEmbedding = R147.minusEmbedding dataSet
  ; R147.LiteralEquation119PathData.plusEmbedding = R147.plusEmbedding dataSet
  ; R147.LiteralEquation119PathData.coarseSegment = R147.coarseSegment dataSet
  ; R147.LiteralEquation119PathData.coarseSegmentEndsAtPlusCentre =
      R147.coarseSegmentEndsAtPlusCentre dataSet
  ; R147.LiteralEquation119PathData.translationCommutation =
      R147.translationCommutation dataSet
  ; R147.LiteralEquation119PathData.dexpMinusOuter = R147.dexpMinusOuter dataSet
  ; R147.LiteralEquation119PathData.inverseDexpMinusAt =
      R147.inverseDexpMinusAt dataSet
  ; R147.LiteralEquation119PathData.adjointExpAt = R147.adjointExpAt dataSet
  ; R147.LiteralEquation119PathData.adjointExpOuter =
      R147.adjointExpOuter dataSet
  }

recoveredQSourceIsEquation120 :
  ∀ {C n Value group}
    (dataSet : R147.LiteralEquation119PathData C n Value group)
    step A →
  R147.qSource (recoverEquation120QSource dataSet) step A
  ≡ equation120LinearQSource dataSet step A
recoveredQSourceIsEquation120 dataSet step A = refl

-- Eq. (119) itself does not depend on the qSource field, so replacing qSource
-- leaves the constructed primed operator unchanged pointwise.
recoveredQPrimeIsOriginalQPrime :
  ∀ {C n Value group}
    (dataSet : R147.LiteralEquation119PathData C n Value group)
    step A →
  R147.literalEquation119QPrime (recoverEquation120QSource dataSet) step A
  ≡ R147.literalEquation119QPrime dataSet step A
recoveredQPrimeIsOriginalQPrime dataSet step A = refl

recoveredOneStepAveragingData :
  ∀ {C n Value group} →
  R147.LiteralEquation119PathData C n Value group →
  R126.OneStepAveragingDerivative (R146.additive C)
recoveredOneStepAveragingData dataSet =
  R147.asLiteralOneStepAveragingDerivative
    (recoverEquation120QSource dataSet)

recoveredOneStepQIsEquation120 :
  ∀ {C n Value group}
    (dataSet : R147.LiteralEquation119PathData C n Value group)
    step A →
  R126.q (recoveredOneStepAveragingData dataSet) step A
  ≡ equation120LinearQSource dataSet step A
recoveredOneStepQIsEquation120 dataSet step A = refl

recoveredOneStepQPrimeIsEquation119 :
  ∀ {C n Value group}
    (dataSet : R147.LiteralEquation119PathData C n Value group)
    step A →
  R126.qPrime (recoveredOneStepAveragingData dataSet) step A
  ≡ R147.literalEquation119QPrime dataSet step A
recoveredOneStepQPrimeIsEquation119 dataSet step A = refl

cmp98Equation120QSourceRecoveryRound215Level : ProofLevel
cmp98Equation120QSourceRecoveryRound215Level = machineChecked

cmp98Equation120SamePathCarrierRound215Level : ProofLevel
cmp98Equation120SamePathCarrierRound215Level = machineChecked

cmp98Equation119PreservedUnderQSourceRecoveryRound215Level : ProofLevel
cmp98Equation119PreservedUnderQSourceRecoveryRound215Level = machineChecked

-- Remaining source-identification leaf: the printed R0 path language in (120)
-- must be identified with R147's already-selected Path13 bond projection and
-- adjoint transport.  The geometry and operator construction are no longer
-- independent qSource inputs after this module.
literalCMP98Equation120SelectedPathSemanticsRound215Level : ProofLevel
literalCMP98Equation120SelectedPathSemanticsRound215Level = conditional
