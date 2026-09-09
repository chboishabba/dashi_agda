module DASHI.Physics.Closure.NSTriadKNLiteralFourSignBonyRoutingRound581Exact where

------------------------------------------------------------------------
-- ROUND581 / EXACT FINITE BONY ROUTING FOR THE LITERAL FOUR-SIGN INNER FIBRE
--
-- R580 deliberately left the finite routing equality as a separate receipt.
-- This file pays it constructively without a permutation/cardinality theorem.
--
-- Each physical incidence is sent pointwise to exactly one of four zero-masked
-- Bony channels.  The existing foldPointwiseAdd theorem then commutes the
-- finite fold with the four-way vector sum.  Therefore the literal fold is
-- EXACTLY the recombination of the four class folds.  No estimate is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNComLiteralBonyOutputFibrePartitionRound63Exact as Bony
import DASHI.Physics.Closure.NSTriadKNFourHelicityVectorRecombinationRound576Exact as R576
import DASHI.Physics.Closure.NSTriadKNFourSignBonyClassGramCompilerRound580Exact as R580
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F = R580.F

zero : C3.Complex3 F
zero = C3.complex3Zero F

zeroLeft : (v : C3.Complex3 F) → C3.complex3Add zero v ≡ v
zeroLeft v =
  trans
    (Field.complex3AddCommutative zero v)
    (Field.complex3AddZeroRight v)

fourOnlyLH : (v : C3.Complex3 F) →
  R576.fourVectorTotal v zero zero zero ≡ v
fourOnlyLH v =
  trans
    (cong₂ C3.complex3Add
      (Field.complex3AddZeroRight v)
      (Field.complex3AddZeroRight zero))
    (Field.complex3AddZeroRight v)

fourOnlyHL : (v : C3.Complex3 F) →
  R576.fourVectorTotal zero v zero zero ≡ v
fourOnlyHL v =
  trans
    (cong₂ C3.complex3Add
      (zeroLeft v)
      (Field.complex3AddZeroRight zero))
    (Field.complex3AddZeroRight v)

fourOnlyHH : (v : C3.Complex3 F) →
  R576.fourVectorTotal zero zero v zero ≡ v
fourOnlyHH v =
  trans
    (cong₂ C3.complex3Add
      (Field.complex3AddZeroRight zero)
      (Field.complex3AddZeroRight v))
    (zeroLeft v)

fourOnlyCC : (v : C3.Complex3 F) →
  R576.fourVectorTotal zero zero zero v ≡ v
fourOnlyCC v =
  trans
    (cong₂ C3.complex3Add
      (Field.complex3AddZeroRight zero)
      (zeroLeft v))
    (zeroLeft v)

lowHighCell581 :
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
lowHighCell581 value tau with Bony.bonyTag tau
... | Bony.lhTag = value tau
... | Bony.hlTag = zero
... | Bony.hhToLowTag = zero
... | Bony.comparableTag = zero

highLowCell581 :
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
highLowCell581 value tau with Bony.bonyTag tau
... | Bony.lhTag = zero
... | Bony.hlTag = value tau
... | Bony.hhToLowTag = zero
... | Bony.comparableTag = zero

highHighToLowCell581 :
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
highHighToLowCell581 value tau with Bony.bonyTag tau
... | Bony.lhTag = zero
... | Bony.hlTag = zero
... | Bony.hhToLowTag = value tau
... | Bony.comparableTag = zero

comparableCell581 :
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
comparableCell581 value tau with Bony.bonyTag tau
... | Bony.lhTag = zero
... | Bony.hlTag = zero
... | Bony.hhToLowTag = zero
... | Bony.comparableTag = value tau

pointwiseBonyDecomposition581 :
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (tau : Physical.PhysicalTriadIncidence) →
  value tau ≡
    R576.fourVectorTotal
      (lowHighCell581 value tau)
      (highLowCell581 value tau)
      (highHighToLowCell581 value tau)
      (comparableCell581 value tau)
pointwiseBonyDecomposition581 value tau with Bony.bonyTag tau
... | Bony.lhTag = sym (fourOnlyLH (value tau))
... | Bony.hlTag = sym (fourOnlyHL (value tau))
... | Bony.hhToLowTag = sym (fourOnlyHH (value tau))
... | Bony.comparableTag = sym (fourOnlyCC (value tau))

foldPointwiseEqual581 :
  (left right : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  ((tau : Physical.PhysicalTriadIncidence) → left tau ≡ right tau) →
  (items : List Physical.PhysicalTriadIncidence) →
  R224.foldVector left items ≡ R224.foldVector right items
foldPointwiseEqual581 left right pointwise [] = refl
foldPointwiseEqual581 left right pointwise (tau ∷ rest) =
  cong₂ C3.complex3Add
    (pointwise tau)
    (foldPointwiseEqual581 left right pointwise rest)

foldFourPointwise581 :
  (a b c d : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  R224.foldVector
    (λ tau → R576.fourVectorTotal (a tau) (b tau) (c tau) (d tau))
    items
  ≡ R576.fourVectorTotal
      (R224.foldVector a items)
      (R224.foldVector b items)
      (R224.foldVector c items)
      (R224.foldVector d items)
foldFourPointwise581 a b c d items =
  trans
    (R225.foldPointwiseAdd
      (λ tau → C3.complex3Add (a tau) (b tau))
      (λ tau → C3.complex3Add (c tau) (d tau))
      items)
    (cong₂ C3.complex3Add
      (R225.foldPointwiseAdd a b items)
      (R225.foldPointwiseAdd c d items))

literalFoldToFourClassFolds581 :
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  R224.foldVector value items
  ≡ R576.fourVectorTotal
      (R224.foldVector (lowHighCell581 value) items)
      (R224.foldVector (highLowCell581 value) items)
      (R224.foldVector (highHighToLowCell581 value) items)
      (R224.foldVector (comparableCell581 value) items)
literalFoldToFourClassFolds581 value items =
  trans
    (foldPointwiseEqual581 value
      (λ tau → R576.fourVectorTotal
        (lowHighCell581 value tau)
        (highLowCell581 value tau)
        (highHighToLowCell581 value tau)
        (comparableCell581 value tau))
      (pointwiseBonyDecomposition581 value)
      items)
    (foldFourPointwise581
      (lowHighCell581 value)
      (highLowCell581 value)
      (highHighToLowCell581 value)
      (comparableCell581 value)
      items)

sumCellsMapAsFold581 :
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  R180.sumCells (map value items) ≡ R224.foldVector value items
sumCellsMapAsFold581 value [] = refl
sumCellsMapAsFold581 value (tau ∷ rest) =
  cong (C3.complex3Add (value tau)) (sumCellsMapAsFold581 value rest)

bonyClassCells581 :
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence → R580.FourBonyClassCells580
bonyClassCells581 value items =
  R580.four-bony-class-cells-580
    (map (lowHighCell581 value) items)
    (map (highLowCell581 value) items)
    (map (highHighToLowCell581 value) items)
    (map (comparableCell581 value) items)

literalRouting581 :
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  R580.LiteralToBonyRouting580
    (R224.foldVector value items)
    (bonyClassCells581 value items)
literalRouting581 value items =
  R580.literal-to-bony-routing-580 routed
  where
  routed :
    R224.foldVector value items
    ≡ R580.routedFourClassVector580 (bonyClassCells581 value items)
  routed =
    trans
      (literalFoldToFourClassFolds581 value items)
      (congFour
        (sym (sumCellsMapAsFold581 (lowHighCell581 value) items))
        (sym (sumCellsMapAsFold581 (highLowCell581 value) items))
        (sym (sumCellsMapAsFold581 (highHighToLowCell581 value) items))
        (sym (sumCellsMapAsFold581 (comparableCell581 value) items)))
    where
    congFour :
      ∀ {a a' b b' c c' d d' : C3.Complex3 F} →
      a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' →
      R576.fourVectorTotal a b c d ≡ R576.fourVectorTotal a' b' c' d'
    congFour refl refl refl refl = refl

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round581PointwiseBonyRoutingClosed : Bool
round581PointwiseBonyRoutingClosed = true

round581FiniteFoldBonyRoutingClosed : Bool
round581FiniteFoldBonyRoutingClosed = true

round581R580LiteralRoutingReceiptConstructed : Bool
round581R580LiteralRoutingReceiptConstructed = true

round581AnyClassGramResidualPaid : Bool
round581AnyClassGramResidualPaid = false

round581CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round581CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round581ClayPromotion : Bool
round581ClayPromotion = false

round581FiniteFoldBonyRoutingClosedIsTrue :
  round581FiniteFoldBonyRoutingClosed ≡ true
round581FiniteFoldBonyRoutingClosedIsTrue = refl

round581ClayPromotionIsFalse : round581ClayPromotion ≡ false
round581ClayPromotionIsFalse = refl
