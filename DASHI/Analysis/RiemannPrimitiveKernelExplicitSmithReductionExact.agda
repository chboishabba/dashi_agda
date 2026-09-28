module DASHI.Analysis.RiemannPrimitiveKernelExplicitSmithReductionExact where

------------------------------------------------------------------------
-- RH PRIMITIVE KERNEL: EXPLICIT 1x4 SMITH REDUCTION
--
-- Start with
--
--   (80,243,1215,972).
--
-- The first determinant-one block change gives
--
--   (1,-3,1215,972).
--
-- Then three elementary column shears clear the remaining coefficients:
--
--   (1,-3,1215,972)
--      -> (1,0,1215,972)
--      -> (1,0,0,972)
--      -> (1,0,0,0).
--
-- Every step has an explicit inverse.  Therefore the bare integer row has
-- Smith invariant factor 1 and no additional unfiltered integer invariant.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Integer using (ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Product using (_,_)

import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR

import DASHI.Analysis.RiemannPrimitiveKernelUnimodularBasisExact as Basis

module RingZ = NR IntRS.ring
open RingZ using (Κ; Ι; _⊕_; _⊗_; ⊝_; solve)

record Row4 : Set where
  constructor row4
  field
    a b c d : ℤ

open Row4 public

originalRow : Row4
originalRow =
  row4 (+ 80) (+ 243) (+ 1215) (+ 972)

firstBlockChange : Row4 -> Row4
firstBlockChange (row4 x y z w) with Basis.forwardU (x , y)
... | u , v = row4 u v z w

firstBlockInverse : Row4 -> Row4
firstBlockInverse (row4 x y z w) with Basis.inverseU (x , y)
... | u , v = row4 u v z w

firstBlockRoundTripLeft :
  (r : Row4) ->
  firstBlockInverse (firstBlockChange r) ≡ r
firstBlockRoundTripLeft (row4 x y z w)
  rewrite Basis.inverseAfterForward (x , y) =
  refl

firstBlockRoundTripRight :
  (r : Row4) ->
  firstBlockChange (firstBlockInverse r) ≡ r
firstBlockRoundTripRight (row4 x y z w)
  rewrite Basis.forwardAfterInverse (x , y) =
  refl

clearB : Row4 -> Row4
clearB (row4 x y z w) =
  row4 x (y + (+ 3) * x) z w

unClearB : Row4 -> Row4
unClearB (row4 x y z w) =
  row4 x (y - (+ 3) * x) z w

clearC : Row4 -> Row4
clearC (row4 x y z w) =
  row4 x y (z - (+ 1215) * x) w

unClearC : Row4 -> Row4
unClearC (row4 x y z w) =
  row4 x y (z + (+ 1215) * x) w

clearD : Row4 -> Row4
clearD (row4 x y z w) =
  row4 x y z (w - (+ 972) * x)

unClearD : Row4 -> Row4
unClearD (row4 x y z w) =
  row4 x y z (w + (+ 972) * x)

clearBRoundTripLeft :
  (r : Row4) ->
  unClearB (clearB r) ≡ r
clearBRoundTripLeft (row4 x y z w) =
  cong
    (λ y' -> row4 x y' z w)
    (RingZ.solve 2
      (λ x y ->
        (((y ⊕ (Κ (+ 3) ⊗ x)) ⊕ (⊝ (Κ (+ 3) ⊗ x))) , y))
      refl x y)

clearBRoundTripRight :
  (r : Row4) ->
  clearB (unClearB r) ≡ r
clearBRoundTripRight (row4 x y z w) =
  cong
    (λ y' -> row4 x y' z w)
    (RingZ.solve 2
      (λ x y ->
        (((y ⊕ (⊝ (Κ (+ 3) ⊗ x))) ⊕ (Κ (+ 3) ⊗ x)) , y))
      refl x y)

clearCRoundTripLeft :
  (r : Row4) ->
  unClearC (clearC r) ≡ r
clearCRoundTripLeft (row4 x y z w) =
  cong
    (λ z' -> row4 x y z' w)
    (RingZ.solve 2
      (λ x z ->
        (((z ⊕ (⊝ (Κ (+ 1215) ⊗ x))) ⊕ (Κ (+ 1215) ⊗ x)) , z))
      refl x z)

clearCRoundTripRight :
  (r : Row4) ->
  clearC (unClearC r) ≡ r
clearCRoundTripRight (row4 x y z w) =
  cong
    (λ z' -> row4 x y z' w)
    (RingZ.solve 2
      (λ x z ->
        (((z ⊕ (Κ (+ 1215) ⊗ x)) ⊕ (⊝ (Κ (+ 1215) ⊗ x))) , z))
      refl x z)

clearDRoundTripLeft :
  (r : Row4) ->
  unClearD (clearD r) ≡ r
clearDRoundTripLeft (row4 x y z w) =
  cong
    (λ w' -> row4 x y z w')
    (RingZ.solve 2
      (λ x w ->
        (((w ⊕ (⊝ (Κ (+ 972) ⊗ x))) ⊕ (Κ (+ 972) ⊗ x)) , w))
      refl x w)

clearDRoundTripRight :
  (r : Row4) ->
  clearD (unClearD r) ≡ r
clearDRoundTripRight (row4 x y z w) =
  cong
    (λ w' -> row4 x y z w')
    (RingZ.solve 2
      (λ x w ->
        (((w ⊕ (Κ (+ 972) ⊗ x)) ⊕ (⊝ (Κ (+ 972) ⊗ x))) , w))
      refl x w)

smithReduce : Row4 -> Row4
smithReduce r =
  clearD (clearC (clearB (firstBlockChange r)))

smithExpand : Row4 -> Row4
smithExpand r =
  firstBlockInverse (unClearB (unClearC (unClearD r)))

smithExpandReduce :
  (r : Row4) ->
  smithExpand (smithReduce r) ≡ r
smithExpandReduce r
  rewrite clearDRoundTripLeft (clearC (clearB (firstBlockChange r)))
        | clearCRoundTripLeft (clearB (firstBlockChange r))
        | clearBRoundTripLeft (firstBlockChange r)
        | firstBlockRoundTripLeft r =
  refl

smithReduceExpand :
  (r : Row4) ->
  smithReduce (smithExpand r) ≡ r
smithReduceExpand r
  rewrite firstBlockRoundTripRight (unClearB (unClearC (unClearD r)))
        | clearBRoundTripRight (unClearC (unClearD r))
        | clearCRoundTripRight (unClearD r)
        | clearDRoundTripRight r =
  refl

stepOneExact :
  firstBlockChange originalRow
  ≡ row4 (+ 1) (- (+ 3)) (+ 1215) (+ 972)
stepOneExact = refl

stepTwoExact :
  clearB (row4 (+ 1) (- (+ 3)) (+ 1215) (+ 972))
  ≡ row4 (+ 1) (+ 0) (+ 1215) (+ 972)
stepTwoExact = refl

stepThreeExact :
  clearC (row4 (+ 1) (+ 0) (+ 1215) (+ 972))
  ≡ row4 (+ 1) (+ 0) (+ 0) (+ 972)
stepThreeExact = refl

stepFourExact :
  clearD (row4 (+ 1) (+ 0) (+ 0) (+ 972))
  ≡ row4 (+ 1) (+ 0) (+ 0) (+ 0)
stepFourExact = refl

explicitSmithNormalForm :
  smithReduce originalRow
  ≡ row4 (+ 1) (+ 0) (+ 0) (+ 0)
explicitSmithNormalForm = refl

rowMap : Row4 -> ℤ
rowMap (row4 x y z w) =
  (+ 80) * x + (+ 243) * y + (+ 1215) * z + (+ 972) * w

rowPreimage : ℤ -> Row4
rowPreimage value =
  row4
    ((- (+ 82)) * value)
    ((+ 27) * value)
    (+ 0)
    (+ 0)

rowMapHasPreimage :
  (value : ℤ) ->
  rowMap (rowPreimage value) ≡ value
rowMapHasPreimage value =
  RingZ.solve 1
    (λ value ->
      ( ((Κ (+ 80) ⊗ ((⊝ (Κ (+ 82))) ⊗ value))
          ⊕ (Κ (+ 243) ⊗ (Κ (+ 27) ⊗ value))
          ⊕ (Κ (+ 1215) ⊗ Κ (+ 0))
          ⊕ (Κ (+ 972) ⊗ Κ (+ 0)))
      , value ))
    refl value

record ExplicitSmithReductionBoundary : Set where
  constructor explicit-smith-reduction-boundary
  field
    determinantOneFirstBlockOwned : Bool
    threeElementaryShearsOwned : Bool
    everyStepHasExplicitInverse : Bool
    fullReductionRoundTripOwned : Bool
    explicitOneZeroZeroZeroNormalFormOwned : Bool
    rowMapSurjectivityWitnessOwned : Bool
    nontrivialBareIntegerInvariantFactorRemains : Bool
    filteredThreeAdicStructureStillAdditional : Bool

canonicalExplicitSmithReductionBoundary :
  ExplicitSmithReductionBoundary
canonicalExplicitSmithReductionBoundary =
  explicit-smith-reduction-boundary
    true true true true true true false true
