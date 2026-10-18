module DASHI.Mathematics.Complexity.PNotEqualsNPSemanticQuotientExponentialNoGoExact where

------------------------------------------------------------------------
-- SEMANTIC SHANNON QUOTIENT CAN HAVE 2^n CLASSES
--
-- P9 asks for a cheap quotient Q on restricted SAT self-instances such that
--
--   Q(a) = Q(b)  =>  SAT(phi_a) <-> SAT(phi_b)
--
-- with few quotient classes.
--
-- Before attributing that to Shannon decomposition itself, we need the generic
-- worst case.  Equality on two n-bit blocks already has the maximal residual
-- subfunction count:
--
--   EQ_n(x,y) = [x = y].
--
-- After fixing x=a, the residual function is
--
--   f_a(y) = [a = y].
--
-- For a != b, evaluate at y=a:
--
--   f_a(a)=true
--   f_b(a)=false.
--
-- Hence all 2^n prefixes induce pairwise distinct residual Boolean functions.
--
-- CONSEQUENCE:
--
-- Generic Shannon semantic quotienting can still require 2^n semantic classes.
-- A small quotient for the self-diagonal SAT family must use special structure
-- of that family, not Shannon semantics alone.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _,_)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit
import DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact as Bits

------------------------------------------------------------------------
-- Vector equality Boolean.
------------------------------------------------------------------------

boolEq : Bool → Bool → Bool
boolEq false false = true
boolEq false true = false
boolEq true false = false
boolEq true true = true

vecEq :
  ∀ {width : Nat} →
  Vec Bool width →
  Vec Bool width →
  Bool
vecEq [] [] =
  true
vecEq (left ∷ lefts) (right ∷ rights) =
  Cook.andBool
    (boolEq left right)
    (vecEq lefts rights)

vecEqRefl :
  ∀ {width : Nat}
    (bits : Vec Bool width) →
  vecEq bits bits ≡ true
vecEqRefl [] =
  refl
vecEqRefl (bit ∷ bits)
    rewrite vecEqRefl bits
    with bit
... | false = refl
... | true = refl

------------------------------------------------------------------------
-- Distinct vectors disagree at some coordinate.
------------------------------------------------------------------------

VectorDifference :
  ∀ {width : Nat} →
  Vec Bool width →
  Vec Bool width →
  Set
VectorDifference {width} left right =
  Σ (Fin width) λ index →
    Circuit.lookupVec index left
    ≡ Cook.notBool (Circuit.lookupVec index right)

differenceForUnequalBoolHead :
  ∀ {width : Nat}
    {leftBit rightBit : Bool}
    {lefts rights : Vec Bool width} →
  leftBit ≡ Cook.notBool rightBit →
  VectorDifference
    (leftBit ∷ lefts)
    (rightBit ∷ rights)
differenceForUnequalBoolHead opposite =
  fzero , opposite

liftTailDifference :
  ∀ {width : Nat}
    {leftBit rightBit : Bool}
    {lefts rights : Vec Bool width} →
  VectorDifference lefts rights →
  VectorDifference
    (leftBit ∷ lefts)
    (rightBit ∷ rights)
liftTailDifference (index , differs) =
  fsuc index , differs

vecEqFalseFromDifference :
  ∀ {width : Nat}
    (left right : Vec Bool width) →
  VectorDifference left right →
  vecEq left right ≡ false
vecEqFalseFromDifference
    (leftBit ∷ lefts)
    (rightBit ∷ rights)
    (fzero , opposite)
    with leftBit | rightBit
... | false | false = ()
... | false | true = refl
... | true | false = refl
... | true | true = ()
vecEqFalseFromDifference
    (leftBit ∷ lefts)
    (rightBit ∷ rights)
    (fsuc index , differs)
    rewrite
      vecEqFalseFromDifference
        lefts
        rights
        (index , differs)
    with leftBit | rightBit
... | false | false = refl
... | false | true = refl
... | true | false = refl
... | true | true = refl

------------------------------------------------------------------------
-- Residual subfunction after fixing the first block.
------------------------------------------------------------------------

equalityResidual :
  ∀ {width : Nat} →
  Vec Bool width →
  Vec Bool width →
  Bool
equalityResidual fixed remaining =
  vecEq fixed remaining

record ResidualFunctionsDiffer
    {width : Nat}
    (leftPrefix rightPrefix : Vec Bool width) : Set where
  constructor residual-functions-differ
  field
    witnessInput :
      Vec Bool width

    leftValue :
      equalityResidual leftPrefix witnessInput
      ≡ true

    rightValue :
      equalityResidual rightPrefix witnessInput
      ≡ false

open ResidualFunctionsDiffer public

differentPrefixesGiveDifferentResidualFunctions :
  ∀ {width : Nat}
    (leftPrefix rightPrefix : Vec Bool width) →
  VectorDifference leftPrefix rightPrefix →
  ResidualFunctionsDiffer
    leftPrefix
    rightPrefix
differentPrefixesGiveDifferentResidualFunctions
    leftPrefix rightPrefix difference =
  residual-functions-differ
    leftPrefix
    (vecEqRefl leftPrefix)
    (vecEqFalseFromDifference
      rightPrefix
      leftPrefix
      symmetricDifference)
  where
    symmetricDifference :
      VectorDifference rightPrefix leftPrefix
    symmetricDifference
      with difference
    ... | index , differs
      with Circuit.lookupVec index leftPrefix
         | Circuit.lookupVec index rightPrefix
         | differs
    ... | false | true | refl =
      index , refl
    ... | true | false | refl =
      index , refl

------------------------------------------------------------------------
-- Canonical finite indexing gives exactly 2^n distinct semantic residuals.
--
-- We reuse the explicit Bool^n <-> Fin(2^n) codec already proved in the exact
-- residual-summary owner.
------------------------------------------------------------------------

prefixAtIndex :
  ∀ {width : Nat} →
  Fin (Bits.bitCardinality width) →
  Vec Bool width
prefixAtIndex =
  Bits.finToBits

prefixAtIndexInjective :
  ∀ {width : Nat}
    {left right : Fin (Bits.bitCardinality width)} →
  prefixAtIndex left ≡ prefixAtIndex right →
  left ≡ right
prefixAtIndexInjective =
  Bits.finToBitsInjective

------------------------------------------------------------------------
-- Semantic-class injection:
--
-- an index determines a residual function uniquely, because equality of the
-- residual functions would imply equality of their unique accepting point.
------------------------------------------------------------------------

ResidualFunction :
  Nat →
  Set
ResidualFunction width =
  Vec Bool width → Bool

indexedResidualFunction :
  ∀ {width : Nat} →
  Fin (Bits.bitCardinality width) →
  ResidualFunction width
indexedResidualFunction index =
  equalityResidual
    (prefixAtIndex index)

indexedResidualFunctionInjective :
  ∀ {width : Nat}
    {left right : Fin (Bits.bitCardinality width)} →
  ((input : Vec Bool width) →
    indexedResidualFunction left input
    ≡ indexedResidualFunction right input) →
  left ≡ right
indexedResidualFunctionInjective
    {width = width}
    {left = left} {right = right}
    sameFunction =
  prefixAtIndexInjective
    prefixEqual
  where
    leftPrefix :
      Vec Bool width
    leftPrefix =
      prefixAtIndex left

    rightPrefix :
      Vec Bool width
    rightPrefix =
      prefixAtIndex right

    leftAccepted :
      indexedResidualFunction left leftPrefix
      ≡ true
    leftAccepted =
      vecEqRefl leftPrefix

    rightAccepted :
      indexedResidualFunction right leftPrefix
      ≡ true
    rightAccepted =
      trans
        (sym
          (sameFunction leftPrefix))
        leftAccepted

    prefixEqual :
      leftPrefix ≡ rightPrefix
    prefixEqual =
      sym
        (vecEqTrueImpliesEqual
          rightPrefix
          leftPrefix
          rightAccepted)

    vecEqTrueImpliesEqual :
      ∀ {n : Nat}
        (a b : Vec Bool n) →
      vecEq a b ≡ true →
      a ≡ b
    vecEqTrueImpliesEqual [] [] equal =
      refl
    vecEqTrueImpliesEqual
        (a ∷ as) (b ∷ bs) equal
        with a | b
    ... | false | false
        with vecEqTrueImpliesEqual as bs equal
    ...   | refl = refl
    ... | false | true = ()
    ... | true | false = ()
    ... | true | true
        with vecEqTrueImpliesEqual as bs equal
    ...   | refl = refl

------------------------------------------------------------------------
-- Research consequence.
--
-- There are exactly 2^n distinct residual subfunctions in this tiny semantic
-- family.  Therefore:
--
--   "merge Shannon nodes whenever the restricted problems compute the same
--    Boolean function"
--
-- still has exponential worst-case width.
--
-- P9 can only succeed by proving a special semantic invariant for the
-- self-diagonal SAT family which does NOT hold for generic Boolean functions.
------------------------------------------------------------------------
