module DASHI.Physics.YangMills.BalabanClayCommonTaylorRemainderToEnclosureExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literature normalization.
--
-- Marc Daumas, David Lester and César Muñoz,
-- "Verified Real Number Calculations: A Library for Interval Arithmetic",
-- IEEE Transactions on Computers 58 (2009), 226--237.
-- DOI: 10.1109/TC.2008.213; arXiv:0708.3721
-- Relationship: proof-assistant architecture for converting Taylor remainder
-- estimates into certified interval enclosures.
--
-- This module contains only order/equality transport.  The derivative bound or
-- alternating-series estimate that controls the remainder remains a separately
-- named analytic authority.
------------------------------------------------------------------------

record OrderedAdditiveEnclosure (Scalar : Set) : Set₁ where
  field
    zero : Scalar
    add : Scalar → Scalar → Scalar
    negate : Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (add left right) (add leftUpper rightUpper)

open OrderedAdditiveEnclosure public

record SymmetricTaylorRemainder
    {Scalar : Set}
    (order : OrderedAdditiveEnclosure Scalar)
    (Point : Set) : Set₁ where
  field
    function polynomial remainder error : Point → Scalar

    exactDecomposition : ∀ point →
      function point ≡ add order (polynomial point) (remainder point)

    remainderLower : ∀ point →
      LessEqual order (negate order (error point)) (remainder point)

    remainderUpper : ∀ point →
      LessEqual order (remainder point) (error point)

open SymmetricTaylorRemainder public

lowerEnclosure :
  ∀ {Scalar Point}
    {order : OrderedAdditiveEnclosure Scalar} →
  SymmetricTaylorRemainder order Point → Point → Scalar
lowerEnclosure {order = order} dataSet point =
  add order (polynomial dataSet point) (negate order (error dataSet point))

upperEnclosure :
  ∀ {Scalar Point}
    {order : OrderedAdditiveEnclosure Scalar} →
  SymmetricTaylorRemainder order Point → Point → Scalar
upperEnclosure {order = order} dataSet point =
  add order (polynomial dataSet point) (error dataSet point)

lowerEnclosureCorrect :
  ∀ {Scalar Point}
    {order : OrderedAdditiveEnclosure Scalar}
    (dataSet : SymmetricTaylorRemainder order Point)
    point →
  LessEqual order (lowerEnclosure dataSet point) (function dataSet point)
lowerEnclosureCorrect {order = order} dataSet point =
  subst
    (λ upper → LessEqual order (lowerEnclosure dataSet point) upper)
    (sym (exactDecomposition dataSet point))
    (addMonotone order
      (reflexive order (polynomial dataSet point))
      (remainderLower dataSet point))

upperEnclosureCorrect :
  ∀ {Scalar Point}
    {order : OrderedAdditiveEnclosure Scalar}
    (dataSet : SymmetricTaylorRemainder order Point)
    point →
  LessEqual order (function dataSet point) (upperEnclosure dataSet point)
upperEnclosureCorrect {order = order} dataSet point =
  subst
    (λ lower → LessEqual order lower (upperEnclosure dataSet point))
    (exactDecomposition dataSet point)
    (addMonotone order
      (reflexive order (polynomial dataSet point))
      (remainderUpper dataSet point))

------------------------------------------------------------------------
-- Alternating one-sided form.  This is the pattern used for the configured
-- sine/cosine/sinc polynomials on [0,1/2].
------------------------------------------------------------------------

record AlternatingTaylorBracket
    {Scalar : Set}
    (order : OrderedAdditiveEnclosure Scalar)
    (Point : Set) : Set₁ where
  field
    function lowerPolynomial upperPolynomial : Point → Scalar
    lowerCorrectInput : ∀ point →
      LessEqual order (lowerPolynomial point) (function point)
    upperCorrectInput : ∀ point →
      LessEqual order (function point) (upperPolynomial point)

open AlternatingTaylorBracket public

alternatingLowerCorrect = lowerCorrectInput
alternatingUpperCorrect = upperCorrectInput

symmetricRemainderReductionLevel : ProofLevel
symmetricRemainderReductionLevel = machineChecked

alternatingBracketReductionLevel : ProofLevel
alternatingBracketReductionLevel = machineChecked

literalDerivativeOrAlternatingRemainderInputsLevel : ProofLevel
literalDerivativeOrAlternatingRemainderInputsLevel = conditional
