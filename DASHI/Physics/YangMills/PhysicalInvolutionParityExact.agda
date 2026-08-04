module DASHI.Physics.YangMills.PhysicalInvolutionParityExact where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Physical parity is always relative to a named involution.  Coordinate
-- negation, link inversion, contour reversal, gauge reflection and field
-- reflection are deliberately not identified by this interface.
------------------------------------------------------------------------

record Involution (Carrier : Set) : Set₁ where
  field
    reverse : Carrier → Carrier
    reverseInvolutive : ∀ value → reverse (reverse value) ≡ value

open Involution public

record SetoidInvolution (Carrier : Set) : Set₁ where
  field
    Equivalent : Carrier → Carrier → Set
    equivalentRefl : ∀ value → Equivalent value value
    equivalentSym : ∀ {left right} →
      Equivalent left right → Equivalent right left
    equivalentTrans : ∀ {left middle right} →
      Equivalent left middle → Equivalent middle right →
      Equivalent left right

    reverse : Carrier → Carrier
    reverseCongruent : ∀ {left right} →
      Equivalent left right →
      Equivalent (reverse left) (reverse right)
    reverseInvolutive : ∀ value →
      Equivalent (reverse (reverse value)) value

open SetoidInvolution public

record ParityCodomain (Carrier : Set) : Set₁ where
  field
    Equivalent : Carrier → Carrier → Set
    equivalentRefl : ∀ value → Equivalent value value
    equivalentSym : ∀ {left right} →
      Equivalent left right → Equivalent right left
    equivalentTrans : ∀ {left middle right} →
      Equivalent left middle → Equivalent middle right →
      Equivalent left right

    zero : Carrier
    add : Carrier → Carrier → Carrier
    negate : Carrier → Carrier

    addCongruent : ∀ {left left′ right right′} →
      Equivalent left left′ → Equivalent right right′ →
      Equivalent (add left right) (add left′ right′)

    addInverseRight : ∀ value →
      Equivalent (add value (negate value)) zero

    addInverseLeft : ∀ value →
      Equivalent (add (negate value) value) zero

    negateCongruent : ∀ {left right} →
      Equivalent left right →
      Equivalent (negate left) (negate right)

open ParityCodomain public

record EvenUnder
    {Domain Codomain : Set}
    (involution : Involution Domain)
    (codomain : ParityCodomain Codomain)
    (function : Domain → Codomain) : Set₁ where
  field
    evenLaw : ∀ value →
      Equivalent codomain
        (function (reverse involution value))
        (function value)

open EvenUnder public

record OddUnder
    {Domain Codomain : Set}
    (involution : Involution Domain)
    (codomain : ParityCodomain Codomain)
    (function : Domain → Codomain) : Set₁ where
  field
    oddLaw : ∀ value →
      Equivalent codomain
        (function (reverse involution value))
        (negate codomain (function value))

open OddUnder public

oddPairCancels :
  ∀ {Domain Codomain : Set}
    {involution : Involution Domain}
    {codomain : ParityCodomain Codomain}
    {function : Domain → Codomain} →
  OddUnder involution codomain function →
  ∀ value →
  Equivalent codomain
    (add codomain
      (function value)
      (function (reverse involution value)))
    (zero codomain)
oddPairCancels {codomain = codomain} {function = function}
    odd value =
  equivalentTrans codomain
    (addCongruent codomain
      (equivalentRefl codomain (function value))
      (oddLaw odd value))
    (addInverseRight codomain (function value))

oddReversePairCancels :
  ∀ {Domain Codomain : Set}
    {involution : Involution Domain}
    {codomain : ParityCodomain Codomain}
    {function : Domain → Codomain} →
  OddUnder involution codomain function →
  ∀ value →
  Equivalent codomain
    (add codomain
      (function (reverse involution value))
      (function value))
    (zero codomain)
oddReversePairCancels {codomain = codomain} {function = function}
    odd value =
  equivalentTrans codomain
    (addCongruent codomain
      (oddLaw odd value)
      (equivalentRefl codomain (function value)))
    (addInverseLeft codomain (function value))

record LinearParityCodomain (Scalar Vector : Set) : Set₁ where
  field
    vector : ParityCodomain Vector
    scale : Scalar → Vector → Vector
    scaleCongruent : ∀ scalar {left right} →
      Equivalent vector left right →
      Equivalent vector (scale scalar left) (scale scalar right)
    scaleNegate : ∀ scalar value →
      Equivalent vector
        (scale scalar (negate vector value))
        (negate vector (scale scalar value))

open LinearParityCodomain public

weightedOddPairCancels :
  ∀ {Domain Scalar Vector : Set}
    {involution : Involution Domain}
    {linear : LinearParityCodomain Scalar Vector}
    {function : Domain → Vector} →
  OddUnder involution (vector linear) function →
  ∀ scalar value →
  Equivalent (vector linear)
    (add (vector linear)
      (scale linear scalar (function value))
      (scale linear scalar
        (function (reverse involution value))))
    (zero (vector linear))
weightedOddPairCancels {linear = linear} {function = function}
    odd scalar value =
  equivalentTrans (vector linear)
    (addCongruent (vector linear)
      (equivalentRefl (vector linear)
        (scale linear scalar (function value)))
      (equivalentTrans (vector linear)
        (scaleCongruent linear scalar (oddLaw odd value))
        (scaleNegate linear scalar (function value))))
    (addInverseRight (vector linear)
      (scale linear scalar (function value)))

identityInvolution : ∀ {Carrier : Set} → Involution Carrier
identityInvolution = record
  { reverse = λ value → value
  ; reverseInvolutive = λ value → refl
  }

record PhysicalInvolutionFamily : Set₁ where
  field
    Coordinate Link Contour GaugeConfiguration Field : Set

    coordinateInvolution : Involution Coordinate
    linkInvolution : Involution Link
    contourInvolution : Involution Contour
    gaugeInvolution : Involution GaugeConfiguration
    fieldInvolution : Involution Field

open PhysicalInvolutionFamily public

physicalInvolutionCoreLevel : ProofLevel
physicalInvolutionCoreLevel = machineChecked

oddPairCancellationLevel : ProofLevel
oddPairCancellationLevel = machineChecked

physicalInvolutionIdentificationLevel : ProofLevel
physicalInvolutionIdentificationLevel = conditional
