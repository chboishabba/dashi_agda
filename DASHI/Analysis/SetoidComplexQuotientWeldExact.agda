module DASHI.Analysis.SetoidComplexQuotientWeldExact where

------------------------------------------------------------------------
-- SETOID COMPLEX -> PROPOSITIONAL-QUOTIENT ConcreteComplex WELD
--
-- DASHI CONTRIBUTION
--
-- The repository already separates:
--
--   * setoid-native constructive complete reals; and
--   * the older propositional-equality ConstructedOrderedCompleteReal carrier.
--
-- A PropositionalQuotientRealization supplies the latter carrier, but its
-- generic spine intentionally leaves "operationsAgree" opaque.  Moonshine's
-- literal q/E4/E6 evaluator needs a sharper same-object statement: quotienting
-- real and imaginary components must commute with the ordinary complex ring
-- operations.
--
-- This owner factors that obligation once.  It does NOT construct a quotient,
-- representative choice, exponential, logarithm, polar branch, or modulus
-- theorem.  Those remain independent inputs.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Analysis.ConcreteComplex as LegacyComplex

------------------------------------------------------------------------
-- Explicit quotient-operation compatibility.
------------------------------------------------------------------------

record PropositionalQuotientOperationCompatibility
    (R : Spine.SetoidOrderedCompleteReal)
    (Q : Spine.PropositionalQuotientRealization R) : Set₁ where
  field
    quotientZero :
      Spine.quotient Q (Spine.zero R) ≡ Spine.zeroQ Q

    quotientOne :
      Spine.quotient Q (Spine.one R) ≡ Spine.oneQ Q

    quotientAdd : ∀ left right →
      Spine.quotient Q (Spine._+_ R left right)
      ≡ Spine.addQ Q
          (Spine.quotient Q left)
          (Spine.quotient Q right)

    quotientSub : ∀ left right →
      Spine.quotient Q (Spine._-_ R left right)
      ≡ Spine.subQ Q
          (Spine.quotient Q left)
          (Spine.quotient Q right)

    quotientMul : ∀ left right →
      Spine.quotient Q (Spine._*_ R left right)
      ≡ Spine.mulQ Q
          (Spine.quotient Q left)
          (Spine.quotient Q right)

    quotientNeg : ∀ value →
      Spine.quotient Q (Spine.neg R value)
      ≡ Spine.negQ Q (Spine.quotient Q value)

    quotientAbs : ∀ value →
      Spine.quotient Q (Spine.abs R value)
      ≡ Spine.absQ Q (Spine.quotient Q value)

open PropositionalQuotientOperationCompatibility public

------------------------------------------------------------------------
-- Setoid-side complex pair on the exact selected real carrier.
------------------------------------------------------------------------

record SetoidComplexPair (R : Spine.SetoidOrderedCompleteReal) : Set where
  constructor setoid-complex
  field
    reSC imSC : Spine.Carrier R

open SetoidComplexPair public

zeroSC : (R : Spine.SetoidOrderedCompleteReal) → SetoidComplexPair R
zeroSC R = setoid-complex (Spine.zero R) (Spine.zero R)

oneSC : (R : Spine.SetoidOrderedCompleteReal) → SetoidComplexPair R
oneSC R = setoid-complex (Spine.one R) (Spine.zero R)

imaginaryUnitSC :
  (R : Spine.SetoidOrderedCompleteReal) → SetoidComplexPair R
imaginaryUnitSC R = setoid-complex (Spine.zero R) (Spine.one R)

addSC :
  (R : Spine.SetoidOrderedCompleteReal) →
  SetoidComplexPair R → SetoidComplexPair R → SetoidComplexPair R
addSC R (setoid-complex a b) (setoid-complex c d) =
  setoid-complex
    (Spine._+_ R a c)
    (Spine._+_ R b d)

subSC :
  (R : Spine.SetoidOrderedCompleteReal) →
  SetoidComplexPair R → SetoidComplexPair R → SetoidComplexPair R
subSC R (setoid-complex a b) (setoid-complex c d) =
  setoid-complex
    (Spine._-_ R a c)
    (Spine._-_ R b d)

mulSC :
  (R : Spine.SetoidOrderedCompleteReal) →
  SetoidComplexPair R → SetoidComplexPair R → SetoidComplexPair R
mulSC R (setoid-complex a b) (setoid-complex c d) =
  setoid-complex
    (Spine._-_ R
      (Spine._*_ R a c)
      (Spine._*_ R b d))
    (Spine._+_ R
      (Spine._*_ R a d)
      (Spine._*_ R b c))

conjugateSC :
  (R : Spine.SetoidOrderedCompleteReal) →
  SetoidComplexPair R → SetoidComplexPair R
conjugateSC R (setoid-complex a b) =
  setoid-complex a (Spine.neg R b)

normSqSC :
  (R : Spine.SetoidOrderedCompleteReal) →
  SetoidComplexPair R → Spine.Carrier R
normSqSC R (setoid-complex a b) =
  Spine._+_ R
    (Spine._*_ R a a)
    (Spine._*_ R b b)

------------------------------------------------------------------------
-- Componentwise map into the literal legacy ConcreteComplex carrier.
------------------------------------------------------------------------

legacyComplex :
  ∀ {R : Spine.SetoidOrderedCompleteReal} →
  (Q : Spine.PropositionalQuotientRealization R) →
  SetoidComplexPair R →
  LegacyComplex.ComplexPair (Spine.asLegacyConstructedReal Q)
legacyComplex Q (setoid-complex a b) =
  LegacyComplex.complex
    (Spine.quotient Q a)
    (Spine.quotient Q b)

legacyComplexZero :
  ∀ {R : Spine.SetoidOrderedCompleteReal}
    {Q : Spine.PropositionalQuotientRealization R} →
  (compat : PropositionalQuotientOperationCompatibility R Q) →
  legacyComplex Q (zeroSC R) ≡ LegacyComplex.zeroC
legacyComplexZero compat
  rewrite quotientZero compat
  = refl

legacyComplexOne :
  ∀ {R : Spine.SetoidOrderedCompleteReal}
    {Q : Spine.PropositionalQuotientRealization R} →
  (compat : PropositionalQuotientOperationCompatibility R Q) →
  legacyComplex Q (oneSC R) ≡ LegacyComplex.oneC
legacyComplexOne compat
  rewrite quotientOne compat
        | quotientZero compat
  = refl

legacyComplexImaginaryUnit :
  ∀ {R : Spine.SetoidOrderedCompleteReal}
    {Q : Spine.PropositionalQuotientRealization R} →
  (compat : PropositionalQuotientOperationCompatibility R Q) →
  legacyComplex Q (imaginaryUnitSC R) ≡ LegacyComplex.imaginaryUnit
legacyComplexImaginaryUnit compat
  rewrite quotientZero compat
        | quotientOne compat
  = refl

legacyComplexAdd :
  ∀ {R : Spine.SetoidOrderedCompleteReal}
    {Q : Spine.PropositionalQuotientRealization R} →
  (compat : PropositionalQuotientOperationCompatibility R Q) →
  ∀ left right →
  legacyComplex Q (addSC R left right)
    ≡ LegacyComplex._+C_
        (legacyComplex Q left)
        (legacyComplex Q right)
legacyComplexAdd compat
  (setoid-complex a b)
  (setoid-complex c d)
  rewrite quotientAdd compat a c
        | quotientAdd compat b d
  = refl

legacyComplexSub :
  ∀ {R : Spine.SetoidOrderedCompleteReal}
    {Q : Spine.PropositionalQuotientRealization R} →
  (compat : PropositionalQuotientOperationCompatibility R Q) →
  ∀ left right →
  legacyComplex Q (subSC R left right)
    ≡ LegacyComplex._-C_
        (legacyComplex Q left)
        (legacyComplex Q right)
legacyComplexSub compat
  (setoid-complex a b)
  (setoid-complex c d)
  rewrite quotientSub compat a c
        | quotientSub compat b d
  = refl

legacyComplexMul :
  ∀ {R : Spine.SetoidOrderedCompleteReal}
    {Q : Spine.PropositionalQuotientRealization R} →
  (compat : PropositionalQuotientOperationCompatibility R Q) →
  ∀ left right →
  legacyComplex Q (mulSC R left right)
    ≡ LegacyComplex._*C_
        (legacyComplex Q left)
        (legacyComplex Q right)
legacyComplexMul compat
  (setoid-complex a b)
  (setoid-complex c d)
  rewrite quotientSub compat
            (Spine._*_ R a c)
            (Spine._*_ R b d)
        | quotientMul compat a c
        | quotientMul compat b d
        | quotientAdd compat
            (Spine._*_ R a d)
            (Spine._*_ R b c)
        | quotientMul compat a d
        | quotientMul compat b c
  = refl

legacyComplexConjugate :
  ∀ {R : Spine.SetoidOrderedCompleteReal}
    {Q : Spine.PropositionalQuotientRealization R} →
  (compat : PropositionalQuotientOperationCompatibility R Q) →
  ∀ value →
  legacyComplex Q (conjugateSC R value)
    ≡ LegacyComplex.conjugateC (legacyComplex Q value)
legacyComplexConjugate compat (setoid-complex a b)
  rewrite quotientNeg compat b
  = refl

legacyNormSq :
  ∀ {R : Spine.SetoidOrderedCompleteReal}
    {Q : Spine.PropositionalQuotientRealization R} →
  (compat : PropositionalQuotientOperationCompatibility R Q) →
  ∀ value →
  Spine.quotient Q (normSqSC R value)
    ≡ LegacyComplex.normSqC (legacyComplex Q value)
legacyNormSq compat (setoid-complex a b)
  rewrite quotientAdd compat
            (Spine._*_ R a a)
            (Spine._*_ R b b)
        | quotientMul compat a a
        | quotientMul compat b b
  = refl
