module DASHI.Mathematics.Algebra.CompositionAlgebraCoreExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Adolf Hurwitz,
-- "Über die Komposition der quadratischen Formen".
-- DOI: 10.1007/BF01448439.
--
-- John C. Baez,
-- "The Octonions".
-- DOI: 10.1090/S0273-0979-01-00934-X.
--
-- Aleksandra Galecka,
-- "A Proof of the Hurwitz Theorem About Composition Algebras".
-- DOI: 10.24917/20809751.13.4.
--
-- DASHI CONTRIBUTION
--
-- Extract the common checked interface shared by the concrete rational
-- quaternion and octonion modules.  A composition core consists of a carrier,
-- multiplication, conjugation and quadratic norm with involutive
-- anti-multiplicative conjugation and norm composition.
--
-- Associativity and alternativity are layered records rather than Boolean
-- labels.  The quaternion instance inhabits the associative layer; the
-- octonion instance inhabits the alternative/flexible layer and carries an
-- explicit associativity counterexample.
--
-- Division, positive definiteness over R, finite dimensionality and the
-- completeness direction of Hurwitz's theorem remain separate obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; _*_)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as CD
import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O

record CompositionCore : Set₁ where
  field
    Carrier : Set
    multiply : Carrier → Carrier → Carrier
    conjugate : Carrier → Carrier
    normSq : Carrier → ℚ
    conjugateInvolutive : ∀ value →
      conjugate (conjugate value) ≡ value
    conjugateReversesProduct : ∀ left right →
      conjugate (multiply left right)
      ≡ multiply (conjugate right) (conjugate left)
    normComposes : ∀ left right →
      normSq (multiply left right)
      ≡ normSq left * normSq right

open CompositionCore public

record AssociativeCompositionCore : Set₁ where
  field
    associativeCore : CompositionCore
    associative : ∀ left middle right →
      multiply associativeCore
        (multiply associativeCore left middle) right
      ≡ multiply associativeCore left
        (multiply associativeCore middle right)

record AlternativeCompositionCore : Set₁ where
  field
    alternativeCore : CompositionCore
    leftAlternative : ∀ left right →
      multiply alternativeCore
        (multiply alternativeCore left left) right
      ≡ multiply alternativeCore left
        (multiply alternativeCore left right)
    rightAlternative : ∀ left right →
      multiply alternativeCore
        (multiply alternativeCore left right) right
      ≡ multiply alternativeCore left
        (multiply alternativeCore right right)
    flexible : ∀ left right →
      multiply alternativeCore
        (multiply alternativeCore left right) left
      ≡ multiply alternativeCore left
        (multiply alternativeCore right left)

record AssociativityFailure
    (core : CompositionCore) : Set where
  field
    failureLeft failureMiddle failureRight : Carrier core
    associativityWouldContradict :
      (multiply core
        (multiply core failureLeft failureMiddle) failureRight
      ≡ multiply core failureLeft
        (multiply core failureMiddle failureRight)) → ⊥

------------------------------------------------------------------------
-- Concrete repository instances.
------------------------------------------------------------------------

quaternionCompositionCore : CompositionCore
quaternionCompositionCore = record
  { Carrier = Q.RationalQuaternion
  ; multiply = Q._*q_
  ; conjugate = CD.quaternionConjugate
  ; normSq = CD.quaternionNormSq
  ; conjugateInvolutive = CD.quaternionConjugateInvolutive
  ; conjugateReversesProduct = CD.quaternionConjugateReversesProduct
  ; normComposes = CD.quaternionNormMultiplicative
  }

quaternionAssociativeCompositionCore : AssociativeCompositionCore
quaternionAssociativeCompositionCore = record
  { associativeCore = quaternionCompositionCore
  ; associative = Q.quaternionMultiplyAssociative
  }

octonionCompositionCore : CompositionCore
octonionCompositionCore = record
  { Carrier = O.RationalOctonion
  ; multiply = O._*o_
  ; conjugate = O.octonionConjugate
  ; normSq = O.octonionNormSq
  ; conjugateInvolutive = O.octonionConjugateInvolutive
  ; conjugateReversesProduct = O.octonionConjugateReversesProduct
  ; normComposes = O.octonionNormMultiplicative
  }

octonionAlternativeCompositionCore : AlternativeCompositionCore
octonionAlternativeCompositionCore = record
  { alternativeCore = octonionCompositionCore
  ; leftAlternative = O.octonionLeftAlternative
  ; rightAlternative = O.octonionRightAlternative
  ; flexible = O.octonionFlexible
  }

octonionAssociativityFailure :
  AssociativityFailure octonionCompositionCore
octonionAssociativityFailure = record
  { failureLeft = O.e1
  ; failureMiddle = O.e2
  ; failureRight = O.e4
  ; associativityWouldContradict = O.e124AssociativityFails
  }

record AnalyticCompositionObligations
    (core : CompositionCore) : Set₁ where
  field
    realScalarCarrier : Set
    finiteDimensionality : Set
    positiveDefiniteNorm : Set
    nonzeroInverseConstruction : Set
    classificationCompleteness : Set

-- No canonical inhabitant is supplied from CompositionCore alone: the exact
-- rational polynomial identities do not manufacture the real analytic and
-- classification hypotheses.
