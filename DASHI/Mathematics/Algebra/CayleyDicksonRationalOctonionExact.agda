module DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John C. Baez,
-- "The Octonions", Bulletin of the American Mathematical Society 39 (2002),
-- 145--205.
-- DOI: 10.1090/S0273-0979-01-00934-X.
--
-- Richard D. Schafer,
-- "An Introduction to Nonassociative Algebras" (Academic Press, 1966).
-- No DOI assigned or verified for the original book.
--
-- DASHI CONTRIBUTION
--
-- Apply the same Cayley--Dickson convention used in the rational
-- complex-to-quaternion bridge once more to the repository's exact rational
-- quaternion carrier:
--
--   (a,b)(c,d) = (ac - conjugate(d)b , da + b conjugate(c)).
--
-- The resulting eight-coordinate rational octonion carrier is proved to have
-- involutive anti-multiplicative conjugation, multiplicative quadratic norm,
-- and the left and right alternative laws.  The basis computation
--
--   (e1 e2)e4 =  e7,
--   e1(e2 e4) = -e7
--
-- supplies an explicit checked failure of associativity under the repository
-- convention.
--
-- This is an exact rational polynomial formalisation.  It does not prove the
-- analytic real division property, positivity/completeness over R, the full
-- Hurwitz classification, Moufang-loop topology, or exceptional Lie-group
-- structure.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as CD

qSub : Q.RationalQuaternion → Q.RationalQuaternion → Q.RationalQuaternion
qSub left right = Q._+q_ left (Q.negQ right)

record RationalOctonion : Set where
  constructor oct
  field
    oFirst oSecond : Q.RationalQuaternion

open RationalOctonion public

zeroO oneO : RationalOctonion
zeroO = oct Q.zeroQ Q.zeroQ
oneO  = oct Q.oneQ Q.zeroQ

_+o_ : RationalOctonion → RationalOctonion → RationalOctonion
oct a b +o oct c d = oct (Q._+q_ a c) (Q._+q_ b d)

negO : RationalOctonion → RationalOctonion
negO (oct a b) = oct (Q.negQ a) (Q.negQ b)

_*o_ : RationalOctonion → RationalOctonion → RationalOctonion
oct a b *o oct c d =
  oct
    (qSub (Q._*q_ a c)
      (Q._*q_ (CD.quaternionConjugate d) b))
    (Q._+q_
      (Q._*q_ d a)
      (Q._*q_ b (CD.quaternionConjugate c)))

octonionConjugate : RationalOctonion → RationalOctonion
octonionConjugate (oct a b) =
  oct (CD.quaternionConjugate a) (Q.negQ b)

octonionNormSq : RationalOctonion → ℚ
octonionNormSq (oct a b) =
  CD.quaternionNormSq a + CD.quaternionNormSq b

octonionExt :
  ∀ {left right} →
  oFirst left ≡ oFirst right →
  oSecond left ≡ oSecond right →
  left ≡ right
octonionExt {oct _ _} {oct _ _} refl refl = refl

------------------------------------------------------------------------
-- Conjugation and composition.
------------------------------------------------------------------------

octonionConjugateInvolutive : ∀ value →
  octonionConjugate (octonionConjugate value) ≡ value
octonionConjugateInvolutive
    (oct (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3)) =
  octonionExt
    (Q.quaternionExt
      (solve (a0 ∷ [])) (solve (a1 ∷ []))
      (solve (a2 ∷ [])) (solve (a3 ∷ [])))
    (Q.quaternionExt
      (solve (b0 ∷ [])) (solve (b1 ∷ []))
      (solve (b2 ∷ [])) (solve (b3 ∷ [])))

octonionConjugateReversesProduct : ∀ left right →
  octonionConjugate (left *o right)
  ≡ octonionConjugate right *o octonionConjugate left
octonionConjugateReversesProduct
    (oct (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3))
    (oct (Q.quat c0 c1 c2 c3) (Q.quat d0 d1 d2 d3)) =
  octonionExt
    (Q.quaternionExt
      (solve vars) (solve vars) (solve vars) (solve vars))
    (Q.quaternionExt
      (solve vars) (solve vars) (solve vars) (solve vars))
  where
    vars : List ℚ
    vars =
      a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ d0 ∷ d1 ∷ d2 ∷ d3 ∷ []

octonionNormMultiplicative : ∀ left right →
  octonionNormSq (left *o right)
  ≡ octonionNormSq left * octonionNormSq right
octonionNormMultiplicative
    (oct (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3))
    (oct (Q.quat c0 c1 c2 c3) (Q.quat d0 d1 d2 d3)) =
  solve
    (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
     c0 ∷ c1 ∷ c2 ∷ c3 ∷ d0 ∷ d1 ∷ d2 ∷ d3 ∷ [])

------------------------------------------------------------------------
-- Alternativity.
------------------------------------------------------------------------

octonionLeftAlternative : ∀ left right →
  (left *o left) *o right ≡ left *o (left *o right)
octonionLeftAlternative
    (oct (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3))
    (oct (Q.quat c0 c1 c2 c3) (Q.quat d0 d1 d2 d3)) =
  octonionExt
    (Q.quaternionExt
      (solve vars) (solve vars) (solve vars) (solve vars))
    (Q.quaternionExt
      (solve vars) (solve vars) (solve vars) (solve vars))
  where
    vars : List ℚ
    vars =
      a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ d0 ∷ d1 ∷ d2 ∷ d3 ∷ []

octonionRightAlternative : ∀ left right →
  (left *o right) *o right ≡ left *o (right *o right)
octonionRightAlternative
    (oct (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3))
    (oct (Q.quat c0 c1 c2 c3) (Q.quat d0 d1 d2 d3)) =
  octonionExt
    (Q.quaternionExt
      (solve vars) (solve vars) (solve vars) (solve vars))
    (Q.quaternionExt
      (solve vars) (solve vars) (solve vars) (solve vars))
  where
    vars : List ℚ
    vars =
      a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ d0 ∷ d1 ∷ d2 ∷ d3 ∷ []

octonionFlexible : ∀ left right →
  (left *o right) *o left ≡ left *o (right *o left)
octonionFlexible
    (oct (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3))
    (oct (Q.quat c0 c1 c2 c3) (Q.quat d0 d1 d2 d3)) =
  octonionExt
    (Q.quaternionExt
      (solve vars) (solve vars) (solve vars) (solve vars))
    (Q.quaternionExt
      (solve vars) (solve vars) (solve vars) (solve vars))
  where
    vars : List ℚ
    vars =
      a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ d0 ∷ d1 ∷ d2 ∷ d3 ∷ []

------------------------------------------------------------------------
-- Explicit nonassociative basis witness.
------------------------------------------------------------------------

e1 e2 e4 e7 : RationalOctonion
e1 = oct (Q.quat 0ℚ 1ℚ 0ℚ 0ℚ) Q.zeroQ
e2 = oct (Q.quat 0ℚ 0ℚ 1ℚ 0ℚ) Q.zeroQ
e4 = oct Q.zeroQ (Q.quat 1ℚ 0ℚ 0ℚ 0ℚ)
e7 = oct Q.zeroQ (Q.quat 0ℚ 0ℚ 0ℚ 1ℚ)

leftAssociatedE124 :
  (e1 *o e2) *o e4 ≡ e7
leftAssociatedE124 =
  octonionExt
    (Q.quaternionExt (solve []) (solve []) (solve []) (solve []))
    (Q.quaternionExt (solve []) (solve []) (solve []) (solve []))

rightAssociatedE124 :
  e1 *o (e2 *o e4) ≡ negO e7
rightAssociatedE124 =
  octonionExt
    (Q.quaternionExt (solve []) (solve []) (solve []) (solve []))
    (Q.quaternionExt (solve []) (solve []) (solve []) (solve []))

seventhCoordinate : RationalOctonion → ℚ
seventhCoordinate (oct _ (Q.quat _ _ _ coordinate)) = coordinate

oneIsNotNegativeOne : 1ℚ ≡ - 1ℚ → ⊥
oneIsNotNegativeOne ()

e7IsNotNegativeE7 : e7 ≡ negO e7 → ⊥
e7IsNotNegativeE7 equality =
  oneIsNotNegativeOne (cong seventhCoordinate equality)

e124AssociativityFails :
  ((e1 *o e2) *o e4 ≡ e1 *o (e2 *o e4)) → ⊥
e124AssociativityFails equality =
  e7IsNotNegativeE7
    (trans
      (sym leftAssociatedE124)
      (trans equality rightAssociatedE124))
