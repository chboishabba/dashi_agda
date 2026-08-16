module DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlTail23AtomsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
-- Kenneth G. Wilson, "Confinement of Quarks", Physical Review D 10 (1974),
-- 2445--2459. DOI: 10.1103/PhysRevD.10.2445.
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base as ℚ using (0ℚ; _+_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlScalarExact
open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlDiagonalAtomsExact

pair23Atom : ∀ c d →
  wilsonAtomContribution
    (pureQuaternion (negV c) *q
      (pureQuaternion (negV d) *q orderedValueProduct []))
  ≡ vectorDot c d
pair23Atom c d =
  trans
    (cong wilsonAtomContribution
      (cong (pureQuaternion (negV c) *q_)
        (oneQMultiplyRight (pureQuaternion (negV d)))))
    (pureNegBothScalar c d)

pair23OneOrderedCopy : ∀ c d →
  pairAtomSum (pureQuaternion (negV c))
    (flatExponentialJet (negV d) ∷ [])
  ≡ vectorDot c d
pair23OneOrderedCopy c d
  rewrite pairAtomSumFlatCons
      (pureQuaternion (negV c))
      (pureQuaternion (negV d))
      (pureQuaternion (negV d) *q pureQuaternion (negV d))
      []
    | pair23Atom c d
    | ℚP.+-identityʳ (vectorDot c d) = refl

pair23TwoOrderedCopies : ∀ c d →
  pairAtomSum (pureQuaternion (negV c))
      (flatExponentialJet (negV d) ∷ [])
    + pairAtomSum (pureQuaternion (negV c))
      (flatExponentialJet (negV d) ∷ [])
  ≡ vectorDot c d + vectorDot c d
pair23TwoOrderedCopies c d =
  cong₂ _+_ (pair23OneOrderedCopy c d) (pair23OneOrderedCopy c d)

flatTail3AtomSum : ∀ d →
  wilsonSecondVariationAtomSum (flatExponentialJet (negV d) ∷ [])
  ≡ vectorDot d d
flatTail3AtomSum d
  rewrite flatSecondAtomRecurrence
      (pureQuaternion (negV d))
      (pureQuaternion (negV d) *q pureQuaternion (negV d))
      []
    | flatDiagonal3 d
    | ℚP.+-identityʳ 0ℚ
    | ℚP.+-identityʳ 0ℚ
    | ℚP.+-identityʳ (vectorDot d d) = refl

flatTail23AtomFamily : ∀ c d →
  wilsonSecondVariationAtomSum
    (flatExponentialJet (negV c) ∷ flatExponentialJet (negV d) ∷ [])
  ≡ vectorDot c c
    + (vectorDot c d + (vectorDot c d + vectorDot d d))
flatTail23AtomFamily c d
  rewrite flatSecondAtomRecurrence
      (pureQuaternion (negV c))
      (pureQuaternion (negV c) *q pureQuaternion (negV c))
      (flatExponentialJet (negV d) ∷ [])
    | flatDiagonal2 c d
    | pair23OneOrderedCopy c d
    | flatTail3AtomSum d = refl
