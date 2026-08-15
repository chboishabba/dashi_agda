module DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlAtomAssemblyExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
-- Kenneth G. Wilson, "Confinement of Quarks", Physical Review D 10 (1974),
-- 2445--2459. DOI: 10.1103/PhysRevD.10.2445.
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- The assembly keeps the exact secondVariationTerms recursion order.  The two
-- copies of every ordered first/first atom remain distinct until after q0 has
-- been projected to the scalar dot product.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; -_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlScalarExact
open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlDiagonalAtomsExact
open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlRow0AtomsExact
open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlRow1AtomsExact
open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlTail23AtomsExact

flatRecursionDotExpansion :
  RationalVector3 → RationalVector3 → RationalVector3 → RationalVector3 → ℚ
flatRecursionDotExpansion a b c d =
  vectorDot a a
  + (row0Scalar + (row0Scalar
    + (vectorDot b b
      + (row1Scalar + (row1Scalar
        + (vectorDot c c
          + (vectorDot c d + (vectorDot c d + vectorDot d d))))))))
  where
    row0Scalar = vectorDot a b + ((- vectorDot a c) + (- vectorDot a d))
    row1Scalar = (- vectorDot b c) + (- vectorDot b d)

flatTail123AtomFamily : ∀ b c d →
  wilsonSecondVariationAtomSum
    (flatExponentialJet b ∷ flatExponentialJet (negV c) ∷
      flatExponentialJet (negV d) ∷ [])
  ≡ vectorDot b b
    + (((- vectorDot b c) + (- vectorDot b d))
      + (((- vectorDot b c) + (- vectorDot b d))
        + (vectorDot c c
          + (vectorDot c d + (vectorDot c d + vectorDot d d)))))
flatTail123AtomFamily b c d
  rewrite flatSecondAtomRecurrence
      (pureQuaternion b)
      (pureQuaternion b *q pureQuaternion b)
      (flatExponentialJet (negV c) ∷ flatExponentialJet (negV d) ∷ [])
    | flatDiagonal1 b c d
    | row1OneOrderedCopy b c d
    | flatTail23AtomFamily c d = refl

flatFourFactorAtomFamilyExpansion : ∀ a b c d →
  wilsonSecondVariationAtomSum
    (flatOrientedPlaquetteJets a b c d)
  ≡ flatRecursionDotExpansion a b c d
flatFourFactorAtomFamilyExpansion a b c d
  rewrite flatSecondAtomRecurrence
      (pureQuaternion a)
      (pureQuaternion a *q pureQuaternion a)
      (flatExponentialJet b ∷ flatExponentialJet (negV c) ∷
        flatExponentialJet (negV d) ∷ [])
    | flatDiagonal0 a b c d
    | row0OneOrderedCopy a b c d
    | flatTail123AtomFamily b c d = refl

flatSecondVariationRecursionDotExpansion : ∀ a b c d →
  flatOrientedPlaquetteSecondVariation a b c d
  ≡ flatRecursionDotExpansion a b c d
flatSecondVariationRecursionDotExpansion a b c d =
  trans
    (wilsonSecondVariationIsAtomSum (flatOrientedPlaquetteJets a b c d))
    (flatFourFactorAtomFamilyExpansion a b c d)
