{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayVoyagerR4HodgeBasisExact where

-- Exact, finite, *flat Euclidean and oriented* R4 Hodge-star action
-- on signed basis 2-forms. This is the classical algebraic donor for
-- the Donaldson/instanton segment of Voyager 2026; it is NOT an
-- instanton moduli-space construction, R4 smooth-structure theorem,
-- Lorentzian star, quantum YM continuum measure or Clay mass gap.
--
-- In four-dimensional positively oriented Euclidean orthonormal
-- coordinates, * e01 = e23, * e02 = -e13, * e03 = e12,
-- * e12 = e03, * e13 = -e02, * e23 = e01.
-- Thus *^2=+1 on real 2-forms (different from Lorentz signature).
-- These are standard Hodge linear-algebra facts; DASHI owns this
-- finite signed-basis proof expression only.

open import Agda.Builtin.Equality using (_≡_; refl)

data Sign : Set where
  plus : Sign
  minus : Sign

data BasisTwoForm : Set where
  e01 : BasisTwoForm
  e02 : BasisTwoForm
  e03 : BasisTwoForm
  e12 : BasisTwoForm
  e13 : BasisTwoForm
  e23 : BasisTwoForm

record SignedBasisTwoForm : Set where
  constructor signed
  field
    sign : Sign
    basis : BasisTwoForm

flip : Sign → Sign
flip plus = minus
flip minus = plus

flipInvolutive : ∀ s → flip (flip s) ≡ s
flipInvolutive plus = refl
flipInvolutive minus = refl

euclideanHodgeStar : SignedBasisTwoForm → SignedBasisTwoForm
euclideanHodgeStar (signed s e01) = signed s e23
euclideanHodgeStar (signed s e02) = signed (flip s) e13
euclideanHodgeStar (signed s e03) = signed s e12
euclideanHodgeStar (signed s e12) = signed s e03
euclideanHodgeStar (signed s e13) = signed (flip s) e02
euclideanHodgeStar (signed s e23) = signed s e01

hodgeSquareOnSignedBasis :
  ∀ b → euclideanHodgeStar (euclideanHodgeStar b) ≡ b
hodgeSquareOnSignedBasis (signed plus e01) = refl
hodgeSquareOnSignedBasis (signed minus e01) = refl
hodgeSquareOnSignedBasis (signed plus e02) = refl
hodgeSquareOnSignedBasis (signed minus e02) = refl
hodgeSquareOnSignedBasis (signed plus e03) = refl
hodgeSquareOnSignedBasis (signed minus e03) = refl
hodgeSquareOnSignedBasis (signed plus e12) = refl
hodgeSquareOnSignedBasis (signed minus e12) = refl
hodgeSquareOnSignedBasis (signed plus e13) = refl
hodgeSquareOnSignedBasis (signed minus e13) = refl
hodgeSquareOnSignedBasis (signed plus e23) = refl
hodgeSquareOnSignedBasis (signed minus e23) = refl

-- Four-dimensional Hodge-star eigenspace projection F^±=(F±*F)/2
-- requires extension from this *basis action* to genuine linear
-- 2-forms, scalar half, an oriented Euclidean metric and connection
-- curvature. These are explicit follow-on mathematical obligations.
data ClassicalInstantonNext : Set where
  extendStarLinearlyToR4TwoForms : ClassicalInstantonNext
  constructSelfAndAntiSelfDualProjectors : ClassicalInstantonNext
  selectedConnectionCurvature : ClassicalInstantonNext
  verifyASDImpliesClassicalYMEulerLagrange : ClassicalInstantonNext
  constructGaugeModuliAndRegularity : ClassicalInstantonNext
  importDonaldsonIntersectionFormTheorems : ClassicalInstantonNext
  combineFreedmanCassonGompfExoticR4Theorem : ClassicalInstantonNext
  keepQuantumClayGapSeparate : ClassicalInstantonNext
