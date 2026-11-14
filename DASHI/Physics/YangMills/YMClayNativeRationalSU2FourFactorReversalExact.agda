module DASHI.Physics.YangMills.YMClayNativeRationalSU2FourFactorReversalExact where

------------------------------------------------------------------------
-- EXACT ORIGINAL NATIVE RATIONAL SU2 FOUR-FACTOR REVERSE WILSON TRACE
--
-- The previous BalabanP33PlaquetteOrientationReversalExact works on its
-- own rational quaternion polynomial jet carrier. This module is the
-- *distinct actual norm-one link* carrier from
-- BalabanClayGate4RationalSU2ExactGroupLaws.
--
-- For A,B,C,D in unit SU(2) quaternions, the forward lattice plaquette
-- is A B C^-1 D^-1. Reversing orientation is D C B^-1 A^-1.
-- The second is exactly inverse of the first; the quaternion scalar-part
-- trace is preserved. These are universal exact group laws, not numerical
-- tests; the physical four-site signed path/layout and source six-plane
-- summed action are distinct downstream attachments.
--
-- Existing mathematical authorship: Wilson, Hall, and existing DASHI
-- native quaternion group-law owners; no physical continuum assertion.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Q

infixl 20 _⊗_

_⊗_ : SU2.RationalUnitQuaternion →
       SU2.RationalUnitQuaternion → SU2.RationalUnitQuaternion
_⊗_ = Q.multiplyRationalSU2

inv : SU2.RationalUnitQuaternion → SU2.RationalUnitQuaternion
inv = Q.inverseRationalSU2

forwardPlaquetteFour :
  SU2.RationalUnitQuaternion → SU2.RationalUnitQuaternion →
  SU2.RationalUnitQuaternion → SU2.RationalUnitQuaternion →
  SU2.RationalUnitQuaternion
forwardPlaquetteFour a b c d =
  a ⊗ (b ⊗ (inv c ⊗ inv d))

reversePlaquetteFour :
  SU2.RationalUnitQuaternion → SU2.RationalUnitQuaternion →
  SU2.RationalUnitQuaternion → SU2.RationalUnitQuaternion →
  SU2.RationalUnitQuaternion
reversePlaquetteFour a b c d =
  ((d ⊗ c) ⊗ inv b) ⊗ inv a

inverseFourIsReversedPlaquette :
  ∀ a b c d →
  inv (forwardPlaquetteFour a b c d)
  ≡ reversePlaquetteFour a b c d
inverseFourIsReversedPlaquette a b c d
  rewrite Q.inverseProduct a (b ⊗ (inv c ⊗ inv d))
        | Q.inverseProduct b (inv c ⊗ inv d)
        | Q.inverseProduct (inv c) (inv d)
        | Q.inverseInverse d
        | Q.inverseInverse c = refl

realTraceInverse :
  ∀ q → SU2.realPart (inv q) ≡ SU2.realPart q
realTraceInverse q = refl

forwardReverseFourTraceSame :
  ∀ a b c d →
  SU2.realPart (forwardPlaquetteFour a b c d)
  ≡ SU2.realPart (reversePlaquetteFour a b c d)
forwardReverseFourTraceSame a b c d =
  trans
    (sym (realTraceInverse (forwardPlaquetteFour a b c d)))
    (cong SU2.realPart (inverseFourIsReversedPlaquette a b c d))
