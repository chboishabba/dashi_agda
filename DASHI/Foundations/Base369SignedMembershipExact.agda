module DASHI.Foundations.Base369SignedMembershipExact where

------------------------------------------------------------------------
-- A Boolean predicate such as `isGood` normally identifies one subset and
-- sends every point outside that subset to `false`.  It does not distinguish
-- semantic opposition from absence, openness, or non-classification.
--
-- This module makes the smallest exact correction: positive membership,
-- exterior/non-member, and true inverse membership are separate constructors.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import Base369 using
  ( TriTruth
  ; tri-low
  ; tri-mid
  ; tri-high
  )

data SignedMembership : Set where
  memberOfInverse : SignedMembership
  notMemberOfEither : SignedMembership
  memberOfGood : SignedMembership

orientation : SignedMembership → TriTruth
orientation memberOfInverse = tri-low
orientation notMemberOfEither = tri-mid
orientation memberOfGood = tri-high

isGood : SignedMembership → Bool
isGood memberOfInverse = false
isGood notMemberOfEither = false
isGood memberOfGood = true

isInverse : SignedMembership → Bool
isInverse memberOfInverse = true
isInverse notMemberOfEither = false
isInverse memberOfGood = false

-- The ordinary Boolean projection identifies two semantically distinct states.
notGoodOutside : isGood notMemberOfEither ≡ false
notGoodOutside = refl

notGoodInverse : isGood memberOfInverse ≡ false
notGoodInverse = refl

outsideIsNotInverse : isInverse notMemberOfEither ≡ false
outsideIsNotInverse = refl

inverseIsInverse : isInverse memberOfInverse ≡ true
inverseIsInverse = refl

isGoodCollapsesInverseAndExterior :
  isGood memberOfInverse ≡ isGood notMemberOfEither
isGoodCollapsesInverseAndExterior = refl

data Empty : Set where

inverseAndExteriorRemainDistinct :
  memberOfInverse ≡ notMemberOfEither → Empty
inverseAndExteriorRemainDistinct ()

-- Therefore `not member of Good` cannot be used as a proof of membership in
-- the semantic inverse class: the same Boolean output is inhabited by the
-- exterior/non-classified state.

------------------------------------------------------------------------
-- The zero coordinate remains compact while its fibre records why it is zero.
------------------------------------------------------------------------

data ZeroKind : Set where
  zeroUnknown
  zeroUnclassified
  zeroBalanced
  zeroIncomparable
  zeroOpen
  zeroExpired
  zeroCompletedNeutral : ZeroKind

record FibredOrientation : Set where
  constructor fibredOrientation
  field
    sign : TriTruth
    zeroKind : ZeroKind

open FibredOrientation public

outsideOrientation : FibredOrientation
outsideOrientation = fibredOrientation tri-mid zeroUnclassified

openOrientation : FibredOrientation
openOrientation = fibredOrientation tri-mid zeroOpen

inverseOrientation : FibredOrientation
inverseOrientation = fibredOrientation tri-low zeroBalanced

goodOrientation : FibredOrientation
goodOrientation = fibredOrientation tri-high zeroBalanced

------------------------------------------------------------------------
-- Declared and realised positivity are independent coordinates.
------------------------------------------------------------------------

record NominalActual (A : Set) : Set where
  constructor nominalActual
  field
    nominal : A
    actual : A

open NominalActual public

politicalSolutionDeclaredButOpen : NominalActual SignedMembership
politicalSolutionDeclaredButOpen =
  nominalActual memberOfGood notMemberOfEither

politicalSolutionDeclaredButAdverse : NominalActual SignedMembership
politicalSolutionDeclaredButAdverse =
  nominalActual memberOfGood memberOfInverse

politicalSolutionAligned : NominalActual SignedMembership
politicalSolutionAligned =
  nominalActual memberOfGood memberOfGood
