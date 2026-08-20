module DASHI.Moonshine.P11Level2DoubleCosetHeckeBasisExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Annals of Mathematics Studies 108,
-- Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
-- Full level structures and prime-to-level isogeny correspondences.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
-- Hecke correspondences / modular-curve context.
--
-- Chris Godsil and Gordon Royle,
-- "Algebraic Graph Theory", Graduate Texts in Mathematics 207,
-- Springer, 2001.
-- DOI: 10.1007/978-1-4613-0163-9.
-- Orbitals and invariant adjacency algebras for permutation actions.
--
-- DASHI CONTRIBUTION
--
-- Identify the six-parameter deck-invariant normal form with the actual finite
-- double-coset/orbital basis of the level-2 deck S3 action on
--
--   C3\S3  disjoint-union  C2\S3.
--
-- There are exactly:
--
--   AA identity / AA nonidentity,
--   one A->B orbital,
--   one B->A orbital,
--   BB identity / BB nonidentity.
--
-- In this basis the existing positive odd-prime operators have coefficients
--
--   R3 : (0,1,1,1,0,1),
--   R5 : (0,3,1,1,0,2).
--
-- Thus the unresolved arithmetic producer is reduced to proving that the
-- actual norm-3 and norm-5 prime-to-level cyclic-isogeny correspondences have
-- zero coefficient on the two identity double cosets.  Coarse Brandt row sums
-- then force every nonidentity coefficient.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11FullLevel2DeckHeckeEquivarianceExact as Deck
import DASHI.Moonshine.P11Level2DeckHeckeRigidityExact as Rigidity

------------------------------------------------------------------------
-- Orbitals of the diagonal deck-S3 action on ordered pairs of fine points.
------------------------------------------------------------------------

data Level2HeckeOrbital : Set where
  aaIdentity aaNonidentity : Level2HeckeOrbital
  abUnique baUnique : Level2HeckeOrbital
  bbIdentity bbNonidentity : Level2HeckeOrbital

orbitalOf : Fine.P11Fine5 → Fine.P11Fine5 → Level2HeckeOrbital
orbitalOf Fine.a0 Fine.a0 = aaIdentity
orbitalOf Fine.a1 Fine.a1 = aaIdentity
orbitalOf Fine.a0 Fine.a1 = aaNonidentity
orbitalOf Fine.a1 Fine.a0 = aaNonidentity
orbitalOf Fine.a0 Fine.b0 = abUnique
orbitalOf Fine.a0 Fine.b1 = abUnique
orbitalOf Fine.a0 Fine.b2 = abUnique
orbitalOf Fine.a1 Fine.b0 = abUnique
orbitalOf Fine.a1 Fine.b1 = abUnique
orbitalOf Fine.a1 Fine.b2 = abUnique
orbitalOf Fine.b0 Fine.a0 = baUnique
orbitalOf Fine.b0 Fine.a1 = baUnique
orbitalOf Fine.b1 Fine.a0 = baUnique
orbitalOf Fine.b1 Fine.a1 = baUnique
orbitalOf Fine.b2 Fine.a0 = baUnique
orbitalOf Fine.b2 Fine.a1 = baUnique
orbitalOf Fine.b0 Fine.b0 = bbIdentity
orbitalOf Fine.b1 Fine.b1 = bbIdentity
orbitalOf Fine.b2 Fine.b2 = bbIdentity
orbitalOf Fine.b0 Fine.b1 = bbNonidentity
orbitalOf Fine.b0 Fine.b2 = bbNonidentity
orbitalOf Fine.b1 Fine.b0 = bbNonidentity
orbitalOf Fine.b1 Fine.b2 = bbNonidentity
orbitalOf Fine.b2 Fine.b0 = bbNonidentity
orbitalOf Fine.b2 Fine.b1 = bbNonidentity

------------------------------------------------------------------------
-- The orbital label is invariant under both deck generators.
------------------------------------------------------------------------

orbitalDeckRInvariant :
  (x y : Fine.P11Fine5) →
  orbitalOf (Deck.deckR x) (Deck.deckR y) ≡ orbitalOf x y
orbitalDeckRInvariant Fine.a0 Fine.a0 = refl
orbitalDeckRInvariant Fine.a0 Fine.a1 = refl
orbitalDeckRInvariant Fine.a0 Fine.b0 = refl
orbitalDeckRInvariant Fine.a0 Fine.b1 = refl
orbitalDeckRInvariant Fine.a0 Fine.b2 = refl
orbitalDeckRInvariant Fine.a1 Fine.a0 = refl
orbitalDeckRInvariant Fine.a1 Fine.a1 = refl
orbitalDeckRInvariant Fine.a1 Fine.b0 = refl
orbitalDeckRInvariant Fine.a1 Fine.b1 = refl
orbitalDeckRInvariant Fine.a1 Fine.b2 = refl
orbitalDeckRInvariant Fine.b0 Fine.a0 = refl
orbitalDeckRInvariant Fine.b0 Fine.a1 = refl
orbitalDeckRInvariant Fine.b0 Fine.b0 = refl
orbitalDeckRInvariant Fine.b0 Fine.b1 = refl
orbitalDeckRInvariant Fine.b0 Fine.b2 = refl
orbitalDeckRInvariant Fine.b1 Fine.a0 = refl
orbitalDeckRInvariant Fine.b1 Fine.a1 = refl
orbitalDeckRInvariant Fine.b1 Fine.b0 = refl
orbitalDeckRInvariant Fine.b1 Fine.b1 = refl
orbitalDeckRInvariant Fine.b1 Fine.b2 = refl
orbitalDeckRInvariant Fine.b2 Fine.a0 = refl
orbitalDeckRInvariant Fine.b2 Fine.a1 = refl
orbitalDeckRInvariant Fine.b2 Fine.b0 = refl
orbitalDeckRInvariant Fine.b2 Fine.b1 = refl
orbitalDeckRInvariant Fine.b2 Fine.b2 = refl

orbitalDeckSInvariant :
  (x y : Fine.P11Fine5) →
  orbitalOf (Deck.deckS x) (Deck.deckS y) ≡ orbitalOf x y
orbitalDeckSInvariant Fine.a0 Fine.a0 = refl
orbitalDeckSInvariant Fine.a0 Fine.a1 = refl
orbitalDeckSInvariant Fine.a0 Fine.b0 = refl
orbitalDeckSInvariant Fine.a0 Fine.b1 = refl
orbitalDeckSInvariant Fine.a0 Fine.b2 = refl
orbitalDeckSInvariant Fine.a1 Fine.a0 = refl
orbitalDeckSInvariant Fine.a1 Fine.a1 = refl
orbitalDeckSInvariant Fine.a1 Fine.b0 = refl
orbitalDeckSInvariant Fine.a1 Fine.b1 = refl
orbitalDeckSInvariant Fine.a1 Fine.b2 = refl
orbitalDeckSInvariant Fine.b0 Fine.a0 = refl
orbitalDeckSInvariant Fine.b0 Fine.a1 = refl
orbitalDeckSInvariant Fine.b0 Fine.b0 = refl
orbitalDeckSInvariant Fine.b0 Fine.b1 = refl
orbitalDeckSInvariant Fine.b0 Fine.b2 = refl
orbitalDeckSInvariant Fine.b1 Fine.a0 = refl
orbitalDeckSInvariant Fine.b1 Fine.a1 = refl
orbitalDeckSInvariant Fine.b1 Fine.b0 = refl
orbitalDeckSInvariant Fine.b1 Fine.b1 = refl
orbitalDeckSInvariant Fine.b1 Fine.b2 = refl
orbitalDeckSInvariant Fine.b2 Fine.a0 = refl
orbitalDeckSInvariant Fine.b2 Fine.a1 = refl
orbitalDeckSInvariant Fine.b2 Fine.b0 = refl
orbitalDeckSInvariant Fine.b2 Fine.b1 = refl
orbitalDeckSInvariant Fine.b2 Fine.b2 = refl

------------------------------------------------------------------------
-- Coefficient functions on the orbital basis.
------------------------------------------------------------------------

record OrbitalCoefficients : Set where
  constructor orbitalCoefficients
  field
    aaId aaOff ab ba bbId bbOff : Nat

open OrbitalCoefficients public

coefficientAt : OrbitalCoefficients → Level2HeckeOrbital → Nat
coefficientAt C aaIdentity = aaId C
coefficientAt C aaNonidentity = aaOff C
coefficientAt C abUnique = ab C
coefficientAt C baUnique = ba C
coefficientAt C bbIdentity = bbId C
coefficientAt C bbNonidentity = bbOff C

orbitalMultiplicity :
  OrbitalCoefficients → Fine.P11Fine5 → Fine.P11Fine5 → Nat
orbitalMultiplicity C x y = coefficientAt C (orbitalOf x y)

r3OrbitalCoefficients : OrbitalCoefficients
r3OrbitalCoefficients = orbitalCoefficients 0 1 1 1 0 1

r5OrbitalCoefficients : OrbitalCoefficients
r5OrbitalCoefficients = orbitalCoefficients 0 3 1 1 0 2

r3OrbitalNormalFormIsExisting :
  (x y : Fine.P11Fine5) →
  orbitalMultiplicity r3OrbitalCoefficients x y
  ≡ Deck.edgeMultiplicity Fine.R3Positive x y
r3OrbitalNormalFormIsExisting Fine.a0 Fine.a0 = refl
r3OrbitalNormalFormIsExisting Fine.a0 Fine.a1 = refl
r3OrbitalNormalFormIsExisting Fine.a0 Fine.b0 = refl
r3OrbitalNormalFormIsExisting Fine.a0 Fine.b1 = refl
r3OrbitalNormalFormIsExisting Fine.a0 Fine.b2 = refl
r3OrbitalNormalFormIsExisting Fine.a1 Fine.a0 = refl
r3OrbitalNormalFormIsExisting Fine.a1 Fine.a1 = refl
r3OrbitalNormalFormIsExisting Fine.a1 Fine.b0 = refl
r3OrbitalNormalFormIsExisting Fine.a1 Fine.b1 = refl
r3OrbitalNormalFormIsExisting Fine.a1 Fine.b2 = refl
r3OrbitalNormalFormIsExisting Fine.b0 Fine.a0 = refl
r3OrbitalNormalFormIsExisting Fine.b0 Fine.a1 = refl
r3OrbitalNormalFormIsExisting Fine.b0 Fine.b0 = refl
r3OrbitalNormalFormIsExisting Fine.b0 Fine.b1 = refl
r3OrbitalNormalFormIsExisting Fine.b0 Fine.b2 = refl
r3OrbitalNormalFormIsExisting Fine.b1 Fine.a0 = refl
r3OrbitalNormalFormIsExisting Fine.b1 Fine.a1 = refl
r3OrbitalNormalFormIsExisting Fine.b1 Fine.b0 = refl
r3OrbitalNormalFormIsExisting Fine.b1 Fine.b1 = refl
r3OrbitalNormalFormIsExisting Fine.b1 Fine.b2 = refl
r3OrbitalNormalFormIsExisting Fine.b2 Fine.a0 = refl
r3OrbitalNormalFormIsExisting Fine.b2 Fine.a1 = refl
r3OrbitalNormalFormIsExisting Fine.b2 Fine.b0 = refl
r3OrbitalNormalFormIsExisting Fine.b2 Fine.b1 = refl
r3OrbitalNormalFormIsExisting Fine.b2 Fine.b2 = refl

r5OrbitalNormalFormIsExisting :
  (x y : Fine.P11Fine5) →
  orbitalMultiplicity r5OrbitalCoefficients x y
  ≡ Deck.edgeMultiplicity Fine.R5Positive x y
r5OrbitalNormalFormIsExisting Fine.a0 Fine.a0 = refl
r5OrbitalNormalFormIsExisting Fine.a0 Fine.a1 = refl
r5OrbitalNormalFormIsExisting Fine.a0 Fine.b0 = refl
r5OrbitalNormalFormIsExisting Fine.a0 Fine.b1 = refl
r5OrbitalNormalFormIsExisting Fine.a0 Fine.b2 = refl
r5OrbitalNormalFormIsExisting Fine.a1 Fine.a0 = refl
r5OrbitalNormalFormIsExisting Fine.a1 Fine.a1 = refl
r5OrbitalNormalFormIsExisting Fine.a1 Fine.b0 = refl
r5OrbitalNormalFormIsExisting Fine.a1 Fine.b1 = refl
r5OrbitalNormalFormIsExisting Fine.a1 Fine.b2 = refl
r5OrbitalNormalFormIsExisting Fine.b0 Fine.a0 = refl
r5OrbitalNormalFormIsExisting Fine.b0 Fine.a1 = refl
r5OrbitalNormalFormIsExisting Fine.b0 Fine.b0 = refl
r5OrbitalNormalFormIsExisting Fine.b0 Fine.b1 = refl
r5OrbitalNormalFormIsExisting Fine.b0 Fine.b2 = refl
r5OrbitalNormalFormIsExisting Fine.b1 Fine.a0 = refl
r5OrbitalNormalFormIsExisting Fine.b1 Fine.a1 = refl
r5OrbitalNormalFormIsExisting Fine.b1 Fine.b0 = refl
r5OrbitalNormalFormIsExisting Fine.b1 Fine.b1 = refl
r5OrbitalNormalFormIsExisting Fine.b1 Fine.b2 = refl
r5OrbitalNormalFormIsExisting Fine.b2 Fine.a0 = refl
r5OrbitalNormalFormIsExisting Fine.b2 Fine.a1 = refl
r5OrbitalNormalFormIsExisting Fine.b2 Fine.b0 = refl
r5OrbitalNormalFormIsExisting Fine.b2 Fine.b1 = refl
r5OrbitalNormalFormIsExisting Fine.b2 Fine.b2 = refl

------------------------------------------------------------------------
-- Bridge to the earlier six-parameter rigidity normal form.
------------------------------------------------------------------------

toRigidityNormalForm :
  OrbitalCoefficients → Rigidity.DeckInvariantSixParameterCorrespondence
toRigidityNormalForm C =
  Rigidity.deckInvariant6
    (aaId C) (aaOff C) (ab C) (ba C) (bbId C) (bbOff C)

r3IdentityOrbitalCoefficientsZero :
  aaId r3OrbitalCoefficients ≡ 0 × bbId r3OrbitalCoefficients ≡ 0
r3IdentityOrbitalCoefficientsZero = refl , refl

r5IdentityOrbitalCoefficientsZero :
  aaId r5OrbitalCoefficients ≡ 0 × bbId r5OrbitalCoefficients ≡ 0
r5IdentityOrbitalCoefficientsZero = refl , refl

record P11Level2DoubleCosetBoundary : Set where
  field
    sixDeckOrbitalsConstructed : Bool
    sixDeckOrbitalsConstructedIsTrue : sixDeckOrbitalsConstructed ≡ true

    existingR3R5ExpressedInOrbitalBasis : Bool
    existingR3R5ExpressedInOrbitalBasisIsTrue :
      existingR3R5ExpressedInOrbitalBasis ≡ true

    crossFiberOrbitalUnique : Bool
    crossFiberOrbitalUniqueIsTrue : crossFiberOrbitalUnique ≡ true

    remainingArithmeticUnknownIsIdentityOrbitalCount : Bool
    remainingArithmeticUnknownIsIdentityOrbitalCountIsTrue :
      remainingArithmeticUnknownIsIdentityOrbitalCount ≡ true

    identityOrbitalVanishingDerivedFromQuaternionArithmeticHere : Bool
    identityOrbitalVanishingDerivedFromQuaternionArithmeticHereIsFalse :
      identityOrbitalVanishingDerivedFromQuaternionArithmeticHere ≡ false

canonicalP11Level2DoubleCosetBoundary : P11Level2DoubleCosetBoundary
canonicalP11Level2DoubleCosetBoundary =
  record
    { sixDeckOrbitalsConstructed = true
    ; sixDeckOrbitalsConstructedIsTrue = refl
    ; existingR3R5ExpressedInOrbitalBasis = true
    ; existingR3R5ExpressedInOrbitalBasisIsTrue = refl
    ; crossFiberOrbitalUnique = true
    ; crossFiberOrbitalUniqueIsTrue = refl
    ; remainingArithmeticUnknownIsIdentityOrbitalCount = true
    ; remainingArithmeticUnknownIsIdentityOrbitalCountIsTrue = refl
    ; identityOrbitalVanishingDerivedFromQuaternionArithmeticHere = false
    ; identityOrbitalVanishingDerivedFromQuaternionArithmeticHereIsFalse = refl
    }
