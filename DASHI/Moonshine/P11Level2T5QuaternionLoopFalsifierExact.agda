module DASHI.Moonshine.P11Level2T5QuaternionLoopFalsifierExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
-- Chapter 42, "Supersingular elliptic curves",
-- DOI: 10.1007/978-3-030-56694-4_42.
-- Example 42.3.11 identifies, at p=11,
--
--   B = (-1,-11 / Q),
--   O = Z<i,(1+j)/2>,
--
-- with End(E) ~= O for the supersingular j(E)=1728 class.  The same chapter
-- uses the Deuring correspondence between endomorphisms and quaternionic norm.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Annals of Mathematics Studies 108,
-- Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
-- Prime-to-level isogenies transport full level structures.
--
-- DASHI CONTRIBUTION
--
-- Exhibit the explicit endomorphism-order element
--
--   alpha = 1 + 2 i in O.
--
-- In B=(-1,-11), Nrd(a+bi+cj+dk)=a^2+b^2+11c^2+11d^2, so
--
--   Nrd(1+2i)=1+4=5.
--
-- Moreover alpha-1=2i lies in 2O, hence alpha is the identity modulo 2O.  Via
-- the standard Deuring / prime-to-level bridge, this is exactly the arithmetic
-- signature of a degree-5 self-isogeny fixing a chosen full level-2 frame.
--
-- The hand-constructed positive R5 on Fine5 has ZERO diagonal at every B sheet.
-- Therefore that R5 cannot be the actual full-level-2 T5 correspondence.
--
-- This is a falsifier of the EDGE DISTRIBUTION, not of the five-state carrier:
-- the carrier, stack multiplicities, Legendre chart and deck S3 remain intact.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11FullLevel2DeckHeckeEquivarianceExact as Deck
import DASHI.Moonshine.P11Level2DoubleCosetHeckeBasisExact as DoubleCoset

------------------------------------------------------------------------
-- Explicit integral quaternion coordinates in B=(-1,-11).
------------------------------------------------------------------------

record P11QuaternionCoordinates : Set where
  constructor quaternion11
  field
    scalar iCoeff jCoeff kCoeff : Nat

open P11QuaternionCoordinates public

-- Positive-coordinate norm suffices for the explicit witness used here.
reducedNormPositive : P11QuaternionCoordinates → Nat
reducedNormPositive q =
  scalar q * scalar q
  + iCoeff q * iCoeff q
  + 11 * (jCoeff q * jCoeff q)
  + 11 * (kCoeff q * kCoeff q)

onePlusTwoI : P11QuaternionCoordinates
onePlusTwoI = quaternion11 1 2 0 0

onePlusTwoINormIsFive : reducedNormPositive onePlusTwoI ≡ 5
onePlusTwoINormIsFive = refl

------------------------------------------------------------------------
-- Membership / level-2 congruence witnesses.
--
-- O=Z<i,(1+j)/2> contains 1 and i, hence 1+2i is integral.  The difference
-- from 1 is literally twice the order element i.
------------------------------------------------------------------------

data J1728OrderGenerator : Set where
  orderOne orderI orderHalfOnePlusJ orderIHalfOnePlusJ : J1728OrderGenerator

record Level2IdentityCongruenceWitness : Set where
  constructor level2IdentityCongruence
  field
    quotientICoefficient : Nat
    twiceQuotientICoefficient : 2 * quotientICoefficient ≡ iCoeff onePlusTwoI

onePlusTwoIIsIdentityMod2 : Level2IdentityCongruenceWitness
onePlusTwoIIsIdentityMod2 = level2IdentityCongruence 1 refl

------------------------------------------------------------------------
-- Arithmetic marked-loop signature.
--
-- Source interpretation: for p != ell, prime reduced norm ell is the isogeny
-- degree, and alpha == 1 mod 2End(E) means the induced map on E[2] is the
-- identity.  We encode the arithmetic side exactly and keep the geometric
-- interpretation classified separately below.
------------------------------------------------------------------------

record ArithmeticMarkedPrimeLoop : Set where
  constructor arithmeticMarkedPrimeLoop
  field
    primeDegree : Nat
    element : P11QuaternionCoordinates
    normExact : reducedNormPositive element ≡ primeDegree
    level2Identity : Level2IdentityCongruenceWitness

j1728ArithmeticMarkedT5Loop : ArithmeticMarkedPrimeLoop
j1728ArithmeticMarkedT5Loop =
  arithmeticMarkedPrimeLoop 5 onePlusTwoI onePlusTwoINormIsFive onePlusTwoIIsIdentityMod2

------------------------------------------------------------------------
-- Existing candidate R5 has zero identity-double-coset coefficient.
------------------------------------------------------------------------

candidateR5J1728FineLoopMultiplicity : Nat
candidateR5J1728FineLoopMultiplicity =
  Deck.edgeMultiplicity Fine.R5Positive Fine.b0 Fine.b0

candidateR5J1728FineLoopMultiplicityIsZero :
  candidateR5J1728FineLoopMultiplicity ≡ 0
candidateR5J1728FineLoopMultiplicityIsZero = refl

candidateR5IdentityOrbitalCoefficientIsZero :
  DoubleCoset.bbId DoubleCoset.r5OrbitalCoefficients ≡ 0
candidateR5IdentityOrbitalCoefficientIsZero = refl

------------------------------------------------------------------------
-- The exact contradiction is conditional only on the standard source bridge
-- from quaternion arithmetic to marked-isogeny semantics.
------------------------------------------------------------------------

record DeuringLevel2Bridge : Set where
  field
    arithmeticMarkedLoopImpliesPositiveFineLoop :
      ArithmeticMarkedPrimeLoop → Nat
    j1728T5LoopIsPositive :
      1 ≤ arithmeticMarkedLoopImpliesPositiveFineLoop j1728ArithmeticMarkedT5Loop

open DeuringLevel2Bridge public

looplessCandidateCannotEqualSourceT5 :
  (bridge : DeuringLevel2Bridge) →
  arithmeticMarkedLoopImpliesPositiveFineLoop bridge j1728ArithmeticMarkedT5Loop
  ≡ candidateR5J1728FineLoopMultiplicity →
  ⊥
looplessCandidateCannotEqualSourceT5 bridge same
  rewrite candidateR5J1728FineLoopMultiplicityIsZero in
  case (j1728T5LoopIsPositive bridge) of λ ()
  where
    case : ∀ {A B : Set} → A → (A → B) → B
    case x f = f x

------------------------------------------------------------------------
-- Boundary / status.
------------------------------------------------------------------------

record P11Level2T5QuaternionLoopBoundary : Set where
  field
    explicitNormFiveOrderElementConstructed : Bool
    explicitNormFiveOrderElementConstructedIsTrue :
      explicitNormFiveOrderElementConstructed ≡ true

    identityModuloTwoOrderWitnessConstructed : Bool
    identityModuloTwoOrderWitnessConstructedIsTrue :
      identityModuloTwoOrderWitnessConstructed ≡ true

    currentR5IdentityOrbitalIsZero : Bool
    currentR5IdentityOrbitalIsZeroIsTrue : currentR5IdentityOrbitalIsZero ≡ true

    looplessR5PromotedToGeometricT5 : Bool
    looplessR5PromotedToGeometricT5IsFalse : looplessR5PromotedToGeometricT5 ≡ false

    deuringNormDegreeBridgeReprovedInternally : Bool
    deuringNormDegreeBridgeReprovedInternallyIsFalse :
      deuringNormDegreeBridgeReprovedInternally ≡ false

canonicalP11Level2T5QuaternionLoopBoundary : P11Level2T5QuaternionLoopBoundary
canonicalP11Level2T5QuaternionLoopBoundary =
  record
    { explicitNormFiveOrderElementConstructed = true
    ; explicitNormFiveOrderElementConstructedIsTrue = refl
    ; identityModuloTwoOrderWitnessConstructed = true
    ; identityModuloTwoOrderWitnessConstructedIsTrue = refl
    ; currentR5IdentityOrbitalIsZero = true
    ; currentR5IdentityOrbitalIsZeroIsTrue = refl
    ; looplessR5PromotedToGeometricT5 = false
    ; looplessR5PromotedToGeometricT5IsFalse = refl
    ; deuringNormDegreeBridgeReprovedInternally = false
    ; deuringNormDegreeBridgeReprovedInternallyIsFalse = refl
    }
