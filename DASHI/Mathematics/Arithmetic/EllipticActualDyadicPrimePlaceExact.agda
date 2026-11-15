module DASHI.Mathematics.Arithmetic.EllipticActualDyadicPrimePlaceExact where

------------------------------------------------------------------------
-- K1: ACTUAL PRIME-2 PLACE FOR ORIGINAL AGDA ALL-PLACE SELMER.
--
-- The original RationalPlaceTwoDescentData carrier has genuine finite
-- prime labels, with proof of irreducibility. We instantiate that
-- ORIGINAL label at the actual integer 2 using the PINNED Agda
-- standard-library prime[2] theorem. No dummy local place or
-- "label=2" axiom is needed.
--
-- This module also extracts the original prime-two Kummer membership
-- of any original all-place Selmer element from its proof field.
-- The field is still an abstract local Kummer image predicate until
-- actual Q₂ point/cohomology objects are supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat.Base using (z≤n; s≤s)
import Data.Nat.Properties as NatProperties
import Data.Nat.Divisibility as Divisibility
import Data.Nat.Primality as NatPrimality
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Arithmetic.EllipticCurveFrobeniusExact as Elliptic
import DASHI.Mathematics.Arithmetic.EllipticTwoDescentRoadExact as Descent
import DASHI.Mathematics.Arithmetic.EllipticRationalPlaceSelmerExact as Place

actualTwoIsPrimeNat : Place.PrimeNat 2
actualTwoIsPrimeNat = record
  { Place.atLeastTwo = s≤s (s≤s z≤n)
  ; Place.onlyTrivialDivisors = λ divisor →
      λ where
        (quotient , divisorTimesQuotient) →
          NatPrimality.prime⇒irreducible
            NatPrimality.prime[2]
            (Divisibility.divides quotient
              (trans
                (sym divisorTimesQuotient)
                (NatProperties.*-comm divisor quotient)))
  }

actualDyadicFinitePrime : Place.FinitePrime
actualDyadicFinitePrime =
  Place.finite-prime 2 actualTwoIsPrimeNat

actualDyadicPrimeLabel :
  Place.primeValue actualDyadicFinitePrime ≡ 2
actualDyadicPrimeLabel = refl

actualDyadicRationalPlace : Place.RationalPlace
actualDyadicRationalPlace =
  Place.finitePlace actualDyadicFinitePrime

-- Membership on the literal canonical p=2 place follows from the
-- ALREADY-EXISTING SelmerTwoElement proof, with no fresh assumption.
actualDyadicLocalConditionFromSelmer :
  ∀ (data : Place.RationalPlaceTwoDescentData
      Elliptic.curveY2EqualsX3MinusX)
    (s : Descent.SelmerTwoElement (Place.rationalPlaceCarrier data)) →
  Place.FiniteKummerImage data actualDyadicFinitePrime
    (Place.localizeFinite data actualDyadicFinitePrime
      (Descent.cohomologyClass s))
actualDyadicLocalConditionFromSelmer data s =
  Descent.satisfiesEveryLocalCondition s actualDyadicRationalPlace
