module DASHI.Mathematics.Arithmetic.EllipticFiniteSeedToSelmerExact where

------------------------------------------------------------------------
-- BSD ARITHMETIC ROAD: FINITE 2-TORSION KUMMER SEED -> SELMER ELEMENT
--
-- The finite seed already gives an exact Kummer image C2 x C2 for
-- y^2 = x^3 - x.  This compiler states the precise global/local evidence
-- required to promote one such finite seed value to a genuine Selmer element.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Mathematics.Arithmetic.EllipticCurveFiniteTwoDescentSeedExact as Seed
import DASHI.Mathematics.Arithmetic.EllipticCurveTwoTorsionAndBadPrimeExact as Torsion
import DASHI.Mathematics.Arithmetic.EllipticCurveFrobeniusExact as Elliptic
import DASHI.Mathematics.Arithmetic.EllipticTwoDescentRoadExact as Descent

record FiniteSeedGlobalRealization
    (carrier :
      Descent.GlobalLocalTwoDescentCarrier
        Elliptic.curveY2EqualsX3MinusX) : Set₁ where
  field
    realize :
      Seed.SquareClassPair →
      Descent.GlobalCohomology carrier

    finiteImageLandsInGlobalKummer :
      (pair : Seed.SquareClassPair) →
      Descent.GlobalKummerImage carrier (realize pair)

    finiteImageSatisfiesEveryLocalCondition :
      (pair : Seed.SquareClassPair) →
      (place : Descent.Place carrier) →
      Descent.LocalKummerImage carrier place
        (Descent.localize carrier place (realize pair))

open FiniteSeedGlobalRealization public

finiteSeedPairToSelmer :
  ∀ {carrier} →
  FiniteSeedGlobalRealization carrier →
  Seed.SquareClassPair →
  Descent.SelmerTwoElement carrier
finiteSeedPairToSelmer realization pair = record
  { Descent.cohomologyClass = realize realization pair
  ; Descent.satisfiesEveryLocalCondition =
      finiteImageSatisfiesEveryLocalCondition realization pair
  }

finiteKummerPointToSelmer :
  ∀ {carrier} →
  FiniteSeedGlobalRealization carrier →
  Torsion.TwoTorsionCode →
  Descent.SelmerTwoElement carrier
finiteKummerPointToSelmer realization point =
  finiteSeedPairToSelmer realization (Seed.finiteKummerMap point)

finiteSeedInfinityToSelmer :
  ∀ {carrier} →
  FiniteSeedGlobalRealization carrier →
  Descent.SelmerTwoElement carrier
finiteSeedInfinityToSelmer realization =
  finiteKummerPointToSelmer realization Torsion.pointAtInfinityCode

record EllipticFiniteSeedToSelmerBoundary : Set where
  constructor elliptic-finite-seed-to-selmer-boundary
  field
    finiteKummerSeedPaid : Bool
    finiteSeedToSelmerCompilerPaid : Bool
    distinguishedInfinitySeedCompilerPaid : Bool
    rationalSquareClassRealizationPaid : Bool
    localKummerRealizationPaid : Bool
    actualGlobalSelmerInhabitantPaid : Bool
    shaTwoExactnessPaid : Bool
    bsdRankEqualityPaid : Bool

canonicalEllipticFiniteSeedToSelmerBoundary :
  EllipticFiniteSeedToSelmerBoundary
canonicalEllipticFiniteSeedToSelmerBoundary =
  elliptic-finite-seed-to-selmer-boundary
    true true true false false false false false
