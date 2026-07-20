module DASHI.Physics.Closure.TriadicConcreteAnalyticInstances where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Integer using (+_)
open import Data.List.Base using ([]; _∷_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope as Env
import DASHI.Physics.Closure.TriadicAnalyticCertificates as Certificates
import DASHI.Foundations.TriadicFiniteQuotient as Quotient

------------------------------------------------------------------------
-- Concrete quarter-scale rational approximants.
--
-- A stream d is represented by the nested rational intervals centred at
--
--   s_n(d) = Σ_{k<n} d_k 4^{-k}
--
-- with radius (4/3)4^{-n}.  The exact one-step budget identity below is the
-- constructive Cauchy argument; the first-difference identity is the strict
-- separation margin supplied by λ=1/4<1/3.

quarter : ℚ
quarter = + 1 / 4

oneThird : ℚ
oneThird = + 1 / 3

fourThirds : ℚ
fourThirds = + 4 / 3

two : ℚ
two = + 2 / 1

four : ℚ
four = + 4 / 1

quarterPower : Nat → ℚ
quarterPower zero = 1ℚ
quarterPower (suc n) = quarterPower n * quarter

quarterPowerStep :
  (n : Nat) → quarterPower (suc n) ≡ quarterPower n * quarter
quarterPowerStep n = refl

tritRational : Env.Trit → ℚ
tritRational Env.neg = - 1ℚ
tritRational Env.zer = 0ℚ
tritRational Env.pos = 1ℚ

quarterPartialSum : Nat → Env.Stream → ℚ
quarterPartialSum zero d = 0ℚ
quarterPartialSum (suc n) d =
  quarterPartialSum n d + tritRational (d n) * quarterPower n

quarterTailRadius : Nat → ℚ
quarterTailRadius n = fourThirds * quarterPower n

quarterSeparationMargin : Nat → ℚ
quarterSeparationMargin n = oneThird * quarterPower n

nextTailBudgetIdentity :
  (n : Nat) →
  quarterPower n + quarterTailRadius (suc n)
  ≡ quarterTailRadius n
nextTailBudgetIdentity n
  rewrite quarterPowerStep n =
  solve (quarterPower n ∷ [])

radiusQuarterStep :
  (n : Nat) →
  four * quarterTailRadius (suc n) ≡ quarterTailRadius n
radiusQuarterStep n
  rewrite quarterPowerStep n =
  solve (quarterPower n ∷ [])

firstDifferenceBudgetIdentity :
  (n : Nat) →
  two * quarterTailRadius (suc n) + quarterSeparationMargin n
  ≡ quarterPower n
firstDifferenceBudgetIdentity n
  rewrite quarterPowerStep n =
  solve (quarterPower n ∷ [])

record QuarterRealCode : Set where
  constructor quarter-real-code
  field
    source : Env.Stream
    center : Nat → ℚ
    centerExact :
      (n : Nat) → center n ≡ quarterPartialSum n source
    radius : Nat → ℚ
    radiusExact :
      (n : Nat) → radius n ≡ quarterTailRadius n
    nestedBudgetExact :
      (n : Nat) → quarterPower n + radius (suc n) ≡ radius n
    radiusScalesByQuarter :
      (n : Nat) → four * radius (suc n) ≡ radius n
    separationBudgetExact :
      (n : Nat) →
      two * radius (suc n) + quarterSeparationMargin n
      ≡ quarterPower n

open QuarterRealCode public

quarterReal : Env.Stream → QuarterRealCode
quarterReal d =
  quarter-real-code
    d
    (λ n → quarterPartialSum n d)
    (λ n → refl)
    quarterTailRadius
    (λ n → refl)
    nextTailBudgetIdentity
    radiusQuarterStep
    firstDifferenceBudgetIdentity

record ConcreteQuarterRealAnalyticInstance : Set₁ where
  field
    ScalarApproximation : Set
    scalarApproximationIsRational : ScalarApproximation ≡ ℚ
    embed : Env.Stream → QuarterRealCode
    contractionScale : ℚ
    scaleIsQuarter : contractionScale ≡ quarter
    exactGeometricTail :
      (n : Nat) →
      quarterPower n + quarterTailRadius (suc n)
      ≡ quarterTailRadius n
    exactRadiusContraction :
      (n : Nat) →
      four * quarterTailRadius (suc n) ≡ quarterTailRadius n
    exactFirstDifferenceMargin :
      (n : Nat) →
      two * quarterTailRadius (suc n) + quarterSeparationMargin n
      ≡ quarterPower n

open ConcreteQuarterRealAnalyticInstance public

concreteQuarterRealAnalyticInstance :
  ConcreteQuarterRealAnalyticInstance
concreteQuarterRealAnalyticInstance =
  record
    { ScalarApproximation = ℚ
    ; scalarApproximationIsRational = refl
    ; embed = quarterReal
    ; contractionScale = quarter
    ; scaleIsQuarter = refl
    ; exactGeometricTail = nextTailBudgetIdentity
    ; exactRadiusContraction = radiusQuarterStep
    ; exactFirstDifferenceMargin = firstDifferenceBudgetIdentity
    }

------------------------------------------------------------------------
-- Native 3-adic global chart.
--
-- The carrier is the already-checked inverse limit of Z/3^nZ.  The global
-- chart is the identity embedding into a distinguished Q3 ambient code.  A
-- one-chart atlas has identity transition map, hence its transition theorem is
-- definitional; compatibility with every finite quotient is the inverse-limit
-- compatibility proof itself.

data GlobalTriadicChart : Set where
  globalTriadicChart : GlobalTriadicChart

data Q3AmbientCode : Set where
  embeddedInteger : Quotient.TriadicInverseLimitPoint → Q3AmbientCode

chartMap :
  GlobalTriadicChart →
  Quotient.TriadicInverseLimitPoint →
  Q3AmbientCode
chartMap globalTriadicChart point = embeddedInteger point

chartTransition :
  GlobalTriadicChart →
  GlobalTriadicChart →
  Q3AmbientCode →
  Q3AmbientCode
chartTransition globalTriadicChart globalTriadicChart value = value

chartTransitionIdentity :
  (value : Q3AmbientCode) →
  chartTransition globalTriadicChart globalTriadicChart value ≡ value
chartTransitionIdentity value = refl

record ConcretePAdicAtlasReceipt : Set₁ where
  field
    coordinateMap :
      GlobalTriadicChart →
      Quotient.TriadicInverseLimitPoint →
      Q3AmbientCode
    transitionMap :
      GlobalTriadicChart →
      GlobalTriadicChart →
      Q3AmbientCode →
      Q3AmbientCode
    transitionIsIdentity :
      (value : Q3AmbientCode) →
      transitionMap globalTriadicChart globalTriadicChart value ≡ value
    finiteCoordinate :
      Quotient.TriadicInverseLimitPoint →
      (n : Nat) →
      Quotient.Residue3Pow n
    finiteCoordinatesCompatible :
      (point : Quotient.TriadicInverseLimitPoint) →
      (n : Nat) →
      Quotient.reduce (finiteCoordinate point (suc n))
      ≡ finiteCoordinate point n

open ConcretePAdicAtlasReceipt public

concretePAdicAtlas : ConcretePAdicAtlasReceipt
concretePAdicAtlas =
  record
    { coordinateMap = chartMap
    ; transitionMap = chartTransition
    ; transitionIsIdentity = chartTransitionIdentity
    ; finiteCoordinate = Quotient.coordinate
    ; finiteCoordinatesCompatible = Quotient.compatible
    }

------------------------------------------------------------------------
-- Adapter into the earlier fail-closed analytic certificate surface.

data IsTriadicIntegerDomain : Set where
  triadicIntegerDomain : IsTriadicIntegerDomain

data ChartMapsIntoQ3 : Set where
  chartMapsIntoQ3 : ChartMapsIntoQ3

data IdentityTransitionAnalytic : Set where
  identityTransitionAnalytic : IdentityTransitionAnalytic

data DistinctFromRealSmooth : Set where
  nonArchimedeanNotRealSmooth : DistinctFromRealSmooth

data CompatibleWithQuotientTower : Set where
  coordinatesAreFiniteQuotients : CompatibleWithQuotientTower

concretePAdicAnalyticCertificate :
  Certificates.PAdicAnalyticManifoldCertificate
concretePAdicAnalyticCertificate =
  record
    { BaseField = Q3AmbientCode
    ; Carrier = Quotient.TriadicInverseLimitPoint
    ; Chart = GlobalTriadicChart
    ; chartDimension = Quotient.one
    ; carrierIsZ3OrCompactOpenDomain = IsTriadicIntegerDomain
    ; chartMapsIntoBaseField = ChartMapsIntoQ3
    ; analyticTransitionMaps = IdentityTransitionAnalytic
    ; distinctFromRealSmoothStructure = DistinctFromRealSmooth
    ; compatibleWithFiniteQuotientTower = CompatibleWithQuotientTower
    }

analyticInstancesStatement : String
analyticInstancesStatement =
  "The real lane is a concrete quarter-scale rational Cauchy/interval presentation with exact geometric-tail contraction and first-difference separation identities. The native 3-adic lane is the inverse-limit carrier with a global identity chart into a Q3 ambient code and exact finite-coordinate compatibility."

analyticInstancesBoundary : String
analyticInstancesBoundary =
  "QuarterRealCode is a constructive real presentation, not a completed ordered-field quotient. Q3AmbientCode supplies the analytic chart codomain used here; full Q3 field operations and a classical real-field completion remain separate foundational libraries rather than being asserted by naming them."
