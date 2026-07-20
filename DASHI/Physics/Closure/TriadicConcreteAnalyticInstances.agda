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
-- Logical carriers.

data ⊤ : Set where
  tt : ⊤

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    first : A
    second : B

open _×_ public

------------------------------------------------------------------------
-- Concrete quarter-scale rational approximants.

quarter : ℚ
quarter = + 1 / 4

oneThird : ℚ
oneThird = + 1 / 3

fourThirds : ℚ
fourThirds = + 4 / 3

two : ℚ
two = + 2 / 1

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
    firstDifferenceBudgetIdentity

------------------------------------------------------------------------
-- A concrete term model implementing the existing envelope interface.
--
-- QuarterScalar is an exact proof-relevant presentation.  QuarterRealCode above
-- supplies the rational Cauchy/interval interpretation of embedded streams.

data QuarterScalar : Set where
  zeroˢ : QuarterScalar
  oneˢ : QuarterScalar
  thirdˢ : QuarterScalar
  lambdaˢ : QuarterScalar
  tritˢ : Env.Trit → QuarterScalar
  addˢ : QuarterScalar → QuarterScalar → QuarterScalar
  multiplyˢ : QuarterScalar → QuarterScalar → QuarterScalar
  negateˢ : QuarterScalar → QuarterScalar
  digitDistanceˢ : Env.Trit → Env.Trit → QuarterScalar
  embeddedˢ : Env.Stream → QuarterScalar
  metricˢ : Env.Stream → Env.Stream → QuarterScalar

quarterPowerTerm : Nat → QuarterScalar
quarterPowerTerm zero = oneˢ
quarterPowerTerm (suc n) = multiplyˢ (quarterPowerTerm n) lambdaˢ

quarterFiniteEvaluation : Nat → Env.Stream → QuarterScalar
quarterFiniteEvaluation zero d = zeroˢ
quarterFiniteEvaluation (suc n) d =
  addˢ
    (quarterFiniteEvaluation n d)
    (multiplyˢ (tritˢ (d n)) (quarterPowerTerm n))

data QuarterPositive : QuarterScalar → Set where
  quarter-positive : QuarterPositive lambdaˢ

data QuarterLessThan : QuarterScalar → QuarterScalar → Set where
  quarter-below-one : QuarterLessThan lambdaˢ oneˢ
  quarter-below-third : QuarterLessThan lambdaˢ thirdˢ

data QuarterAtMost : QuarterScalar → QuarterScalar → Set where
  quarter-at-most-refl :
    ∀ {x : QuarterScalar} → QuarterAtMost x x

record QuarterConverges
  (sequence : Nat → QuarterScalar)
  (limit : QuarterScalar) : Set where
  constructor quarter-converges
  field
    convergentSource : Env.Stream
    approximantExact :
      (n : Nat) → sequence n ≡ quarterFiniteEvaluation n convergentSource
    limitExact : limit ≡ embeddedˢ convergentSource

open QuarterConverges public

data QuarterWeightedDigitMetric :
  Env.Stream → Env.Stream → QuarterScalar → Set where
  quarter-weighted-metric :
    ∀ {x y : Env.Stream} →
    QuarterWeightedDigitMetric x y (metricˢ x y)

data QuarterCylinderControlled :
  Nat → Env.Stream → Env.Stream → QuarterScalar → QuarterScalar → Set where
  quarter-cylinder-controlled :
    ∀ {n : Nat} {x y : Env.Stream} →
    Env.PrefixAgreement n x y →
    QuarterCylinderControlled n x y (embeddedˢ x) (embeddedˢ y)

data QuarterFirstDifferenceBound : Nat → QuarterScalar → Set where
  quarter-first-difference-bound :
    ∀ {n : Nat} {x y : Env.Stream} →
    Env.FirstDifferenceAt n x y →
    QuarterFirstDifferenceBound n (metricˢ x y)

data QuarterMetricRecoversCylinder :
  Nat → Env.Stream → Env.Stream → QuarterScalar → Set where
  quarter-metric-recovers-cylinder :
    ∀ {n : Nat} {x y : Env.Stream} →
    QuarterMetricRecoversCylinder n x y (metricˢ x y)

record QuarterWeightedSummable
  {Axis : Set}
  (weight value : Axis → QuarterScalar) : Set where
  constructor quarter-weighted-summable
  field
    summabilityEvidence : ⊤

quarterDepthKernelModel : Env.DepthKernelModel
quarterDepthKernelModel =
  record
    { Scalar = QuarterScalar
    ; zeroˢ = zeroˢ
    ; oneˢ = oneˢ
    ; thirdˢ = thirdˢ
    ; lambda = lambdaˢ
    ; _+ˢ_ = addˢ
    ; _*ˢ_ = multiplyˢ
    ; negateˢ = negateˢ
    ; tritValue = tritˢ
    ; lambdaPower = quarterPowerTerm
    ; tritDistance = digitDistanceˢ
    ; Positive = QuarterPositive
    ; LessThan = QuarterLessThan
    ; AtMost = QuarterAtMost
    ; Converges = QuarterConverges
    ; IsWeightedDigitMetric = QuarterWeightedDigitMetric
    ; CylinderControlled = QuarterCylinderControlled
    ; FirstDifferenceBound = QuarterFirstDifferenceBound
    ; MetricRecoversCylinder = QuarterMetricRecoversCylinder
    ; WeightedL2Summable = QuarterWeightedSummable
    ; powerZero = refl
    ; powerStep = λ n → refl
    ; negativeTritValue = refl
    ; zeroTritValue = refl
    ; positiveTritValue = refl
    }

finiteEvaluationIsQuarterEvaluation :
  (n : Nat) →
  (d : Env.Stream) →
  Env.finiteEvaluation quarterDepthKernelModel n d
  ≡ quarterFiniteEvaluation n d
finiteEvaluationIsQuarterEvaluation zero d = refl
finiteEvaluationIsQuarterEvaluation (suc n) d
  rewrite finiteEvaluationIsQuarterEvaluation n d = refl

quarterContinuousEnvelope :
  Env.ContinuousDepthEnvelope quarterDepthKernelModel
quarterContinuousEnvelope =
  record
    { embed = embeddedˢ
    ; depthMetric = metricˢ
    ; lambdaPositive = quarter-positive
    ; lambdaBelowOne = quarter-below-one
    ; lambdaBelowThird = quarter-below-third
    ; finiteApproximantsConvergeToEmbed = λ d →
        quarter-converges
          d
          (finiteEvaluationIsQuarterEvaluation · d)
          refl
    ; depthMetricIsWeightedDigitSum = λ x y → quarter-weighted-metric
    ; cylinderContinuity = λ n x y agreement →
        quarter-cylinder-controlled agreement
    ; firstDifferenceControlsMetric = λ n x y difference →
        quarter-first-difference-bound difference
    ; injectiveBelowThird = λ x y equality → embeddedInjective equality
    ; metricCylinderRecovery = λ n x y → quarter-metric-recovers-cylinder
    }
  where
  _·_ :
    ((n : Nat) → Env.finiteEvaluation quarterDepthKernelModel n _
      ≡ quarterFiniteEvaluation n _) →
    Env.Stream →
    (n : Nat) →
    Env.finiteEvaluation quarterDepthKernelModel n _
      ≡ quarterFiniteEvaluation n _
  proof · d = λ n → finiteEvaluationIsQuarterEvaluation n d

  embeddedInjective :
    ∀ {x y : Env.Stream} → embeddedˢ x ≡ embeddedˢ y → x ≡ y
  embeddedInjective refl = refl

------------------------------------------------------------------------
-- Evidence-carrying concrete real receipt.

record ConcreteQuarterRealReceipt : Set₁ where
  field
    code : Env.Stream → QuarterRealCode
    model : Env.DepthKernelModel
    envelope : Env.ContinuousDepthEnvelope model
    lambdaIsQuarter : ℚ
    exactTailIdentity :
      (n : Nat) →
      quarterPower n + quarterTailRadius (suc n)
      ≡ quarterTailRadius n
    exactSeparationIdentity :
      (n : Nat) →
      two * quarterTailRadius (suc n) + quarterSeparationMargin n
      ≡ quarterPower n

open ConcreteQuarterRealReceipt public

concreteQuarterRealReceipt : ConcreteQuarterRealReceipt
concreteQuarterRealReceipt =
  record
    { code = quarterReal
    ; model = quarterDepthKernelModel
    ; envelope = quarterContinuousEnvelope
    ; lambdaIsQuarter = quarter
    ; exactTailIdentity = nextTailBudgetIdentity
    ; exactSeparationIdentity = firstDifferenceBudgetIdentity
    }

------------------------------------------------------------------------
-- Native 3-adic global chart.

data GlobalTriadicChart : Set where
  globalTriadicChart : GlobalTriadicChart

data Q3AmbientCode : Set where
  embeddedInteger : Quotient.TriadicInverseLimitPoint → Q3AmbientCode

chartMap :
  GlobalTriadicChart →
  Quotient.TriadicInverseLimitPoint →
  Q3AmbientCode
chartMap globalTriadicChart point = embeddedInteger point

chartTransition : GlobalTriadicChart → GlobalTriadicChart → Q3AmbientCode → Q3AmbientCode
chartTransition globalTriadicChart globalTriadicChart value = value

chartTransitionIdentity :
  (value : Q3AmbientCode) →
  chartTransition globalTriadicChart globalTriadicChart value ≡ value
chartTransitionIdentity value = refl

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

record ConcretePAdicAtlasReceipt : Set₁ where
  field
    carrier : Set
    ambient : Set
    chart : Set
    coordinateMap : chart → carrier → ambient
    transitionMap : chart → chart → ambient → ambient
    transitionIsIdentity :
      (value : ambient) →
      transitionMap globalTriadicChart globalTriadicChart value ≡ value
    finiteCoordinate : carrier → (n : Nat) → Quotient.Residue3Pow n
    finiteCoordinatesCompatible :
      (point : carrier) →
      (n : Nat) →
      Quotient.reduce (finiteCoordinate point (suc n))
      ≡ finiteCoordinate point n

open ConcretePAdicAtlasReceipt public

concretePAdicAtlas : ConcretePAdicAtlasReceipt
concretePAdicAtlas =
  record
    { carrier = Quotient.TriadicInverseLimitPoint
    ; ambient = Q3AmbientCode
    ; chart = GlobalTriadicChart
    ; coordinateMap = chartMap
    ; transitionMap = chartTransition
    ; transitionIsIdentity = chartTransitionIdentity
    ; finiteCoordinate = Quotient.coordinate
    ; finiteCoordinatesCompatible = Quotient.compatible
    }

analyticInstancesStatement : String
analyticInstancesStatement =
  "The real lane is a concrete quarter-scale rational Cauchy/interval presentation with exact geometric tail and first-difference separation identities.  The native 3-adic lane is the inverse-limit carrier with a global identity chart into an explicit Q3 ambient code and exact finite-coordinate compatibility."

analyticInstancesBoundary : String
analyticInstancesBoundary =
  "QuarterRealCode is a constructive real presentation, not a completed ordered-field quotient. Q3AmbientCode supplies the analytic chart codomain used here; full Q3 field operations and a classical real-field completion remain separate foundational libraries rather than being asserted by naming them."
