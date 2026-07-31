module DASHI.Foundations.UBP.RationalCertificateTransport where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Rational using
  ( ℚ ; _+_ ; _-_ ; _*_ ; _/_ ; _≤_ ; _<_ ; 0ℚ )
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.UBP.Pi50ConvergentTable as Pi50

------------------------------------------------------------------------
-- Rational certificate first, semantic exact-real embedding second.
--
-- This module is intentionally independent of any particular real backend.
-- It proves the reusable interval-transport logic in ordered rational terms
-- and isolates the exact algebraic factorisation needed for the observer map
--
--                    f(x) = x / (x² + 2).
--
-- Constructive pi enters only through a later containment witness.  Bishop,
-- Cubical or another exact-real carrier is not asked to rediscover the finite
-- rational arithmetic.
------------------------------------------------------------------------

infixr 4 _,_ _×_

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open _×_ public

record RationalInterval : Set where
  constructor rationalInterval
  field
    lower : ℚ
    upper : ℚ
    ordered : lower ≤ upper

open RationalInterval public

record PointInInterval (interval : RationalInterval) (point : ℚ) : Set where
  constructor pointInInterval
  field
    lowerBound : lower interval ≤ point
    upperBound : point ≤ upper interval

open PointInInterval public

record AntitoneOn
    (Domain : ℚ → Set)
    (function : ℚ → ℚ) : Set₁ where
  field
    antitone :
      ∀ {left right} →
      Domain left →
      Domain right →
      left ≤ right →
      function right ≤ function left

open AntitoneOn public

antitoneIntervalTransport :
  ∀ {Domain : ℚ → Set}
    {function : ℚ → ℚ}
    (antitoneCertificate : AntitoneOn Domain function)
    (interval : RationalInterval)
    (lowerDomain : Domain (lower interval))
    (upperDomain : Domain (upper interval))
    (point : ℚ)
    (pointDomain : Domain point) →
  PointInInterval interval point →
  (function (upper interval) ≤ function point)
  ×
  (function point ≤ function (lower interval))
antitoneIntervalTransport
  antitoneCertificate interval lowerDomain upperDomain point pointDomain
  (pointInInterval lower≤point point≤upper) =
  antitone antitoneCertificate pointDomain upperDomain point≤upper
  ,
  antitone antitoneCertificate lowerDomain pointDomain lower≤point

record ExactRealEmbeddingBoundary : Set₁ where
  field
    ExactReal : Set
    embedRational : ℚ → ExactReal
    lessOrEqual : ExactReal → ExactReal → Set
    embeddingMonotone :
      ∀ {left right} →
      left ≤ right →
      lessOrEqual (embedRational left) (embedRational right)

open ExactRealEmbeddingBoundary public

embedRationalInterval :
  (boundary : ExactRealEmbeddingBoundary) →
  (interval : RationalInterval) →
  lessOrEqual boundary
    (embedRational boundary (lower interval))
    (embedRational boundary (upper interval))
embedRationalInterval boundary interval =
  embeddingMonotone boundary (ordered interval)

------------------------------------------------------------------------
-- Observer-map algebra.
------------------------------------------------------------------------

observerMap : ℚ → ℚ
observerMap x = x / (x * x + 2)

observerCrossDifference : ℚ → ℚ → ℚ
observerCrossDifference x y =
  x * (y * y + 2) - y * (x * x + 2)

observerFactorDifference : ℚ → ℚ → ℚ
observerFactorDifference x y =
  (y - x) * (x * y - 2)

observerCrossDifferenceIdentity :
  (x y : ℚ) →
  observerCrossDifference x y
  ≡ observerFactorDifference x y
observerCrossDifferenceIdentity x y = ℚRing.solve

record PositiveCrossMultiplication : Set₁ where
  field
    positiveDenominator : ℚ → Set
    crossMultiplyAntitone :
      ∀ {x y} →
      positiveDenominator (x * x + 2) →
      positiveDenominator (y * y + 2) →
      0ℚ ≤ observerCrossDifference x y →
      observerMap y ≤ observerMap x

open PositiveCrossMultiplication public

record ObserverFactorCertificate
    (crossMultiplication : PositiveCrossMultiplication)
    (x y : ℚ) : Set where
  constructor observerFactorCertificate
  field
    x≤y : x ≤ y
    xyAtLeastTwo : 2 ≤ x * y
    xDenominatorPositive :
      positiveDenominator crossMultiplication (x * x + 2)
    yDenominatorPositive :
      positiveDenominator crossMultiplication (y * y + 2)
    factorProductNonnegative :
      0ℚ ≤ (y - x) * (x * y - 2)

open ObserverFactorCertificate public

observerAntitoneFromFactorCertificate :
  (crossMultiplication : PositiveCrossMultiplication) →
  (x y : ℚ) →
  ObserverFactorCertificate crossMultiplication x y →
  observerMap y ≤ observerMap x
observerAntitoneFromFactorCertificate
  crossMultiplication x y certificate =
  crossMultiplyAntitone crossMultiplication
    (xDenominatorPositive certificate)
    (yDenominatorPositive certificate)
    (let factorNonnegative = factorProductNonnegative certificate in
      subst
        (0ℚ ≤_)
        (sym (observerCrossDifferenceIdentity x y))
        factorNonnegative)
  where
    open import Relation.Binary.PropositionalEquality.Core
      using (subst; sym)

------------------------------------------------------------------------
-- Canonical continued-fraction rational endpoints.
------------------------------------------------------------------------

canonicalPiRadius : ℚ
canonicalPiRadius =
  1 /
  30975954210267369528087864730966858500331494237311153657

canonicalPiLower : ℚ
canonicalPiLower = Pi50.canonicalPi50 - canonicalPiRadius

canonicalPiUpper : ℚ
canonicalPiUpper = Pi50.canonicalPi50 + canonicalPiRadius

canonicalYLowerCandidate : ℚ
canonicalYLowerCandidate = observerMap canonicalPiUpper

canonicalYUpperCandidate : ℚ
canonicalYUpperCandidate = observerMap canonicalPiLower

canonicalPiLowerDefinition :
  canonicalPiLower
  ≡ Pi50.canonicalPi50 - canonicalPiRadius
canonicalPiLowerDefinition = refl

canonicalPiUpperDefinition :
  canonicalPiUpper
  ≡ Pi50.canonicalPi50 + canonicalPiRadius
canonicalPiUpperDefinition = refl

canonicalYLowerDefinition :
  canonicalYLowerCandidate ≡ observerMap canonicalPiUpper
canonicalYLowerDefinition = refl

canonicalYUpperDefinition :
  canonicalYUpperCandidate ≡ observerMap canonicalPiLower
canonicalYUpperDefinition = refl

record PiYTransportInstantiation (ExactReal : Set) : Set₁ where
  field
    embedding : ExactRealEmbeddingBoundary
    piExact : ExactReal
    observerExact : ExactReal → ExactReal

    canonicalPiInterval : RationalInterval
    canonicalPiIntervalLower :
      lower canonicalPiInterval ≡ canonicalPiLower
    canonicalPiIntervalUpper :
      upper canonicalPiInterval ≡ canonicalPiUpper

    piContainedLower :
      lessOrEqual embedding
        (embedRational embedding (lower canonicalPiInterval))
        piExact
    piContainedUpper :
      lessOrEqual embedding
        piExact
        (embedRational embedding (upper canonicalPiInterval))

    observerCommutesWithEmbedding :
      (x : ℚ) →
      observerExact (embedRational embedding x)
      ≡ embedRational embedding (observerMap x)

    observerAntitoneOnPiInterval :
      (point : ℚ) →
      lower canonicalPiInterval ≤ point →
      point ≤ upper canonicalPiInterval →
      observerMap (upper canonicalPiInterval)
      ≤ observerMap point
      ×
      observerMap point
      ≤ observerMap (lower canonicalPiInterval)

open PiYTransportInstantiation public

record RationalFirstArchitectureStatus : Set where
  constructor rationalFirstArchitectureStatus
  field
    finiteInequalityProvedBeforeRealEmbedding : Bool
    finiteInequalityProvedBeforeRealEmbeddingIsTrue :
      finiteInequalityProvedBeforeRealEmbedding ≡ true
    observerCrossFactorisationProved : Bool
    observerCrossFactorisationProvedIsTrue :
      observerCrossFactorisationProved ≡ true
    antitoneIntervalTransportGeneric : Bool
    antitoneIntervalTransportGenericIsTrue :
      antitoneIntervalTransportGeneric ≡ true
    canonicalPiRationalEndpointsDefined : Bool
    canonicalPiRationalEndpointsDefinedIsTrue :
      canonicalPiRationalEndpointsDefined ≡ true
    constructivePiContainmentInstantiated : Bool
    constructivePiContainmentInstantiatedIsFalse :
      constructivePiContainmentInstantiated ≡ false
    reading : String

canonicalRationalFirstArchitectureStatus :
  RationalFirstArchitectureStatus
canonicalRationalFirstArchitectureStatus =
  rationalFirstArchitectureStatus
    true refl
    true refl
    true refl
    true refl
    false refl
    "ordered rational algebra owns factorisation and interval transport; the exact-real backend supplies only the constructive pi containment and embedding compatibility witnesses"

rationalCertificateTransportReceipt : GenericReceipt.GenericReceipt
rationalCertificateTransportReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "rational certificate before exact-real embedding"
    "DASHI.Foundations.UBP.RationalCertificateTransport"
    "canonicalRationalFirstArchitectureStatus"
    "generic antitone interval transport, exact observer cross-factorisation, canonical continued-fraction rational endpoints and an exact-real embedding interface are exposed"
    "constructive pi containment and the positive cross-multiplication order package remain explicit instantiation obligations; no rational approximation is promoted to exact pi or exact Y"
    "agda -i . DASHI/Foundations/UBP/RationalCertificateTransport.agda"

rationalCertificateTransportReceiptNonPromoting :
  GenericReceipt.promotesClaim rationalCertificateTransportReceipt ≡ false
rationalCertificateTransportReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse rationalCertificateTransportReceipt
