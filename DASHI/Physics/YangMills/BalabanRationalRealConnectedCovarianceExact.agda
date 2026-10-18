{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanRationalRealConnectedCovarianceExact where

------------------------------------------------------------------------
-- EXACT Q -> R TRANSPORT OF CONNECTED COVARIANCE AND MAGNITUDE
--
-- Once the three selected expectations F, G, FG are the same physical numbers
-- in the rational executable carrier and the real Haar/continuum carrier,
-- covariance is not a new same-object theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _-_; ∣_∣)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; _*ℝ_; _-ℝ_; absℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as Ring
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as Add
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Base

embedQ : Ring.RationalRealRingEmbedding → ℚ → ℝ
embedQ embedding =
  Base.embed (Add.base (Ring.additive embedding))

record RationalRealAbsoluteRingEmbedding : Set₁ where
  field
    ring : Ring.RationalRealRingEmbedding

    subtractExact : ∀ left right →
      embedQ ring (left - right)
      ≡ embedQ ring left -ℝ embedQ ring right

    absoluteExact : ∀ value →
      embedQ ring (∣ value ∣)
      ≡ absℝ (embedQ ring value)

open RationalRealAbsoluteRingEmbedding public

rationalConnectedCovariance :
  ∀ {Observable : Set} →
  (Observable → ℚ) →
  (Observable → Observable → Observable) →
  Observable → Observable → ℚ
rationalConnectedCovariance expectation multiplyObservable left right =
  expectation (multiplyObservable left right)
  - expectation left * expectation right

realConnectedCovariance :
  ∀ {Observable : Set} →
  (Observable → ℝ) →
  (Observable → Observable → Observable) →
  Observable → Observable → ℝ
realConnectedCovariance expectation multiplyObservable left right =
  expectation (multiplyObservable left right)
  -ℝ expectation left *ℝ expectation right

record SelectedExpectationTripleWeld
    {Observable : Set}
    (embedding : RationalRealAbsoluteRingEmbedding)
    (multiplyObservable : Observable → Observable → Observable)
    (rationalExpectation : Observable → ℚ)
    (realExpectation : Observable → ℝ)
    (left right : Observable) : Set where
  field
    leftExpectationExact :
      embedQ (ring embedding) (rationalExpectation left)
      ≡ realExpectation left

    rightExpectationExact :
      embedQ (ring embedding) (rationalExpectation right)
      ≡ realExpectation right

    productExpectationExact :
      embedQ (ring embedding)
        (rationalExpectation (multiplyObservable left right))
      ≡
      realExpectation (multiplyObservable left right)

open SelectedExpectationTripleWeld public

connectedCovarianceEmbeddingExact :
  ∀ {Observable}
    {embedding : RationalRealAbsoluteRingEmbedding}
    {multiplyObservable : Observable → Observable → Observable}
    {rationalExpectation : Observable → ℚ}
    {realExpectation : Observable → ℝ}
    {left right}
    (weld :
      SelectedExpectationTripleWeld
        embedding multiplyObservable
        rationalExpectation realExpectation
        left right) →
  embedQ (ring embedding)
    (rationalConnectedCovariance
      rationalExpectation multiplyObservable left right)
  ≡
  realConnectedCovariance
    realExpectation multiplyObservable left right
connectedCovarianceEmbeddingExact
    {embedding = embedding}
    {multiplyObservable = multiplyObservable}
    {rationalExpectation = rationalExpectation}
    {realExpectation = realExpectation}
    {left = left} {right = right}
    weld =
  trans
    (subtractExact embedding
      (rationalExpectation (multiplyObservable left right))
      (rationalExpectation left * rationalExpectation right))
    (trans
      (cong
        (λ product →
          embedQ (ring embedding)
            (rationalExpectation (multiplyObservable left right))
          -ℝ product)
        (Ring.multiplyExact (ring embedding)
          (rationalExpectation left)
          (rationalExpectation right)))
      (cong₂ _-ℝ_
        (productExpectationExact weld)
        (cong₂ _*ℝ_
          (leftExpectationExact weld)
          (rightExpectationExact weld))))
  where
  cong₂ :
    ∀ {A B C : Set} {a a' : A} {b b' : B}
      (f : A → B → C) →
    a ≡ a' → b ≡ b' → f a b ≡ f a' b'
  cong₂ f refl refl = refl

connectedCovarianceMagnitudeEmbeddingExact :
  ∀ {Observable}
    {embedding : RationalRealAbsoluteRingEmbedding}
    {multiplyObservable : Observable → Observable → Observable}
    {rationalExpectation : Observable → ℚ}
    {realExpectation : Observable → ℝ}
    {left right}
    (weld :
      SelectedExpectationTripleWeld
        embedding multiplyObservable
        rationalExpectation realExpectation
        left right) →
  embedQ (ring embedding)
    (∣ rationalConnectedCovariance
        rationalExpectation multiplyObservable left right ∣)
  ≡
  absℝ
    (realConnectedCovariance
      realExpectation multiplyObservable left right)
connectedCovarianceMagnitudeEmbeddingExact
    {embedding = embedding} weld =
  trans
    (absoluteExact embedding _)
    (cong absℝ
      (connectedCovarianceEmbeddingExact weld))

rationalRealConnectedCovarianceCompilerLevel : ProofLevel
rationalRealConnectedCovarianceCompilerLevel = machineChecked

rationalRealCovarianceMagnitudeCompilerLevel : ProofLevel
rationalRealCovarianceMagnitudeCompilerLevel = machineChecked

-- Standard scalar authority for the repository's chosen Q -> R embedding.
rationalRealSubtractAndAbsoluteEmbeddingLevel : ProofLevel
rationalRealSubtractAndAbsoluteEmbeddingLevel = standardImported
