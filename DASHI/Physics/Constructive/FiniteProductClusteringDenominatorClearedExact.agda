module DASHI.Physics.Constructive.FiniteProductClusteringDenominatorClearedExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II",
-- Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978.
--
-- DASHI CONTRIBUTION
--
-- Construct an exact two-site product measure without introducing rational
-- normalization constructors.  For arbitrary two-state observables F and G,
-- the denominator-cleared identity is
--
--   4 E[F G] = (2 E[F]) (2 E[G]).
--
-- Therefore the denominator-cleared connected correlation vanishes exactly
-- at every declared separation.  This is an exact finite product/OS4 model,
-- not clustering for an interacting gauge measure.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

record TwoStateObservable : Set where
  constructor twoStateObservable
  field
    plusValue minusValue : ℚ

open TwoStateObservable public

twiceExpectation : TwoStateObservable → ℚ
twiceExpectation observable =
  plusValue observable + minusValue observable

fourTimesJointExpectation :
  TwoStateObservable → TwoStateObservable → ℚ
fourTimesJointExpectation first second =
  plusValue first * plusValue second
  + plusValue first * minusValue second
  + minusValue first * plusValue second
  + minusValue first * minusValue second

productMeasureFactorization : ∀ first second →
  fourTimesJointExpectation first second
  ≡ twiceExpectation first * twiceExpectation second
productMeasureFactorization
    (twoStateObservable fPlus fMinus)
    (twoStateObservable gPlus gMinus) =
  solve (fPlus ∷ fMinus ∷ gPlus ∷ gMinus ∷ [])

fourTimesConnectedCorrelation :
  TwoStateObservable → TwoStateObservable → ℚ
fourTimesConnectedCorrelation first second =
  fourTimesJointExpectation first second
  - twiceExpectation first * twiceExpectation second

connectedCorrelationVanishes : ∀ first second →
  fourTimesConnectedCorrelation first second ≡ 0ℚ
connectedCorrelationVanishes
    (twoStateObservable fPlus fMinus)
    (twoStateObservable gPlus gMinus) =
  solve (fPlus ∷ fMinus ∷ gPlus ∷ gMinus ∷ [])

record SeparatedObservables : Set where
  constructor separatedObservables
  field
    separation : Nat
    leftObservable rightObservable : TwoStateObservable

open SeparatedObservables public

exactClusteringAtEverySeparation : ∀ separated →
  fourTimesConnectedCorrelation
    (leftObservable separated)
    (rightObservable separated)
  ≡ 0ℚ
exactClusteringAtEverySeparation separated =
  connectedCorrelationVanishes
    (leftObservable separated)
    (rightObservable separated)

record FiniteProductClusteringCertificate : Set where
  field
    factorization : ∀ first second →
      fourTimesJointExpectation first second
      ≡ twiceExpectation first * twiceExpectation second
    connectedZero : ∀ first second →
      fourTimesConnectedCorrelation first second ≡ 0ℚ
    allSeparations : ∀ separated →
      fourTimesConnectedCorrelation
        (leftObservable separated)
        (rightObservable separated)
      ≡ 0ℚ

canonicalFiniteProductClusteringCertificate :
  FiniteProductClusteringCertificate
canonicalFiniteProductClusteringCertificate = record
  { factorization = productMeasureFactorization
  ; connectedZero = connectedCorrelationVanishes
  ; allSeparations = exactClusteringAtEverySeparation
  }

record InteractingOS4Boundary : Set₁ where
  field
    GaugeObservable : Set
    euclideanMeasure : Set
    translationAction : Set
    connectedCorrelation : Set
    exponentialDecayRate : Set
    distanceUniformConstant : Set
    spacingUniformity : Set
    os4ClusterTheorem : Set
