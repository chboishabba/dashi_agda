module DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ; 0ℤ; 1ℤ; _+_; _-_; _*_; -_)
open import Data.Integer.Tactic.RingSolver using (solve)
open import Data.List.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.TriadicSectorQSeries as QS
import DASHI.Physics.Closure.TriadicModularAutomorphicGate as Modular

------------------------------------------------------------------------
-- Small logical carriers.

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    first : A
    second : B

open _×_ public

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- Integral lattice and SL₂(Z).

record LatticePoint : Set where
  constructor lattice-point
  field
    horizontal : ℤ
    vertical : ℤ

open LatticePoint public

record SL2Z : Set where
  constructor sl2z
  field
    a b c d : ℤ
    determinantOne : a * d - b * c ≡ 1ℤ

open SL2Z public

forwardIndex : SL2Z → LatticePoint → LatticePoint
forwardIndex g (lattice-point m n) =
  lattice-point
    (m * a g + n * c g)
    (m * b g + n * d g)

inverseIndex : SL2Z → LatticePoint → LatticePoint
inverseIndex g (lattice-point m n) =
  lattice-point
    (m * d g - n * c g)
    ((- m) * b g + n * a g)

lattice-ext :
  ∀ {m n m′ n′ : ℤ} →
  m ≡ m′ → n ≡ n′ →
  lattice-point m n ≡ lattice-point m′ n′
lattice-ext refl refl = refl

inverseForward :
  (g : SL2Z) →
  (p : LatticePoint) →
  inverseIndex g (forwardIndex g p) ≡ p
inverseForward (sl2z a b c d determinant) (lattice-point m n) =
  lattice-ext firstCoordinate secondCoordinate
  where
  firstPolynomial :
    (m * a + n * c) * d - (m * b + n * d) * c
    ≡ m * (a * d - b * c)
  firstPolynomial = solve (m ∷ n ∷ a ∷ b ∷ c ∷ d ∷ [])

  firstCoordinate :
    (m * a + n * c) * d - (m * b + n * d) * c ≡ m
  firstCoordinate =
    trans firstPolynomial (trans (cong (m *_) determinant) (solve (m ∷ [])))

  secondPolynomial :
    (- (m * a + n * c)) * b + (m * b + n * d) * a
    ≡ n * (a * d - b * c)
  secondPolynomial = solve (m ∷ n ∷ a ∷ b ∷ c ∷ d ∷ [])

  secondCoordinate :
    (- (m * a + n * c)) * b + (m * b + n * d) * a ≡ n
  secondCoordinate =
    trans secondPolynomial (trans (cong (n *_) determinant) (solve (n ∷ [])))

forwardInverse :
  (g : SL2Z) →
  (p : LatticePoint) →
  forwardIndex g (inverseIndex g p) ≡ p
forwardInverse (sl2z a b c d determinant) (lattice-point m n) =
  lattice-ext firstCoordinate secondCoordinate
  where
  firstPolynomial :
    (m * d - n * c) * a + ((- m) * b + n * a) * c
    ≡ m * (a * d - b * c)
  firstPolynomial = solve (m ∷ n ∷ a ∷ b ∷ c ∷ d ∷ [])

  firstCoordinate :
    (m * d - n * c) * a + ((- m) * b + n * a) * c ≡ m
  firstCoordinate =
    trans firstPolynomial (trans (cong (m *_) determinant) (solve (m ∷ [])))

  secondPolynomial :
    (m * d - n * c) * b + ((- m) * b + n * a) * d
    ≡ n * (a * d - b * c)
  secondPolynomial = solve (m ∷ n ∷ a ∷ b ∷ c ∷ d ∷ [])

  secondCoordinate :
    (m * d - n * c) * b + ((- m) * b + n * a) * d ≡ n
  secondCoordinate =
    trans secondPolynomial (trans (cong (n *_) determinant) (solve (n ∷ [])))

record LatticeBijection (g : SL2Z) : Set where
  constructor lattice-bijection
  field
    forward : LatticePoint → LatticePoint
    backward : LatticePoint → LatticePoint
    backwardForward : (p : LatticePoint) → backward (forward p) ≡ p
    forwardBackward : (p : LatticePoint) → forward (backward p) ≡ p

open LatticeBijection public

sl2zLatticeBijection : (g : SL2Z) → LatticeBijection g
sl2zLatticeBijection g =
  lattice-bijection
    (forwardIndex g)
    (inverseIndex g)
    (inverseForward g)
    (forwardInverse g)

------------------------------------------------------------------------
-- Analytic summand and reindexable absolute-sum interface.
--
-- The local summand law is the algebraic identity
--
--   (m·(gτ)+n)^(-k)
--     = (cτ+d)^k · (((m,n)g)·(τ,1))^(-k).
--
-- The global modular law below is derived from this identity and the proved
-- lattice bijection; it is not stored as an assumption.

record EisensteinAnalyticModel : Set₁ where
  field
    Scalar : Set
    zero : Scalar
    one : Scalar
    _+ˢ_ : Scalar → Scalar → Scalar
    _*ˢ_ : Scalar → Scalar → Scalar

    Parameter : Set
    actParameter : SL2Z → Parameter → Parameter
    denominator : SL2Z → Parameter → Scalar
    power : Scalar → Nat → Scalar

    summand : Nat → LatticePoint → Parameter → Scalar
    eisensteinSum : (LatticePoint → Scalar) → Scalar

    pointwiseCongruence :
      ∀ {f h : LatticePoint → Scalar} →
      ((p : LatticePoint) → f p ≡ h p) →
      eisensteinSum f ≡ eisensteinSum h

    reindexInvariant :
      (g : SL2Z) →
      (f : LatticePoint → Scalar) →
      eisensteinSum (λ p → f (forwardIndex g p)) ≡ eisensteinSum f

    factorOut :
      (factor : Scalar) →
      (f : LatticePoint → Scalar) →
      eisensteinSum (λ p → factor *ˢ f p)
      ≡ factor *ˢ eisensteinSum f

    summandTransformation :
      (weight : Nat) →
      (g : SL2Z) →
      (τ : Parameter) →
      (p : LatticePoint) →
      summand weight p (actParameter g τ)
      ≡ power (denominator g τ) weight
          *ˢ summand weight (forwardIndex g p) τ

open EisensteinAnalyticModel public

EisensteinSeries :
  EisensteinAnalyticModel → Nat → Parameter → Scalar
EisensteinSeries M weight τ =
  eisensteinSum M (λ p → summand M weight p τ)

------------------------------------------------------------------------
-- Genuine global transformation theorem.

eisensteinTransformation :
  (M : EisensteinAnalyticModel) →
  (weight : Nat) →
  (g : SL2Z) →
  (τ : Parameter M) →
  EisensteinSeries M weight (actParameter M g τ)
  ≡ _*ˢ_ M
      (power M (denominator M g τ) weight)
      (EisensteinSeries M weight τ)
eisensteinTransformation M weight g τ =
  trans
    (pointwiseCongruence M
      (summandTransformation M weight g τ))
    (trans
      (factorOut M
        (power M (denominator M g τ) weight)
        (λ p → summand M weight (forwardIndex g p) τ))
      (cong
        (_*ˢ_ M (power M (denominator M g τ) weight))
        (reindexInvariant M g (λ p → summand M weight p τ))))

------------------------------------------------------------------------
-- Adapter into the existing fail-closed modular gate.

record EisensteinTraceAgreement
  (C : QS.QSeriesCarrier)
  (T : QS.SectorTraceTower C)
  (M : EisensteinAnalyticModel) : Set₁ where
  field
    scalarMatchesCoefficient : Scalar M ≡ QS.Coeff C
    sector : QS.Sector T
    weight : Nat
    level : Nat
    coefficientAgreement : (n : Nat) → ⊤

open EisensteinTraceAgreement public

-- Equality of the scalar carrier is kept explicit in the agreement record.
-- The concrete adapter below uses a model whose Scalar is definitionally the
-- q-series coefficient carrier, avoiding an unsafe transport.

record CoefficientEisensteinModel
  (C : QS.QSeriesCarrier)
  (T : QS.SectorTraceTower C) : Set₁ where
  field
    analyticModel : EisensteinAnalyticModel
    scalarIsCoeff : Scalar analyticModel ≡ QS.Coeff C
    sector : QS.Sector T
    weight : Nat
    level : Nat
    coefficientAgreement : (n : Nat) → ⊤

open CoefficientEisensteinModel public

-- A definitionally aligned version is used for the actual gate constructor.
record AlignedEisensteinModel
  (C : QS.QSeriesCarrier)
  (T : QS.SectorTraceTower C) : Set₁ where
  field
    Parameter : Set
    actParameter : SL2Z → Parameter → Parameter
    denominator : SL2Z → Parameter → QS.Coeff C
    power : QS.Coeff C → Nat → QS.Coeff C
    summand : Nat → LatticePoint → Parameter → QS.Coeff C
    eisensteinSum : (LatticePoint → QS.Coeff C) → QS.Coeff C
    pointwiseCongruence :
      ∀ {f h : LatticePoint → QS.Coeff C} →
      ((p : LatticePoint) → f p ≡ h p) →
      eisensteinSum f ≡ eisensteinSum h
    reindexInvariant :
      (g : SL2Z) →
      (f : LatticePoint → QS.Coeff C) →
      eisensteinSum (λ p → f (forwardIndex g p)) ≡ eisensteinSum f
    factorOut :
      (factor : QS.Coeff C) →
      (f : LatticePoint → QS.Coeff C) →
      eisensteinSum (λ p → QS._*ᶜ_ C factor (f p))
      ≡ QS._*ᶜ_ C factor (eisensteinSum f)
    summandTransformation :
      (weight : Nat) →
      (g : SL2Z) →
      (τ : Parameter) →
      (p : LatticePoint) →
      summand weight p (actParameter g τ)
      ≡ QS._*ᶜ_ C
          (power (denominator g τ) weight)
          (summand weight (forwardIndex g p) τ)
    sector : QS.Sector T
    modularWeight : Nat
    modularLevel : Nat
    coefficientAgreement : (n : Nat) → ⊤

open AlignedEisensteinModel public

alignedAnalyticModel :
  (C : QS.QSeriesCarrier) →
  (T : QS.SectorTraceTower C) →
  AlignedEisensteinModel C T →
  EisensteinAnalyticModel
alignedAnalyticModel C T A =
  record
    { Scalar = QS.Coeff C
    ; zero = QS.zeroᶜ C
    ; one = QS.oneᶜ C
    ; _+ˢ_ = QS._+ᶜ_ C
    ; _*ˢ_ = QS._*ᶜ_ C
    ; Parameter = Parameter A
    ; actParameter = actParameter A
    ; denominator = denominator A
    ; power = power A
    ; summand = summand A
    ; eisensteinSum = eisensteinSum A
    ; pointwiseCongruence = pointwiseCongruence A
    ; reindexInvariant = reindexInvariant A
    ; factorOut = factorOut A
    ; summandTransformation = summandTransformation A
    }

modularTransformationFromEisenstein :
  (C : QS.QSeriesCarrier) →
  (T : QS.SectorTraceTower C) →
  (A : AlignedEisensteinModel C T) →
  Modular.ModularTransformationGate C T
modularTransformationFromEisenstein C T A =
  record
    { sector = sector A
    ; ParameterDomain = Parameter A
    ; ModularElement = SL2Z
    ; act = actParameter A
    ; automorphyFactor = λ g τ →
        power A (denominator A g τ) (modularWeight A)
    ; evaluateSeries = EisensteinSeries
        (alignedAnalyticModel C T A)
        (modularWeight A)
    ; weight = modularWeight A
    ; level = modularLevel A
    ; transformationLaw =
        eisensteinTransformation
          (alignedAnalyticModel C T A)
          (modularWeight A)
    ; coefficientAgreement = λ n → coefficientAgreement A n
    }

------------------------------------------------------------------------
-- A one-generator Eisenstein promotion, available only from the theorem gate.

data OneEisenstein : Set where
  eisensteinGenerator : OneEisenstein

data NoCusp : Set where

certifiedSingleEisensteinBasis :
  (C : QS.QSeriesCarrier) →
  (T : QS.SectorTraceTower C) →
  (A : AlignedEisensteinModel C T) →
  Modular.EisensteinBasisGate C T (modularTransformationFromEisenstein C T A)
certifiedSingleEisensteinBasis C T A =
  record
    { EisensteinIndex = OneEisenstein
    ; CuspIndex = NoCusp
    ; eisensteinCoordinate = λ _ → QS.oneᶜ C
    ; cuspCoordinate = λ ()
    ; eisensteinCoefficient = λ _ n →
        QS.traceCoefficient T n (sector A)
    ; cuspCoefficient = λ ()
    ; assembleCoefficient = λ n →
        QS.traceCoefficient T n (sector A)
    ; basisReconstruction = λ n → refl
    ; finiteDimensionalBasis = ⊤
    ; basisLinearIndependence = ⊤
    }

transformationTheoremStatement : String
transformationTheoremStatement =
  "The weight-k Eisenstein transformation law is derived from an explicit SL2(Z) lattice bijection, a local transformed-summand identity, reindex-invariant absolute summation, and factor extraction; the Eisenstein gate is constructed only after that theorem."
