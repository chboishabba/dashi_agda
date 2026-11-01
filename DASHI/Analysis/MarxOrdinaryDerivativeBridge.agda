module DASHI.Analysis.MarxOrdinaryDerivativeBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Set)
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Analysis.MarxDifferentialCore public

------------------------------------------------------------------------
-- Punctured little-o topology.
--
-- A remainder is small relative to h when its normalized value tends to zero
-- on punctured approaches to zero.  The normalization operation is supplied by
-- the selected field/norm carrier; no division or topology is fabricated by
-- the finite algebra itself.

record RemainderDerivativeStructure
  (A : MarxAlgebra)
  : Set₂ where
  field
    Nonzero : Carrier A → Set

    normaliseRemainder :
      Carrier A → Carrier A → Carrier A

    TendsToZeroPunctured :
      (Carrier A → Carrier A) → Set₁

    puncturedCongruence :
      ∀ {phi psi : Carrier A → Carrier A} →
      (∀ h → Nonzero h → phi h ≡ psi h) →
      TendsToZeroPunctured phi →
      TendsToZeroPunctured psi

    normalizedProductCancellation :
      ∀ h q →
      Nonzero h →
      normaliseRemainder h (_*_ A h q) ≡ q

    zeroTendsToZero :
      TendsToZeroPunctured (λ _ → zero A)

open RemainderDerivativeStructure public

NormalizedRemainderVanishes :
  {A : MarxAlgebra} →
  RemainderDerivativeStructure A →
  (Carrier A → Carrier A) →
  Set₁
NormalizedRemainderVanishes R remainder =
  TendsToZeroPunctured R
    (λ h → normaliseRemainder R h (remainder h))

littleOAtZero :
  {A : MarxAlgebra} →
  RemainderDerivativeStructure A →
  (Carrier A → Carrier A) →
  Set₁
littleOAtZero = NormalizedRemainderVanishes

------------------------------------------------------------------------
-- Ordinary remainder derivative.

record OrdinaryDerivativeAt
  {A : MarxAlgebra}
  (R : RemainderDerivativeStructure A)
  (f : Function A)
  (x : Carrier A)
  : Set₁ where
  field
    linearCoefficient : Carrier A
    remainder : Carrier A → Carrier A

    expansion :
      ∀ h →
      f (_+_ A x h)
      ≡ _+_ A
          (f x)
          (_+_ A
            (_*_ A linearCoefficient h)
            (remainder h))

    normalizedRemainderVanishes :
      NormalizedRemainderVanishes R remainder

open OrdinaryDerivativeAt public

------------------------------------------------------------------------
-- Genuine diagonal continuity of the preliminary derived function.

PreliminaryContinuousAtDiagonal :
  {A : MarxAlgebra} →
  (R : RemainderDerivativeStructure A) →
  {f : Function A} →
  MarxFactorisation A f →
  Carrier A →
  Set₁
PreliminaryContinuousAtDiagonal {A} R F x =
  TendsToZeroPunctured R
    (λ h →
      _-_ A
        (preliminary F x (_+_ A x h))
        (preliminary F x x))

ContinuousDiagonal :
  {A : MarxAlgebra} →
  (R : RemainderDerivativeStructure A) →
  {f : Function A} →
  MarxFactorisation A f →
  Carrier A →
  Set₁
ContinuousDiagonal = PreliminaryContinuousAtDiagonal

marxRemainder :
  {A : MarxAlgebra} →
  {f : Function A} →
  (F : MarxFactorisation A f) →
  Carrier A →
  Carrier A →
  Carrier A
marxRemainder {A} F x h =
  _*_ A h
    (_-_ A
      (preliminary F x (_+_ A x h))
      (preliminary F x x))

------------------------------------------------------------------------
-- Exact finite-algebra rearrangement required to expose the remainder.

record MarxRemainderExpansionLaws
  (A : MarxAlgebra)
  : Set₁ where
  field
    factorisationToRemainderExpansion :
      {f : Function A} →
      (F : MarxFactorisation A f) →
      (x h : Carrier A) →
      f (_+_ A x h)
      ≡ _+_ A
          (f x)
          (_+_ A
            (_*_ A (marxDerivative F x) h)
            (marxRemainder F x h))

open MarxRemainderExpansionLaws public

------------------------------------------------------------------------
-- Main compatibility construction.
--
-- The normalized Marx remainder equals the diagonal preliminary difference on
-- every nonzero h.  Diagonal continuity therefore supplies the actual little-o
-- proof rather than merely assuming equality with an ordinary derivative.

marxFactorisationAndDiagonalContinuityGiveOrdinaryDerivative :
  {A : MarxAlgebra} →
  (R : RemainderDerivativeStructure A) →
  (E : MarxRemainderExpansionLaws A) →
  {f : Function A} →
  (F : MarxFactorisation A f) →
  (x : Carrier A) →
  PreliminaryContinuousAtDiagonal R F x →
  OrdinaryDerivativeAt R f x
marxFactorisationAndDiagonalContinuityGiveOrdinaryDerivative {A} R E F x continuous =
  record
    { linearCoefficient = marxDerivative F x
    ; remainder = marxRemainder F x
    ; expansion = factorisationToRemainderExpansion E F x
    ; normalizedRemainderVanishes =
        puncturedCongruence R
          (λ h nonzeroH →
            sym
              (normalizedProductCancellation R
                h
                (_-_ A
                  (preliminary F x (_+_ A x h))
                  (preliminary F x x))
                nonzeroH))
          continuous
    }

------------------------------------------------------------------------
-- Uniqueness is a topology/field theorem, separated from finite algebra.

record OrdinaryDerivativeUniqueness
  {A : MarxAlgebra}
  (R : RemainderDerivativeStructure A)
  : Set₁ where
  field
    uniqueLinearCoefficient :
      {f : Function A} →
      {x : Carrier A} →
      (left right : OrdinaryDerivativeAt R f x) →
      linearCoefficient left ≡ linearCoefficient right

open OrdinaryDerivativeUniqueness public

marxDerivativeEqualsOrdinaryDerivative :
  {A : MarxAlgebra} →
  {R : RemainderDerivativeStructure A} →
  (E : MarxRemainderExpansionLaws A) →
  (U : OrdinaryDerivativeUniqueness R) →
  {f : Function A} →
  (F : MarxFactorisation A f) →
  (x : Carrier A) →
  PreliminaryContinuousAtDiagonal R F x →
  (ordinary : OrdinaryDerivativeAt R f x) →
  marxDerivative F x ≡ linearCoefficient ordinary
marxDerivativeEqualsOrdinaryDerivative RemainderLaws uniqueness F x continuous ordinary =
  uniqueLinearCoefficient uniqueness
    (marxFactorisationAndDiagonalContinuityGiveOrdinaryDerivative
      _ RemainderLaws F x continuous)
    ordinary

------------------------------------------------------------------------
-- Compatibility package retained for downstream consumers, now carrying the
-- ingredients from which the theorem is derived rather than a direct equality
-- authority.

record MarxOrdinaryCompatibilityAuthority
  {A : MarxAlgebra}
  (R : RemainderDerivativeStructure A)
  : Set₁ where
  field
    expansionLaws : MarxRemainderExpansionLaws A
    derivativeUniqueness : OrdinaryDerivativeUniqueness R

open MarxOrdinaryCompatibilityAuthority public

marxDerivativeAgreesWithOrdinaryDerivative :
  {A : MarxAlgebra} →
  {R : RemainderDerivativeStructure A} →
  (authority : MarxOrdinaryCompatibilityAuthority R) →
  {f : Function A} →
  (F : MarxFactorisation A f) →
  (x : Carrier A) →
  ContinuousDiagonal R F x →
  (ordinary : OrdinaryDerivativeAt R f x) →
  marxDerivative F x ≡ linearCoefficient ordinary
marxDerivativeAgreesWithOrdinaryDerivative authority F x continuous ordinary =
  marxDerivativeEqualsOrdinaryDerivative
    (expansionLaws authority)
    (derivativeUniqueness authority)
    F x continuous ordinary

------------------------------------------------------------------------
-- Converse divided-difference extension.

record DividedDifferenceExtension
  (A : MarxAlgebra)
  (f : Function A)
  : Set₁ where
  field
    extendedPreliminary : Carrier A → Carrier A → Carrier A
    extensionFactorisation :
      ∀ x x₁ →
      functionDifference A f x x₁
      ≡ _*_ A
          (inputDifference A x x₁)
          (extendedPreliminary x x₁)

open DividedDifferenceExtension public

ordinaryDerivativeWithDividedDifferenceExtensionGivesMarxFactorisation :
  {A : MarxAlgebra} →
  {f : Function A} →
  DividedDifferenceExtension A f →
  MarxFactorisation A f
ordinaryDerivativeWithDividedDifferenceExtensionGivesMarxFactorisation extension =
  record
    { preliminary = extendedPreliminary extension
    ; finiteFactorisation = extensionFactorisation extension
    }

------------------------------------------------------------------------
-- Completion seam for the selected constructive-real implementation.

record ConstructiveRealDerivativeSeam : Set₂ where
  field
    algebra : MarxAlgebra
    remainderStructure : RemainderDerivativeStructure algebra
    expansionLaws : MarxRemainderExpansionLaws algebra
    uniqueness : OrdinaryDerivativeUniqueness remainderStructure

-- A concrete inhabitant still requires the selected quotient real's norm,
-- reciprocal normalization, punctured convergence and derivative uniqueness.
