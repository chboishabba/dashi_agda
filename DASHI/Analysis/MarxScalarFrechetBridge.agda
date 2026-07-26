module DASHI.Analysis.MarxScalarFrechetBridge where

open import Agda.Primitive using (Set₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import DASHI.Analysis.MarxDifferentialCore
open import DASHI.Analysis.MarxPowerRuleNormalisation
open import DASHI.Analysis.MarxOrdinaryDerivativeBridge
open import DASHI.Analysis.MarxHigherCalculus

------------------------------------------------------------------------
-- The scalar carrier as a one-dimensional module over itself.

record MarxScalarModuleLaws
  (A : MarxAlgebra)
  : Set₁ where
  field
    powerLaws : MarxPowerAlgebraLaws A
    distribLeftLaw :
      ∀ scalar u v →
      _*_ A scalar (_+_ A u v)
      ≡ _+_ A (_*_ A scalar u) (_*_ A scalar v)

open MarxScalarModuleLaws public

scalarModule :
  {A : MarxAlgebra} →
  MarxScalarModuleLaws A →
  Module A
scalarModule {A} L =
  record
    { Vector = Carrier A
    ; zeroV = zero A
    ; _+V_ = _+_ A
    ; _•_ = _*_ A
    ; addZeroLeftV = addZeroLeftLaw (powerLaws L)
    ; addZeroRightV = addZeroRightLaw (powerLaws L)
    ; addAssocV = addAssocLaw (powerLaws L)
    ; scaleZeroV = mulZeroRight A
    ; scaleOneV = mulOneLeft (powerLaws L)
    ; scaleDistributesAddV = distribLeftLaw L
    }

coefficientLinearMap :
  {A : MarxAlgebra} →
  (L : MarxScalarModuleLaws A) →
  Carrier A →
  LinearMap A (scalarModule L) (scalarModule L)
coefficientLinearMap {A} L coefficient =
  record
    { apply = λ h → _*_ A coefficient h
    ; mapZero = mulZeroRight A coefficient
    ; mapAdd = distribLeftLaw L coefficient
    ; mapScale = λ scalar h →
        trans
          (sym (mulAssoc A coefficient scalar h))
          (trans
            (cong (λ left → _*_ A left h)
              (mulCommLaw (powerLaws L) coefficient scalar))
            (mulAssoc A scalar coefficient h))
    }

------------------------------------------------------------------------
-- Ordinary scalar remainder data and vector little-o are intentionally linked
-- by an explicit compatibility receipt.  This avoids silently identifying two
-- independently chosen convergence predicates.

record ScalarFrechetCompatibility
  {A : MarxAlgebra}
  (L : MarxScalarModuleLaws A)
  (R : RemainderDerivativeStructure A)
  (vectorLittleO :
    VectorLittleOStructure A (scalarModule L) (scalarModule L))
  : Set₁ where
  field
    ordinaryLittleOImpliesVectorLittleO :
      ∀ remainder →
      NormalizedRemainderVanishes R remainder →
      LittleO vectorLittleO remainder

    vectorLittleOImpliesOrdinaryLittleO :
      ∀ remainder →
      LittleO vectorLittleO remainder →
      NormalizedRemainderVanishes R remainder

open ScalarFrechetCompatibility public

ordinaryDerivativeToFrechetDerivative :
  {A : MarxAlgebra} →
  (L : MarxScalarModuleLaws A) →
  (R : RemainderDerivativeStructure A) →
  (vectorLittleO :
    VectorLittleOStructure A (scalarModule L) (scalarModule L)) →
  (compatibility : ScalarFrechetCompatibility L R vectorLittleO) →
  {f : Function A} →
  {x : Carrier A} →
  OrdinaryDerivativeAt R f x →
  FrechetDerivativeAt vectorLittleO f x
ordinaryDerivativeToFrechetDerivative L R vectorLittleO compatibility ordinary =
  record
    { derivative = coefficientLinearMap L (linearCoefficient ordinary)
    ; remainder = remainder ordinary
    ; expansion = expansion ordinary
    ; remainderLittleO =
        ordinaryLittleOImpliesVectorLittleO compatibility
          (remainder ordinary)
          (normalizedRemainderVanishes ordinary)
    }

frechetDerivativeToOrdinaryDerivative :
  {A : MarxAlgebra} →
  (L : MarxScalarModuleLaws A) →
  (R : RemainderDerivativeStructure A) →
  (vectorLittleO :
    VectorLittleOStructure A (scalarModule L) (scalarModule L)) →
  (compatibility : ScalarFrechetCompatibility L R vectorLittleO) →
  {f : Function A} →
  {x : Carrier A} →
  (coefficient : Carrier A) →
  (F : FrechetDerivativeAt vectorLittleO f x) →
  derivative F ≡ coefficientLinearMap L coefficient →
  OrdinaryDerivativeAt R f x
frechetDerivativeToOrdinaryDerivative L R vectorLittleO compatibility coefficient F derivativeIsCoefficient =
  record
    { linearCoefficient = coefficient
    ; remainder = remainder F
    ; expansion = λ h →
        trans
          (expansion F h)
          (cong
            (λ linearTerm →
              _+_ _ (f _) (_+_ _ linearTerm (remainder F h)))
            (cong (λ map → apply map h) derivativeIsCoefficient))
    ; normalizedRemainderVanishes =
        vectorLittleOImpliesOrdinaryLittleO compatibility
          (remainder F)
          (remainderLittleO F)
    }

------------------------------------------------------------------------
-- Direct Marx-to-Frechet bridge via the proved ordinary compatibility theorem.

marxDerivativeToFrechetDerivative :
  {A : MarxAlgebra} →
  (L : MarxScalarModuleLaws A) →
  (R : RemainderDerivativeStructure A) →
  (vectorLittleO :
    VectorLittleOStructure A (scalarModule L) (scalarModule L)) →
  (compatibility : ScalarFrechetCompatibility L R vectorLittleO) →
  (rearrangement : MarxRemainderExpansionLaws A) →
  {f : Function A} →
  (F : MarxFactorisation A f) →
  (x : Carrier A) →
  PreliminaryContinuousAtDiagonal R F x →
  FrechetDerivativeAt vectorLittleO f x
marxDerivativeToFrechetDerivative L R vectorLittleO compatibility rearrangement F x continuous =
  ordinaryDerivativeToFrechetDerivative
    L R vectorLittleO compatibility
    (marxFactorisationAndDiagonalContinuityGiveOrdinaryDerivative
      R rearrangement F x continuous)
