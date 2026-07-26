module DASHI.Analysis.MarxFiniteExteriorComplex where

open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import DASHI.Analysis.MarxDifferentialCore
open import DASHI.Analysis.MarxPowerRuleNormalisation
open import DASHI.Analysis.MarxScalarFrechetBridge
open import DASHI.Analysis.MarxFiniteVectorSpace
open import DASHI.Analysis.MarxExteriorIntegration

------------------------------------------------------------------------
-- Concrete zero form on a finite coordinate module.

zeroAlternatingMap :
  {A : MarxAlgebra} →
  (L : MarxScalarModuleLaws A) →
  (n degree : Nat) →
  AlternatingMultilinearMap A (finiteVectorModule L n) degree
zeroAlternatingMap {A} L n degree =
  record
    { evaluate = λ _ → zero A
    ; acceptedArity = λ _ → ⊤
    ; multilinearAdd = λ _ _ _ _ _ →
        sym
          (MarxPowerAlgebraLaws.addZeroLeftLaw
            (MarxScalarModuleLaws.powerLaws L)
            (zero A))
    ; multilinearScale = λ _ _ scalar _ _ →
        sym (mulZeroRight A scalar)
    ; alternatingAdjacent = λ _ _ _ _ → refl
    }

finiteGradedForms :
  {A : MarxAlgebra} →
  (L : MarxScalarModuleLaws A) →
  (n : Nat) →
  GradedDifferentialForms A (finiteVectorModule L n)
finiteGradedForms L n =
  record
    { Form = λ degree →
        AlternatingMultilinearMap _ (finiteVectorModule L n) degree
    ; zeroForm = zeroAlternatingMap L n
    ; asAlternatingMap = λ form → form
    }

finiteZeroExteriorDerivative :
  {A : MarxAlgebra} →
  (L : MarxScalarModuleLaws A) →
  (n : Nat) →
  ExteriorDerivative (finiteGradedForms L n)
finiteZeroExteriorDerivative L n =
  zeroExteriorDerivative (finiteGradedForms L n)

finiteExteriorDerivativeSquaredZero :
  {A : MarxAlgebra} →
  (L : MarxScalarModuleLaws A) →
  (n degree : Nat) →
  (omega : GradedDifferentialForms.Form (finiteGradedForms L n) degree) →
  ExteriorDerivative.d (finiteZeroExteriorDerivative L n)
    (ExteriorDerivative.d (finiteZeroExteriorDerivative L n) omega)
  ≡ GradedDifferentialForms.zeroForm
      (finiteGradedForms L n)
      (suc (suc degree))
finiteExteriorDerivativeSquaredZero L n degree omega =
  exteriorDerivativeSquaredZero
    (finiteZeroExteriorDerivative L n)
    omega

-- This is a concrete cochain complex over every finite coordinate module.  It
-- does not claim to be the de Rham complex; a nontrivial coordinate/discrete
-- exterior derivative remains a separate inhabitant of the same exact d²=0
-- interface.
