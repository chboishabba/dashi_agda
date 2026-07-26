module DASHI.Analysis.MarxHigherDerivativeConstruction where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Analysis.MarxDifferentialCore
open import DASHI.Analysis.MarxHigherCalculus

------------------------------------------------------------------------
-- Canonical construction of every finite derivative order in a derivative-
-- closed Marx family.

mutual
  canonicalDerivativeAtOrder :
    {A : MarxAlgebra} →
    (C : ClosedMarxDifferentialFamily A) →
    (f : Function A) →
    admissible C f →
    Nat →
    Function A
  canonicalDerivativeAtOrder C f pf zero = f
  canonicalDerivativeAtOrder C f pf (suc n) =
    familyDerivative C
      (canonicalDerivativeAtOrder C f pf n)
      (canonicalAdmissibleAtOrder C f pf n)

  canonicalAdmissibleAtOrder :
    {A : MarxAlgebra} →
    (C : ClosedMarxDifferentialFamily A) →
    (f : Function A) →
    (pf : admissible C f) →
    (n : Nat) →
    admissible C (canonicalDerivativeAtOrder C f pf n)
  canonicalAdmissibleAtOrder C f pf zero = pf
  canonicalAdmissibleAtOrder C f pf (suc n) =
    derivativeClosed C
      (canonicalDerivativeAtOrder C f pf n)
      (canonicalAdmissibleAtOrder C f pf n)

canonicalHigherDerivativeTower :
  {A : MarxAlgebra} →
  (C : ClosedMarxDifferentialFamily A) →
  (f : Function A) →
  (pf : admissible C f) →
  HigherDerivativeTower C f
canonicalHigherDerivativeTower C f pf =
  record
    { baseAdmissible = pf
    ; derivativeAtOrder = canonicalDerivativeAtOrder C f pf
    ; admissibleAtOrder = canonicalAdmissibleAtOrder C f pf
    ; orderZero = refl
    ; orderSuccessor = λ n → refl
    }

canonicalTaylorExpansionData :
  {A : MarxAlgebra} →
  {C : ClosedMarxDifferentialFamily A} →
  {f : Function A} →
  (tower : HigherDerivativeTower C f) →
  (T : TaylorCoefficientStructure A) →
  (centre : Carrier A) →
  TaylorExpansionData T
    (HigherDerivativeTower.derivativeAtOrder tower)
    centre
canonicalTaylorExpansionData tower T centre =
  record
    { coefficient = λ n →
        divide T
          (HigherDerivativeTower.derivativeAtOrder tower n centre)
          (factorial T n)
    ; coefficientLaw = λ n → refl
    }

higherDerivativeSuccessorLaw :
  {A : MarxAlgebra} →
  (C : ClosedMarxDifferentialFamily A) →
  (f : Function A) →
  (pf : admissible C f) →
  (n : Nat) →
  canonicalDerivativeAtOrder C f pf (suc n)
  ≡ familyDerivative C
      (canonicalDerivativeAtOrder C f pf n)
      (canonicalAdmissibleAtOrder C f pf n)
higherDerivativeSuccessorLaw C f pf n = refl
