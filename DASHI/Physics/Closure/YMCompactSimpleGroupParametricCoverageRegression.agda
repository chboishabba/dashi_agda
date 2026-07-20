module DASHI.Physics.Closure.YMCompactSimpleGroupParametricCoverageRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ)

open import DASHI.Physics.Closure.YMCompactSimpleGroupParametricCoverage

su3GlobalForm : CompactSimpleGlobalForm
su3GlobalForm = globalForm (SU 3) 1

so5GlobalForm : CompactSimpleGlobalForm
so5GlobalForm = globalForm (SOodd 2) 2

sp2GlobalForm : CompactSimpleGlobalForm
sp2GlobalForm = globalForm (Sp 2) 1

e8AdjointGlobalForm : CompactSimpleGlobalForm
e8AdjointGlobalForm = globalForm E8 1

su3Package : QuantitativeCompactLiePackage su3GlobalForm
su3Package = compactSimpleHasQuantitativePackage su3GlobalForm

so5Package : QuantitativeCompactLiePackage so5GlobalForm
so5Package = compactSimpleHasQuantitativePackage so5GlobalForm

sp2Package : QuantitativeCompactLiePackage sp2GlobalForm
sp2Package = compactSimpleHasQuantitativePackage sp2GlobalForm

e8Package : QuantitativeCompactLiePackage e8AdjointGlobalForm
e8Package = compactSimpleHasQuantitativePackage e8AdjointGlobalForm

su3LatticeIndependence :
  (Λ k U₀ P : Nat) →
  LocalLieConstants su3GlobalForm (latticeDatum Λ k U₀ P)
    ≡ lambdaG su3Package
su3LatticeIndependence = localUniformBound su3Package

e8LatticeIndependence :
  (Λ k U₀ P : Nat) →
  LocalLieConstants e8AdjointGlobalForm (latticeDatum Λ k U₀ P)
    ≡ lambdaG e8Package
e8LatticeIndependence = localUniformBound e8Package

allClassicalFamiliesCovered :
  QuantitativeCompactLiePackage (globalForm (SU 4) 1)
  × QuantitativeCompactLiePackage (globalForm (SOodd 3) 1)
  × QuantitativeCompactLiePackage (globalForm (SOeven 4) 2)
  × QuantitativeCompactLiePackage (globalForm (Sp 3) 1)
allClassicalFamiliesCovered =
  compactSimpleHasQuantitativePackage (globalForm (SU 4) 1) ,
  compactSimpleHasQuantitativePackage (globalForm (SOodd 3) 1) ,
  compactSimpleHasQuantitativePackage (globalForm (SOeven 4) 2) ,
  compactSimpleHasQuantitativePackage (globalForm (Sp 3) 1)
  where
    infixr 4 _×_
    _×_ : Set → Set → Set
    A × B = Σ A (λ _ → B)

allExceptionalFamiliesCovered :
  QuantitativeCompactLiePackage (globalForm G2 1)
  × QuantitativeCompactLiePackage (globalForm F4 1)
  × QuantitativeCompactLiePackage (globalForm E6 1)
  × QuantitativeCompactLiePackage (globalForm E7 1)
  × QuantitativeCompactLiePackage (globalForm E8 1)
allExceptionalFamiliesCovered =
  compactSimpleHasQuantitativePackage (globalForm G2 1) ,
  compactSimpleHasQuantitativePackage (globalForm F4 1) ,
  compactSimpleHasQuantitativePackage (globalForm E6 1) ,
  compactSimpleHasQuantitativePackage (globalForm E7 1) ,
  compactSimpleHasQuantitativePackage (globalForm E8 1)
  where
    infixr 4 _×_
    _×_ : Set → Set → Set
    A × B = Σ A (λ _ → B)
