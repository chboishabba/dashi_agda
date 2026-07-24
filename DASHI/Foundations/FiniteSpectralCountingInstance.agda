module DASHI.Foundations.FiniteSpectralCountingInstance where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_≤_)

open import DASHI.Foundations.SpectralCountingComplexity

------------------------------------------------------------------------
-- Concrete finite spectral accounting for a three-mode operator.  This is not a
-- Weyl asymptotic theorem; it exercises the discrete/continuous/remainder split
-- on an exact finite spectrum where continuous and residual masses vanish.

natSpectralScalar : SpectralScalar
natSpectralScalar =
  record
    { Scalar = Nat
    ; zero = zero
    ; one = suc zero
    ; add = _+_
    ; mul = _*_
    ; log = λ n → n
    ; LessEqual = _≤_
    }

data ThreeCutoff : Set where
  belowAll : ThreeCutoff
  firstMode : ThreeCutoff
  secondMode : ThreeCutoff
  allModes : ThreeCutoff

finiteDiscreteCount : ThreeCutoff → Nat
finiteDiscreteCount belowAll = zero
finiteDiscreteCount firstMode = suc zero
finiteDiscreteCount secondMode = suc (suc zero)
finiteDiscreteCount allModes = suc (suc (suc zero))

finiteSpectralCountingPackage :
  SpectralCountingPackage ThreeCutoff natSpectralScalar
finiteSpectralCountingPackage =
  record
    { cutoff = allModes
    ; discreteCount = finiteDiscreteCount
    ; discreteMass = finiteDiscreteCount
    ; continuousMass = λ _ → zero
    ; residualMass = λ _ → zero
    ; totalSpectralMass = finiteDiscreteCount
    ; principalWeylTerm = finiteDiscreteCount
    ; countingDecomposition = decomposition
    ; principalPlusRemainder = principal
    }
  where
    decomposition :
      ∀ cutoff →
      finiteDiscreteCount cutoff
      ≡ finiteDiscreteCount cutoff + (zero + zero)
    decomposition belowAll = refl
    decomposition firstMode = refl
    decomposition secondMode = refl
    decomposition allModes = refl

    principal :
      ∀ cutoff →
      finiteDiscreteCount cutoff
      ≡ finiteDiscreteCount cutoff + zero
    principal belowAll = refl
    principal firstMode = refl
    principal secondMode = refl
    principal allModes = refl

finiteMDLBudget :
  SpectralMDLComplexityBudget finiteSpectralCountingPackage
finiteMDLBudget =
  record
    { countAsScalar = λ n → n
    ; descriptionComplexity = finiteDiscreteCount
    ; geometryCorrection = λ _ → zero
    ; complexityFromSpectralCardinality = complexity
    }
  where
    complexity :
      ∀ cutoff →
      finiteDiscreteCount cutoff
      ≡ finiteDiscreteCount cutoff + zero
    complexity belowAll = refl
    complexity firstMode = refl
    complexity secondMode = refl
    complexity allModes = refl
