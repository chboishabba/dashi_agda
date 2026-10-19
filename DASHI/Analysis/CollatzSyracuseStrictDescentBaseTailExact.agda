module DASHI.Analysis.CollatzSyracuseStrictDescentBaseTailExact where

------------------------------------------------------------------------
-- TERMINAL STRICT-DESCENT BASE/TAIL SPLIT
--
-- This follows the repository's mature max-cut discipline used in the NS/P
-- lanes: pay the generic compiler and a literal finite base in-kernel, while
-- leaving exactly one unbounded source-specific tail theorem visible.
--
-- Nothing in this file claims the tail theorem.  In particular, finite
-- computation, Bernoulli density, or the old 3z/(3z-1) spectral relation cannot
-- inhabit TailStrictDescentSource.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_<_; _≤_)
import Data.Nat.Properties as NatP
import Data.Product as Product
open Product using (Σ; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.Analysis.CollatzSyracuseUniversalStoppingCompilerExact as Universal

------------------------------------------------------------------------
-- Any literal iterate reaching one supplies strict descent for x > 1.
------------------------------------------------------------------------

strictDropFromReachOne :
  (x : Syracuse.PositiveNat) →
  (nontrivial : 1 < Syracuse.toNat x) →
  (k : Nat) →
  Syracuse.syracuseIterate k x ≡ Syracuse.one →
  Syracuse.toNat (Syracuse.syracuseIterate k x) < Syracuse.toNat x
strictDropFromReachOne x nontrivial k atOne =
  subst
    (λ value → value < Syracuse.toNat x)
    (sym (cong Syracuse.toNat atOne))
    nontrivial

------------------------------------------------------------------------
-- Literal finite base: 2,...,8 all reach one by normalization of the exact
-- Syracuse definition.  The x=1 branch is impossible under 1<x, and x>=9 is
-- impossible under x<=8.
------------------------------------------------------------------------

smallBaseDescend :
  (x : Syracuse.PositiveNat) →
  1 < Syracuse.toNat x →
  Syracuse.toNat x ≤ 8 →
  Σ Nat (λ k →
    Syracuse.toNat (Syracuse.syracuseIterate k x) < Syracuse.toNat x)
smallBaseDescend (Syracuse.positiveNat zero) () bound
smallBaseDescend x@(Syracuse.positiveNat (suc zero)) nontrivial bound =
  1 , strictDropFromReachOne x nontrivial 1 refl
smallBaseDescend x@(Syracuse.positiveNat (suc (suc zero))) nontrivial bound =
  5 , strictDropFromReachOne x nontrivial 5 refl
smallBaseDescend x@(Syracuse.positiveNat (suc (suc (suc zero)))) nontrivial bound =
  2 , strictDropFromReachOne x nontrivial 2 refl
smallBaseDescend x@(Syracuse.positiveNat (suc (suc (suc (suc zero))))) nontrivial bound =
  4 , strictDropFromReachOne x nontrivial 4 refl
smallBaseDescend x@(Syracuse.positiveNat (suc (suc (suc (suc (suc zero)))))) nontrivial bound =
  6 , strictDropFromReachOne x nontrivial 6 refl
smallBaseDescend x@(Syracuse.positiveNat (suc (suc (suc (suc (suc (suc zero))))))) nontrivial bound =
  11 , strictDropFromReachOne x nontrivial 11 refl
smallBaseDescend x@(Syracuse.positiveNat (suc (suc (suc (suc (suc (suc (suc zero)))))))) nontrivial bound =
  3 , strictDropFromReachOne x nontrivial 3 refl
smallBaseDescend
  (Syracuse.positiveNat
    (suc (suc (suc (suc (suc (suc (suc (suc n)))))))))
  nontrivial
  ()

------------------------------------------------------------------------
-- The only unbounded source-specific producer after paying the finite base.
------------------------------------------------------------------------

record TailStrictDescentAboveEightSource : Set₁ where
  field
    tailDescend :
      (x : Syracuse.PositiveNat) →
      8 ≤ Syracuse.toNat x →
      1 < Syracuse.toNat x →
      Σ Nat (λ k →
        Syracuse.toNat (Syracuse.syracuseIterate k x)
        < Syracuse.toNat x)

open TailStrictDescentAboveEightSource public

strictDescentFromBaseAndTail :
  TailStrictDescentAboveEightSource →
  Universal.LiteralStrictDescentSource
strictDescentFromBaseAndTail tail = record
  { Universal.descend = λ x nontrivial →
      case NatP.≤-total (Syracuse.toNat x) 8 of λ where
        (inj₁ x≤8) → smallBaseDescend x nontrivial x≤8
        (inj₂ eight≤x) → tailDescend tail x eight≤x nontrivial
  }
  where
    case : ∀ {a b : Set} → a → (a → b) → b
    case value f = f value

universalStoppingFromBaseAndTail :
  TailStrictDescentAboveEightSource →
  (x : Syracuse.PositiveNat) →
  Universal.ReachesOne x
universalStoppingFromBaseAndTail tail =
  Universal.universalStoppingFromStrictDescent
    (strictDescentFromBaseAndTail tail)

record StrictDescentBaseTailBoundary : Set where
  constructor strictDescentBaseTailBoundary
  field
    literalSmallBasePaid : Nat
    genericBaseTailCompilerPaid : Nat
    wellFoundedStoppingCompilerPaid : Nat
    finiteComputationCreatesTailTheorem : Nat
    BernoulliDensityCreatesTailTheorem : Nat
    tailAboveEightProducerPaid : Nat
    onlyUnboundedLeafIsTailProducer : Nat

canonicalStrictDescentBaseTailBoundary : StrictDescentBaseTailBoundary
canonicalStrictDescentBaseTailBoundary =
  strictDescentBaseTailBoundary 1 1 1 0 0 0 1
