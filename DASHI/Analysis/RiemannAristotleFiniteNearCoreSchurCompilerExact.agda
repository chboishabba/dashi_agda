module DASHI.Analysis.RiemannAristotleFiniteNearCoreSchurCompilerExact where

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP

record FiniteNearCoreSchurPerturbation : Set where
  constructor finite-near-core-schur-perturbation
  field
    cutoff : Nat
    offSchurSq nearSchurSq farErrorSq clusterMargin : ℚ
    perturbationBound :
      offSchurSq ≤ ((+ 2 / 1) * nearSchurSq) + ((+ 2 / 1) * farErrorSq)
    finiteNearPlusFarBelowCluster :
      ((+ 2 / 1) * nearSchurSq) + ((+ 2 / 1) * farErrorSq) < clusterMargin

open FiniteNearCoreSchurPerturbation public

offSchurStrictlyBelowCluster :
  (d : FiniteNearCoreSchurPerturbation) → offSchurSq d < clusterMargin d
offSchurStrictlyBelowCluster d =
  ℚP.≤-<-trans (perturbationBound d) (finiteNearPlusFarBelowCluster d)

finiteNearCoreContradictsExactSchur :
  (d : FiniteNearCoreSchurPerturbation) →
  clusterMargin d ≡ offSchurSq d → ⊥
finiteNearCoreContradictsExactSchur d exactSchur =
  ℚP.<-irrefl refl
    (subst (λ x → x < clusterMargin d) (sym exactSchur) (offSchurStrictlyBelowCluster d))
  where
    open import Relation.Binary.PropositionalEquality using (subst; sym)

record FiniteNearCoreAllowance : Set where
  constructor finite-near-core-allowance
  field
    cutoff : Nat
    nearSchurSq farErrorSq nearAllowance farAllowance clusterMargin : ℚ
    nearBound : nearSchurSq ≤ nearAllowance
    farBound : farErrorSq ≤ farAllowance
    weightedActualsBelowAllowances :
      ((+ 2 / 1) * nearSchurSq) + ((+ 2 / 1) * farErrorSq)
        ≤ ((+ 2 / 1) * nearAllowance) + ((+ 2 / 1) * farAllowance)
    weightedAllowancesBelowCluster :
      ((+ 2 / 1) * nearAllowance) + ((+ 2 / 1) * farAllowance) < clusterMargin

open FiniteNearCoreAllowance public

weightedActualsBelowCluster :
  (d : FiniteNearCoreAllowance) →
  ((+ 2 / 1) * nearSchurSq d) + ((+ 2 / 1) * farErrorSq d) < clusterMargin d
weightedActualsBelowCluster d =
  ℚP.≤-<-trans (weightedActualsBelowAllowances d) (weightedAllowancesBelowCluster d)

record FiniteNearCoreSchurBoundary : Set where
  constructor finite-near-core-schur-boundary
  field
    literalFiniteNearCarrierClosedInLean : Bool
    literalFiniteNearCarrierClosedInLeanIsTrue : literalFiniteNearCarrierClosedInLean ≡ true
    explicitFarRemainderClosedInLean : Bool
    explicitFarRemainderClosedInLeanIsTrue : explicitFarRemainderClosedInLean ≡ true
    scalarPerturbationConsumerClosedInAgda : Bool
    scalarPerturbationConsumerClosedInAgdaIsTrue : scalarPerturbationConsumerClosedInAgda ≡ true
    finiteNearSchurCancellationClosed : Bool
    finiteNearSchurCancellationClosedIsFalse : finiteNearSchurCancellationClosed ≡ false

canonicalFiniteNearCoreSchurBoundary : FiniteNearCoreSchurBoundary
canonicalFiniteNearCoreSchurBoundary =
  finite-near-core-schur-boundary true refl true refl true refl false refl
