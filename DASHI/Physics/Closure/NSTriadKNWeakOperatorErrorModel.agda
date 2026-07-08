module DASHI.Physics.Closure.NSTriadKNWeakOperatorErrorModel where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Nat using (_≤_)

import DASHI.Physics.Closure.NSTriadKNPairIncidenceCNTheorem as CNTheorem
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm

------------------------------------------------------------------------
-- Weak-side operator error model.
--
-- This is the first concrete Blocker 2 theorem surface after PairIncidence C/N:
-- package a candidate weak quadratic error functional together with the exact
-- weak-side O(N^-1) inequality it must satisfy.

record WeakOperatorErrorModel (Carrier : Set) : Set₁ where
  constructor mkWeakOperatorErrorModel
  field
    weakNormSquared : Carrier → Nat
    weakError : Carrier → Nat
    weakErrorConstant : Nat

    pairIncidenceCNWitness :
      CNTheorem.pairIncidenceCNTheoremClosed ≡ true
    operatorWeakCN : Set

    weakErrorModelClosed : Bool

record WeakOperatorErrorModelTarget : Set₁ where
  constructor mkWeakOperatorErrorModelTarget
  field
    residueNormModel : ResidueNorm.ResidueNormModel
    shellIndex : Nat

    pairIncidenceCNWitness :
      CNTheorem.pairIncidenceCNTheoremClosed ≡ true

    weakError :
      ResidueNorm.Carrier residueNormModel shellIndex → Nat

    weakErrorConstant : Nat

    targetClosed : Bool

weakErrorCarrier :
  (target : WeakOperatorErrorModelTarget) → Set
weakErrorCarrier target =
  ResidueNorm.Carrier
    (WeakOperatorErrorModelTarget.residueNormModel target)
    (WeakOperatorErrorModelTarget.shellIndex target)

operatorWeakCNTarget :
  (target : WeakOperatorErrorModelTarget) → Set
operatorWeakCNTarget target =
  (x : weakErrorCarrier target) →
  WeakOperatorErrorModelTarget.shellIndex target
    * WeakOperatorErrorModelTarget.weakError target x
    ≤
    WeakOperatorErrorModelTarget.weakErrorConstant target
      *
      ResidueNorm.weakNormSquared
        (WeakOperatorErrorModelTarget.residueNormModel target)
        (WeakOperatorErrorModelTarget.shellIndex target)
        x

toWeakOperatorErrorModel :
  (target : WeakOperatorErrorModelTarget) →
  WeakOperatorErrorModel (weakErrorCarrier target)
toWeakOperatorErrorModel target =
  mkWeakOperatorErrorModel
    (λ x →
      ResidueNorm.weakNormSquared
        (WeakOperatorErrorModelTarget.residueNormModel target)
        (WeakOperatorErrorModelTarget.shellIndex target)
        x)
    (WeakOperatorErrorModelTarget.weakError target)
    (WeakOperatorErrorModelTarget.weakErrorConstant target)
    (WeakOperatorErrorModelTarget.pairIncidenceCNWitness target)
    (operatorWeakCNTarget target)
    (WeakOperatorErrorModelTarget.targetClosed target)
