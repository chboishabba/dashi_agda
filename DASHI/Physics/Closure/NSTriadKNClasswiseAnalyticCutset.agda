module DASHI.Physics.Closure.NSTriadKNClasswiseAnalyticCutset where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as Nat

------------------------------------------------------------------------
-- Exact analytic leaf cutset.
--
-- Each class field names the mechanism that must be proved. The assembly of
-- those four estimates into one cutoff-uniform error constant is constructive.
------------------------------------------------------------------------

record ConcreteClassConstants {c s : Level} : Set (lsuc (c ⊔ s)) where
  field
    Cutoff : Set c
    State : Set s

    scaleSquare : Cutoff → Nat
    strongNormSquared : Cutoff → State → Nat

    forcedTailForm transitionForm adversarialForm residualForm :
      Cutoff → State → Nat

    forcedTailConstant transitionConstant adversarialConstant residualConstant :
      Nat

    forcedTailScaleRatioEstimate :
      ∀ N x →
      scaleSquare N * forcedTailForm N x
      ≤ forcedTailConstant * strongNormSquared N x

    transitionCancellationEstimate :
      ∀ N x →
      scaleSquare N * transitionForm N x
      ≤ transitionConstant * strongNormSquared N x

    adversarialNullGainEstimate :
      ∀ N x →
      scaleSquare N * adversarialForm N x
      ≤ adversarialConstant * strongNormSquared N x

    residualDominationEstimate :
      ∀ N x →
      scaleSquare N * residualForm N x
      ≤ residualConstant * strongNormSquared N x

open ConcreteClassConstants public

totalErrorForm :
  ∀ {c s} (C : ConcreteClassConstants {c} {s}) →
  Cutoff C → State C → Nat
totalErrorForm C N x =
  forcedTailForm C N x
  + (transitionForm C N x
  + (adversarialForm C N x
  + residualForm C N x))

totalErrorConstant :
  ∀ {c s} → ConcreteClassConstants {c} {s} → Nat
totalErrorConstant C =
  forcedTailConstant C
  + (transitionConstant C
  + (adversarialConstant C
  + residualConstant C))

totalClasswiseBound :
  ∀ {c s}
    (C : ConcreteClassConstants {c} {s})
    (N : Cutoff C)
    (x : State C) →
  scaleSquare C N * totalErrorForm C N x
  ≤ totalErrorConstant C * strongNormSquared C N x
totalClasswiseBound C N x
  rewrite Nat.*-distribˡ-+
    (scaleSquare C N)
    (forcedTailForm C N x)
    (transitionForm C N x
      + (adversarialForm C N x + residualForm C N x))
        | Nat.*-distribˡ-+
    (scaleSquare C N)
    (transitionForm C N x)
    (adversarialForm C N x + residualForm C N x)
        | Nat.*-distribˡ-+
    (scaleSquare C N)
    (adversarialForm C N x)
    (residualForm C N x)
        | Nat.*-distribʳ-+
    (forcedTailConstant C)
    (transitionConstant C
      + (adversarialConstant C + residualConstant C))
    (strongNormSquared C N x)
        | Nat.*-distribʳ-+
    (transitionConstant C)
    (adversarialConstant C + residualConstant C)
    (strongNormSquared C N x)
        | Nat.*-distribʳ-+
    (adversarialConstant C)
    (residualConstant C)
    (strongNormSquared C N x)
  =
  Nat.+-mono-≤
    (forcedTailScaleRatioEstimate C N x)
    (Nat.+-mono-≤
      (transitionCancellationEstimate C N x)
      (Nat.+-mono-≤
        (adversarialNullGainEstimate C N x)
        (residualDominationEstimate C N x)))

record StrictClasswiseGap
    {c s : Level}
    (C : ConcreteClassConstants {c} {s}) :
    Set (lsuc (c ⊔ s)) where
  field
    baseConstant : Nat
    baseForm : Cutoff C → State C → Nat

    baseCoercive :
      ∀ N x →
      baseConstant * strongNormSquared C N x
      ≤ scaleSquare C N * baseForm N x

    errorStrictlyBelowBase :
      totalErrorConstant C < baseConstant

open StrictClasswiseGap public

classwiseAssemblyClosed : Bool
classwiseAssemblyClosed = true

classwiseAssemblyClosedIsTrue : classwiseAssemblyClosed ≡ true
classwiseAssemblyClosedIsTrue = refl
