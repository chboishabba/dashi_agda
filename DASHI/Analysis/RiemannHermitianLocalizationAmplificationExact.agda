module DASHI.Analysis.RiemannHermitianLocalizationAmplificationExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Exact endgame algebra for the two quantitative ways to cross a nonzero
-- arithmetic error floor: localize one off-line pair, or amplify its positive
-- Hermitian defect before comparison with the prime-side error.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Data.Empty using (⊥)

selfPlusPositiveImpossible :
  (n extra : Nat) → n + suc extra ≡ n → ⊥
selfPlusPositiveImpossible zero extra ()
selfPlusPositiveImpossible (suc n) extra refl =
  selfPlusPositiveImpossible n extra refl

record LocalizedPairLedger : Set where
  constructor localizedPairLedger
  field
    pairDefect : Nat
    leakage : Nat
    localizedSignal : Nat
    localArithmeticError : Nat
    localizationIdentity : pairDefect + leakage ≡ localizedSignal

open LocalizedPairLedger public

record LocalizedDetectability (l : LocalizedPairLedger) : Set where
  constructor localizedDetectability
  field
    gapPredecessor : Nat
    pairBeatsLocalError :
      localArithmeticError l + suc gapPredecessor ≡ pairDefect l
    localizedBoundSlack : Nat
    localizedWithinError :
      localizedSignal l + localizedBoundSlack ≡ localArithmeticError l

record LocalizationProducer : Set₁ where
  field
    ZeroPair : Set
    Window : Set
    targetWindow : ZeroPair → Window
    localizedPairLedger : ZeroPair → LocalizedPairLedger
    leakageEstimate : ZeroPair → Set
    sourceLocalPrimeBound : ZeroPair → Set

record AmplificationDetectabilityLedger : Set where
  constructor amplificationDetectabilityLedger
  field
    basePairDefect : Nat
    amplificationResidual : Nat
    amplifiedPairDefect : Nat
    higherMomentErrorBudget : Nat
    amplificationIdentity :
      basePairDefect + amplificationResidual ≡ amplifiedPairDefect

open AmplificationDetectabilityLedger public

record AmplifiedDetectability
  (a : AmplificationDetectabilityLedger) : Set where
  constructor amplifiedDetectability
  field
    gapPredecessor : Nat
    amplifiedBeatsError :
      higherMomentErrorBudget a + suc gapPredecessor ≡ amplifiedPairDefect a

record HigherMomentLocalizationProducer : Set₁ where
  field
    ZeroPair : Set
    MomentLevel : Set
    amplifiedLedger : ZeroPair → MomentLevel → AmplificationDetectabilityLedger
    analyticPowerIdentification : ZeroPair → MomentLevel → Set
    primeSideHigherTraceBound : ZeroPair → MomentLevel → Set

record LocalizationAmplificationBoundary : Set where
  field
    localizationLedgerConstructed : Bool
    amplificationDetectabilityLedgerConstructed : Bool
    leakageAndErrorSocketsConstructed : Bool
    higherMomentPrimeSocketConstructed : Bool
    actualZetaLocalizationProvedHere : Bool
    actualZetaHigherTraceBoundProvedHere : Bool
    rhDetectabilityClosedHere : Bool

localizationAmplificationBoundary : LocalizationAmplificationBoundary
localizationAmplificationBoundary = record
  { localizationLedgerConstructed = true
  ; amplificationDetectabilityLedgerConstructed = true
  ; leakageAndErrorSocketsConstructed = true
  ; higherMomentPrimeSocketConstructed = true
  ; actualZetaLocalizationProvedHere = false
  ; actualZetaHigherTraceBoundProvedHere = false
  ; rhDetectabilityClosedHere = false
  }
