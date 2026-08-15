module DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicNearTriadClassification as NearClass
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical

------------------------------------------------------------------------
-- Littlewood--Paley is the outer scale axis only.
--
-- The classifier is executable and uses an explicit overlap constant.  It
-- distinguishes low-high, high-low, high-high-to-low, and the remaining
-- comparable regime.  No phase, parity, orientation or polarisation claim is
-- folded into this scale classification.
------------------------------------------------------------------------

data ScaleRegime : Set where
  lowHigh highLow highHigh comparable : ScaleRegime

record PhysicalShellPolicy : Set₁ where
  constructor shell-policy
  field
    shellLevel : Z3.FourierMode → Nat
    overlapRadius : Nat

open PhysicalShellPolicy public

classifyScaleLevels :
  Nat → Nat → Nat → Nat → ScaleRegime
classifyScaleLevels overlapLevel jp jq jk
  with NearClass.natLess (jp + overlapLevel) jq
     | NearClass.natLess (jq + overlapLevel) jp
     | NearClass.natLess (jk + overlapLevel) jp
     | NearClass.natLess (jk + overlapLevel) jq
... | true  | hl    | kp    | kq    = lowHigh
... | false | true  | kp    | kq    = highLow
... | false | false | true  | true  = highHigh
... | false | false | true  | false = comparable
... | false | false | false | kq    = comparable

classifyScale :
  PhysicalShellPolicy →
  Physical.PhysicalTriadIncidence →
  ScaleRegime
classifyScale policy τ =
  classifyScaleLevels
    (overlapRadius policy)
    (shellLevel policy (Physical.p τ))
    (shellLevel policy (Physical.q τ))
    (shellLevel policy (Physical.k τ))

data ScaleCondition
    (policy : PhysicalShellPolicy)
    (τ : Physical.PhysicalTriadIncidence) :
    ScaleRegime → Set where
  lowHighCondition :
    NearClass.natLess
      (shellLevel policy (Physical.p τ) + overlapRadius policy)
      (shellLevel policy (Physical.q τ))
    ≡ true →
    ScaleCondition policy τ lowHigh

  highLowCondition :
    NearClass.natLess
      (shellLevel policy (Physical.p τ) + overlapRadius policy)
      (shellLevel policy (Physical.q τ))
    ≡ false →
    NearClass.natLess
      (shellLevel policy (Physical.q τ) + overlapRadius policy)
      (shellLevel policy (Physical.p τ))
    ≡ true →
    ScaleCondition policy τ highLow

  highHighCondition :
    NearClass.natLess
      (shellLevel policy (Physical.p τ) + overlapRadius policy)
      (shellLevel policy (Physical.q τ))
    ≡ false →
    NearClass.natLess
      (shellLevel policy (Physical.q τ) + overlapRadius policy)
      (shellLevel policy (Physical.p τ))
    ≡ false →
    NearClass.natLess
      (shellLevel policy (Physical.k τ) + overlapRadius policy)
      (shellLevel policy (Physical.p τ))
    ≡ true →
    NearClass.natLess
      (shellLevel policy (Physical.k τ) + overlapRadius policy)
      (shellLevel policy (Physical.q τ))
    ≡ true →
    ScaleCondition policy τ highHigh

  comparableCondition :
    NearClass.natLess
      (shellLevel policy (Physical.p τ) + overlapRadius policy)
      (shellLevel policy (Physical.q τ))
    ≡ false →
    NearClass.natLess
      (shellLevel policy (Physical.q τ) + overlapRadius policy)
      (shellLevel policy (Physical.p τ))
    ≡ false →
    (NearClass.natLess
      (shellLevel policy (Physical.k τ) + overlapRadius policy)
      (shellLevel policy (Physical.p τ))
      ≡ false
     ⊎
     NearClass.natLess
      (shellLevel policy (Physical.k τ) + overlapRadius policy)
      (shellLevel policy (Physical.q τ))
      ≡ false) →
    ScaleCondition policy τ comparable

scaleClassificationSound :
  ∀ policy τ →
  ScaleCondition policy τ (classifyScale policy τ)
scaleClassificationSound policy τ
  with NearClass.natLess
    (shellLevel policy (Physical.p τ) + overlapRadius policy)
    (shellLevel policy (Physical.q τ))
    in hProof
     | NearClass.natLess
    (shellLevel policy (Physical.q τ) + overlapRadius policy)
    (shellLevel policy (Physical.p τ))
    in pProof
     | NearClass.natLess
    (shellLevel policy (Physical.k τ) + overlapRadius policy)
    (shellLevel policy (Physical.p τ))
    in kpProof
     | NearClass.natLess
    (shellLevel policy (Physical.k τ) + overlapRadius policy)
    (shellLevel policy (Physical.q τ))
    in kqProof
... | true  | hl    | kp    | kq    = lowHighCondition hProof
... | false | true  | kp    | kq    = highLowCondition hProof pProof
... | false | false | true  | true  =
      highHighCondition hProof pProof kpProof kqProof
... | false | false | true  | false =
      comparableCondition hProof pProof (inj₂ kqProof)
... | false | false | false | kq    =
      comparableCondition hProof pProof (inj₁ kpProof)

scaleClassificationComplete :
  ∀ policy τ →
  Σ ScaleRegime (λ regime → ScaleCondition policy τ regime)
scaleClassificationComplete policy τ =
  classifyScale policy τ , scaleClassificationSound policy τ

scaleClassificationUnique :
  ∀ {policy τ first second} →
  classifyScale policy τ ≡ first →
  classifyScale policy τ ≡ second →
  first ≡ second
scaleClassificationUnique firstEquality secondEquality =
  trans (sym firstEquality) secondEquality

------------------------------------------------------------------------
-- The executable partition is not itself a shell-triangle theorem.  This
-- record is the exact bridge required to turn the computed regimes into
-- quantitative output-shell conclusions for a chosen norm and shell policy.
------------------------------------------------------------------------

record LittlewoodPaleyShellConsequences
    (policy : PhysicalShellPolicy) : Set₁ where
  field
    OutputComparableTo : Nat → Nat → Set

    lowHighOutputTracksQ :
      ∀ τ →
      ScaleCondition policy τ lowHigh →
      OutputComparableTo
        (shellLevel policy (Physical.k τ))
        (shellLevel policy (Physical.q τ))

    highLowOutputTracksP :
      ∀ τ →
      ScaleCondition policy τ highLow →
      OutputComparableTo
        (shellLevel policy (Physical.k τ))
        (shellLevel policy (Physical.p τ))

    highHighOutputBelowInputs :
      ∀ τ →
      ScaleCondition policy τ highHigh →
      NearClass.natLess
        (shellLevel policy (Physical.k τ) + overlapRadius policy)
        (shellLevel policy (Physical.p τ))
      ≡ true

    comparableHasNoSeparatedInput :
      ∀ τ →
      ScaleCondition policy τ comparable →
      NearClass.natLess
        (shellLevel policy (Physical.p τ) + overlapRadius policy)
        (shellLevel policy (Physical.q τ))
      ≡ false

open LittlewoodPaleyShellConsequences public

executablePhysicalScaleTrichotomyImplemented : Bool
executablePhysicalScaleTrichotomyImplemented = true

executablePhysicalScaleTrichotomyImplementedIsTrue :
  executablePhysicalScaleTrichotomyImplemented ≡ true
executablePhysicalScaleTrichotomyImplementedIsTrue = refl

shellTrichotomyCoverageImplemented : Bool
shellTrichotomyCoverageImplemented = true

shellTrichotomyCoverageImplementedIsTrue :
  shellTrichotomyCoverageImplemented ≡ true
shellTrichotomyCoverageImplementedIsTrue = refl

quantitativeShellConsequenceBridgeInhabited : Bool
quantitativeShellConsequenceBridgeInhabited = false

quantitativeShellConsequenceBridgeInhabitedIsFalse :
  quantitativeShellConsequenceBridgeInhabited ≡ false
quantitativeShellConsequenceBridgeInhabitedIsFalse = refl
