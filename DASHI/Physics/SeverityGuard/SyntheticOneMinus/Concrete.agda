module DASHI.Physics.SeverityGuard.SyntheticOneMinus.Concrete where

open import Agda.Builtin.Nat using (Nat)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat.Properties as NatP using (≤-refl)
open import UFTC_Lattice using (Code; Severity; normal; special)

open import DASHI.Physics.SeverityGuard.Core as SG
open import DASHI.Physics.Closure.Validation.SyntheticOneMinusDynamicsWitness as SOMDW

stateCardinality : Nat
stateCardinality =
  SOMDW.SyntheticOneMinusDynamicsWitness.stateCardinality
    SOMDW.syntheticDynamicsWitness

State : Set
State = Fin stateCardinality

codeᵒ : State → Code
codeᵒ zero = normal 0
codeᵒ (suc _) = special 4

safeThresholdᵒ : Severity
safeThresholdᵒ = 3

brokenThresholdᵒ : Severity
brokenThresholdᵒ = 4

policyᵒ : SG.SeverityPolicy State
policyᵒ =
  record
    { code = codeᵒ
    ; safeThreshold = safeThresholdᵒ
    ; brokenThreshold = brokenThresholdᵒ
    }

witnessState : State
witnessState = suc zero

witnessSnap : SG.Snap policyᵒ witnessState
witnessSnap = NatP.≤-refl
