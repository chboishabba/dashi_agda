module DASHI.Physics.Closure.CanonicalPrimeConcentration where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Execution.Contract as EC
open import DASHI.Geometry.ShiftLorentzEmergenceInstance as SLEI
open import DASHI.Physics.Closure.CanonicalPrimeSelectionBridge
  using
    ( ShiftContractState
    ; shiftStep
    ; PrimeSelected
    ; canonicalPrimeEmbeddingStepCoarse-commute
    )
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
  using (shiftCoarse)
open import DASHI.Physics.Closure.ShiftContractObservableTransportPrimeCompatibilityProfileInstance
  using (shiftContractObservablePrimeEmbedding)
open import MonsterOntos using (SSP)
open import Ontology.Hecke.MoonshinePrimeCarrierMatch
  using (CarrierBoundarySurface; factorVecSupportAt)

private
  ShiftC : EC.Contract
  ShiftC = SLEI.shiftContract {suc zero} {suc (suc (suc zero))}

PrimeWeight : ShiftContractState → SSP → Nat
PrimeWeight x p =
  CarrierBoundarySurface.supportValue
    (factorVecSupportAt (shiftContractObservablePrimeEmbedding x) p)

PrimeDominates : ShiftContractState → SSP → Set
PrimeDominates x p =
  ∀ q → PrimeWeight x q ≤ PrimeWeight x p

PrimeConcentrated : ShiftContractState → SSP → Set
PrimeConcentrated x p =
  PrimeSelected x p × PrimeDominates x p

primeWeightEq-from-primeEmbedding :
  ∀ {x y p} →
  shiftContractObservablePrimeEmbedding x
    ≡
  shiftContractObservablePrimeEmbedding y
  →
  PrimeWeight x p ≡ PrimeWeight y p
primeWeightEq-from-primeEmbedding {x} {y} {p} emb≡ =
  cong
    (λ v → CarrierBoundarySurface.supportValue (factorVecSupportAt v p))
    emb≡

primeWeight-coarse-step-transport :
  ∀ (x : ShiftContractState) (p : SSP) →
  PrimeWeight (shiftCoarse (shiftStep x)) p
    ≡
  PrimeWeight (shiftStep (shiftCoarse x)) p
primeWeight-coarse-step-transport x p =
  primeWeightEq-from-primeEmbedding
    {x = shiftCoarse (shiftStep x)}
    {y = shiftStep (shiftCoarse x)}
    {p = p}
    (canonicalPrimeEmbeddingStepCoarse-commute x)

postulate
  primeDominates-coarse-step-transport :
    ∀ x p →
    PrimeDominates (shiftCoarse (shiftStep x)) p
      →
    PrimeDominates (shiftStep (shiftCoarse x)) p

  primeConcentration-exists-target :
    ∀ x →
    Σ SSP (PrimeConcentrated x)

  primeConcentration-no-loss-target :
    EC.Contract.ExecutionAdmissible ShiftC
      →
    ∀ x p →
    PrimeConcentrated (shiftStep x) p
      →
    PrimeConcentrated x p

record CanonicalPrimeConcentration : Set₁ where
  field
    weight : ShiftContractState → SSP → Nat
    dominates : ShiftContractState → SSP → Set
    concentrated : ShiftContractState → SSP → Set
    weightStepCoarse :
      ∀ x p →
      weight (shiftCoarse (shiftStep x)) p
        ≡
      weight (shiftStep (shiftCoarse x)) p
    existenceTarget : Set
    noLossTarget : Set

canonicalPrimeConcentration : CanonicalPrimeConcentration
canonicalPrimeConcentration = record
  { weight = PrimeWeight
  ; dominates = PrimeDominates
  ; concentrated = PrimeConcentrated
  ; weightStepCoarse = primeWeight-coarse-step-transport
  ; existenceTarget = ∀ x → Σ SSP (PrimeConcentrated x)
  ; noLossTarget =
      EC.Contract.ExecutionAdmissible ShiftC
        →
      ∀ x p →
      PrimeConcentrated (shiftStep x) p
        →
      PrimeConcentrated x p
  }
