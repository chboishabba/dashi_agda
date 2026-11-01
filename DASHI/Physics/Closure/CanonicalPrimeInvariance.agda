module DASHI.Physics.Closure.CanonicalPrimeInvariance where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Execution.Contract as EC
open import DASHI.Geometry.ShiftLorentzEmergenceInstance as SLEI
open import DASHI.Physics.Closure.CanonicalPrimeSelectionBridge
  using
    ( ShiftContractState
    ; shiftStep
    ; PrimeSelected
    ; canonicalPrimeWitness
    ; canonicalPrimeEmbeddingStepCoarse-commute
    )
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
  using (shiftCoarse)
open import DASHI.Physics.Closure.ShiftContractObservableTransportPrimeCompatibilityProfileInstance
  using (shiftContractObservablePrimeEmbedding)
open import MonsterOntos using (SSP)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.Hecke.MoonshinePrimeCarrierMatch
  using (CarrierBoundarySurface; factorVecSupportAt)

private
  ShiftC : EC.Contract
  ShiftC = SLEI.shiftContract {suc zero} {suc (suc (suc zero))}

PrimeSelectedOn : FactorVec → SSP → Set
PrimeSelectedOn v p =
  CarrierBoundarySurface.supportPrime (factorVecSupportAt v p) ≡ p

PrimeSupport : ShiftContractState → SSP → Set
PrimeSupport = PrimeSelected

SupportSub : ShiftContractState → ShiftContractState → Set
SupportSub x y = ∀ p → PrimeSupport y p → PrimeSupport x p

SupportEq : ShiftContractState → ShiftContractState → Set
SupportEq x y = SupportSub x y × SupportSub y x

primeSupportEq-from-primeEmbedding :
  ∀ {x y} →
  shiftContractObservablePrimeEmbedding x
    ≡
  shiftContractObservablePrimeEmbedding y
  →
  SupportEq x y
primeSupportEq-from-primeEmbedding {x} {y} emb≡ =
  ( λ p py →
      subst (λ v → PrimeSelectedOn v p) (sym emb≡) py
  )
  ,
  ( λ p px →
      subst (λ v → PrimeSelectedOn v p) emb≡ px
  )

primeSupport-coarse-step-transport :
  ∀ (x : ShiftContractState) →
  SupportEq (shiftCoarse (shiftStep x)) (shiftStep (shiftCoarse x))
primeSupport-coarse-step-transport x =
  primeSupportEq-from-primeEmbedding
    {x = shiftCoarse (shiftStep x)}
    {y = shiftStep (shiftCoarse x)}
    (canonicalPrimeEmbeddingStepCoarse-commute x)

PrimeExecutionAdmissible : Set
PrimeExecutionAdmissible = EC.Contract.ExecutionAdmissible ShiftC

primeSupport-no-growth :
  PrimeExecutionAdmissible →
  ∀ x →
  SupportSub x (shiftStep x)
primeSupport-no-growth _ x p _ = canonicalPrimeWitness x p

primeSupport-no-growth-target : Set
primeSupport-no-growth-target =
  PrimeExecutionAdmissible →
  ∀ x →
  SupportSub x (shiftStep x)

record CanonicalPrimeInvariance : Set₁ where
  field
    coarseStepTransport :
      ∀ x →
      SupportEq (shiftCoarse (shiftStep x)) (shiftStep (shiftCoarse x))
    noGrowth :
      PrimeExecutionAdmissible →
      ∀ x →
      SupportSub x (shiftStep x)
    noGrowthTarget : Set

canonicalPrimeInvariance : CanonicalPrimeInvariance
canonicalPrimeInvariance = record
  { coarseStepTransport = primeSupport-coarse-step-transport
  ; noGrowth = primeSupport-no-growth
  ; noGrowthTarget = primeSupport-no-growth-target
  }
