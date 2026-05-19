module DASHI.Physics.Closure.CanonicalPrimeSelectionBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Execution.Contract as EC
open import DASHI.Geometry.ShiftLorentzEmergenceInstance as SLEI
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
  using
    ( canonicalShiftHeckeState
    ; shiftCoarse
    ; shiftCoarseStep-commute
    ; shiftPrimeEmbedding
    ; shiftRGConeWitness
    ; shiftConeTransportCoarse
    ; shiftConeTransportStep
    )
open import DASHI.Physics.Closure.ShiftContractObservableTransportPrimeCompatibilityProfileInstance as SCOT
  using
    ( signatureOnGeo
    ; eigenOnGeo
    ; shiftContractObservablePrimeEmbedding
    ; shiftContractObservableChamberToShiftWitnessBridge
    ; shiftContractObservableIllegalCount≤forcedStableCountHist
    )
open import MonsterOntos using
  (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.Hecke.ChamberToShiftWitnessBridge as CTSW
open import Ontology.Hecke.Scan as HS using (Sig15)
open import Ontology.Hecke.PrimeHeckeEigenMotifPipeline as PHEM using (EigenProfile)
open import Ontology.Hecke.MoonshinePrimeCarrierMatch
  using (CarrierBoundarySurface; factorVecSupportAt)

private
  ShiftC : EC.Contract
  ShiftC = SLEI.shiftContract {suc zero} {suc (suc (suc zero))}

ShiftContractState : Set
ShiftContractState = EC.Contract.State ShiftC

shiftStep : ShiftContractState → ShiftContractState
shiftStep = EC.Contract.step ShiftC

------------------------------------------------------------------------
-- Concrete witnesses already available on the current closure pipeline.

PrimeSelected : ShiftContractState → SSP → Set
PrimeSelected x p =
  CarrierBoundarySurface.supportPrime
    (factorVecSupportAt (shiftContractObservablePrimeEmbedding x) p)
    ≡
  p

primeSelectedWitness : ∀ x p → PrimeSelected x p
primeSelectedWitness x p with p
... | p2  = refl
... | p3  = refl
... | p5  = refl
... | p7  = refl
... | p11 = refl
... | p13 = refl
... | p17 = refl
... | p19 = refl
... | p23 = refl
... | p29 = refl
... | p31 = refl
... | p41 = refl
... | p47 = refl
... | p59 = refl
... | p71 = refl

PrimeWitness : ShiftContractState → Set
PrimeWitness x = ∀ p → PrimeSelected x p

canonicalPrimeWitness : ∀ x → PrimeWitness x
canonicalPrimeWitness x = primeSelectedWitness x

canonicalPrimeEmbeddingStepCoarse-commute :
  ∀ x →
  shiftContractObservablePrimeEmbedding (shiftCoarse (shiftStep x))
    ≡
  shiftContractObservablePrimeEmbedding (shiftStep (shiftCoarse x))
canonicalPrimeEmbeddingStepCoarse-commute x =
  cong shiftContractObservablePrimeEmbedding (shiftCoarseStep-commute x)

canonicalPrimeSignatureStepCoarse-commute :
  ∀ x →
  signatureOnGeo (canonicalShiftHeckeState (shiftCoarse (shiftStep x)))
    ≡
  signatureOnGeo (canonicalShiftHeckeState (shiftStep (shiftCoarse x)))
canonicalPrimeSignatureStepCoarse-commute x =
  cong
    (λ s → signatureOnGeo (canonicalShiftHeckeState s))
    (shiftCoarseStep-commute x)

canonicalPrimeEigenStepCoarse-commute :
  ∀ x →
  eigenOnGeo (canonicalShiftHeckeState (shiftCoarse (shiftStep x)))
    ≡
  eigenOnGeo (canonicalShiftHeckeState (shiftStep (shiftCoarse x)))
canonicalPrimeEigenStepCoarse-commute x =
  cong
    (λ s → eigenOnGeo (canonicalShiftHeckeState s))
    (shiftCoarseStep-commute x)

canonicalPrimeConeStepCoarseTransport :
  ∀ x →
  shiftRGConeWitness x →
  shiftRGConeWitness (shiftCoarse (shiftStep x))
canonicalPrimeConeStepCoarseTransport x w =
  shiftConeTransportCoarse (shiftStep x) (shiftConeTransportStep x w)

------------------------------------------------------------------------
-- Current bridge package:
-- what is already theorem-bearing vs what remains the explicit next target.

record CanonicalPrimeSelectionBridge : Set₁ where
  field
    selectedPrime      : ShiftContractState → SSP → Set
    selectedPrime-at   : ∀ x → PrimeWitness x
    primeEmbedding     : ShiftContractState → FactorVec
    signature          : ShiftContractState → Sig15
    eigenProfile       : ShiftContractState → EigenProfile
    stepCoarse-prime   :
      ∀ x →
      primeEmbedding (shiftCoarse (shiftStep x))
        ≡
      primeEmbedding (shiftStep (shiftCoarse x))
    stepCoarse-signature :
      ∀ x →
      signature (shiftCoarse (shiftStep x))
        ≡
      signature (shiftStep (shiftCoarse x))
    primeHistogramLowerBound :
      ∀ x p →
      CTSW.illegalCount-chamber
        shiftContractObservableChamberToShiftWitnessBridge x p
        ≤
      CTSW.forcedStableCount-hist
        shiftContractObservableChamberToShiftWitnessBridge x p
    primeInvarianceTarget : Set
    primeIsolationTarget  : Set

canonicalPrimeSelectionBridge : CanonicalPrimeSelectionBridge
canonicalPrimeSelectionBridge = record
  { selectedPrime = PrimeSelected
  ; selectedPrime-at = canonicalPrimeWitness
  ; primeEmbedding = shiftContractObservablePrimeEmbedding
  ; signature = λ x → signatureOnGeo (canonicalShiftHeckeState x)
  ; eigenProfile = λ x → eigenOnGeo (canonicalShiftHeckeState x)
  ; stepCoarse-prime = canonicalPrimeEmbeddingStepCoarse-commute
  ; stepCoarse-signature = canonicalPrimeSignatureStepCoarse-commute
  ; primeHistogramLowerBound = shiftContractObservableIllegalCount≤forcedStableCountHist
  ; primeInvarianceTarget =
      ∀ x →
      shiftContractObservablePrimeEmbedding (shiftCoarse x)
        ≡
      shiftContractObservablePrimeEmbedding x
  ; primeIsolationTarget =
      ∀ x →
      shiftRGConeWitness x →
      shiftRGConeWitness (shiftCoarse (shiftStep x))
  }
