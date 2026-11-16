module DASHI.Physics.Motors.SmithFilsingerSunEarthCoupledSourceExact where

-- Abstract, dimensionless NONNEGATIVE work units only. Not a Maxwell solver
-- and not physical evidence of sun-to-ground power capture.
-- Source owners and context:
-- R. Lukianova et al., Solar Wind-Ionosphere-Troposphere Coupling Via the
-- Polar Branch of the Global Electric Circuit (2025), doi:10.1007/s10712-025-09914-7.
-- D. Lin et al., Efficiency of Electromagnetic Energy Transfer From Solar Wind
-- to Ionosphere Through Magnetospheric ULF Waves (2026), doi:10.1029/2025GL118532.
-- M. Blanc et al., Physical Links Between Weather in Space and Weather in the
-- Lower Atmosphere (2026), doi:10.1007/s10712-026-09968-1.
-- B. Tinsley, Uncertainties in Evaluating Global Electric Circuit Interactions
-- With Atmospheric Clouds and Aerosols (2022), doi:10.1029/2021JD035954.
-- New source-attribution and abstract finite-work bounds are DASHI extensions.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

data Empty : Set where

data SourcePort : Set where
  solarPhotons solarWindThroughMagnetosphere atmosphericStormGenerator
    activeController storedFieldRelease : SourcePort

solarWindNotStormGenerator :
  solarWindThroughMagnetosphere ≡ atmosphericStormGenerator → Empty
solarWindNotStormGenerator ()

data SourceStudy : Set where
  lukianovaPolar2025 linULF2026 blancWholeAtmosphere2026 tinsleyCloud2022 : SourceStudy

data EvidenceTier : Set where
  researchReview globalSimulation observationAndTheory : EvidenceTier

sourceTier : SourceStudy → EvidenceTier
sourceTier lukianovaPolar2025 = observationAndTheory
sourceTier linULF2026 = globalSimulation
sourceTier blancWholeAtmosphere2026 = researchReview
sourceTier tinsleyCloud2022 = researchReview

-- Energy ports must be disjoint physical crossings of ONE selected boundary.
-- Counting solar heating and its downstream storm electrical output twice is
-- forbidden: an outer Sun/Earth budget makes storm generation INTERNAL.
record NonnegativeBoundaryWork : Set where
  field
    sunPhotons : Nat
    solarWind : Nat
    atmosphere : Nat
    pump : Nat
    initialStorageRelease : Nat
    usefulLoad : Nat
    dissipated : Nat
    radiationLeaving : Nat
    finalStorageIncrease : Nat
    conservation :
      sunPhotons + (solarWind + (atmosphere + (pump + initialStorageRelease)))
      ≡ usefulLoad + (dissipated + (radiationLeaving + finalStorageIncrease))

-- Uninterpreted Nat amounts: this theorem only enforces the supplied ledger.
data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤ : {m n : Nat} → m ≤ n → suc m ≤ suc n

sucInjective : {m n : Nat} → suc m ≡ suc n → m ≡ n
sucInjective refl = refl

loadBelowInput : (input load rest : Nat) →
  input ≡ load + rest → load ≤ input
loadBelowInput input zero rest equal = zero≤
loadBelowInput zero (suc load) rest ()
loadBelowInput (suc input) (suc load) rest equal =
  suc≤ (loadBelowInput input load rest (sucInjective equal))

loadWorkBound : (b : NonnegativeBoundaryWork) →
  NonnegativeBoundaryWork.usefulLoad b ≤
  (NonnegativeBoundaryWork.sunPhotons b +
    (NonnegativeBoundaryWork.solarWind b +
      (NonnegativeBoundaryWork.atmosphere b +
        (NonnegativeBoundaryWork.pump b +
          NonnegativeBoundaryWork.initialStorageRelease b))))
loadWorkBound b =
  loadBelowInput _ _ _ (NonnegativeBoundaryWork.conservation b)

sourceFreeLoadZero : (load losses : Nat) →
  zero ≡ load + losses → load ≡ zero
sourceFreeLoadZero zero losses equal = refl
sourceFreeLoadZero (suc load) losses ()
