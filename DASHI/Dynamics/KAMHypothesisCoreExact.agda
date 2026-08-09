module DASHI.Dynamics.KAMHypothesisCoreExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Jürgen Pöschel,
-- "Integrability of Hamiltonian Systems on Cantor Sets",
-- Communications on Pure and Applied Mathematics 35 (1982), 653--696.
-- DOI: 10.1002/cpa.3160350504.
--
-- DASHI CONTRIBUTION
--
-- Make the KAM comparison fail closed.  A finite order-three helical rotation
-- has an explicit resonance witness and therefore cannot itself serve as a
-- nonresonant/quasiperiodic KAM frequency.  Genuine KAM promotion is typed by
-- separate near-integrability, nondegeneracy, Diophantine and invariant-torus
-- witnesses.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Topology.HelicalWeaveMappingTorusExact as Helix

_≠_ : {A : Set} → A → A → Set
first ≠ second = first ≡ second → ⊥

record FiniteResonanceWitness : Set where
  constructor finiteResonanceWitness
  field
    phase : Helix.Phase3
    period : Nat
    periodIsThree : period ≡ 3
    returnsAfterPeriod :
      Helix.iterateRotation period phase ≡ phase

open FiniteResonanceWitness public

phaseThreeResonance :
  (phase : Helix.Phase3) →
  FiniteResonanceWitness
phaseThreeResonance phase =
  finiteResonanceWitness
    phase
    3
    refl
    (Helix.iterateRotationThree phase)

NoThreeStepReturn : Helix.Phase3 → Set
NoThreeStepReturn phase =
  Helix.iterateRotation 3 phase ≠ phase

orderThreeRotationRefutesNoReturn :
  (phase : Helix.Phase3) →
  NoThreeStepReturn phase → ⊥
orderThreeRotationRefutesNoReturn phase noReturn =
  noReturn (Helix.iterateRotationThree phase)

------------------------------------------------------------------------
-- Genuine KAM inputs.  The record does not assert a theorem by itself; it
-- identifies the mathematical data that a real imported or reconstructed KAM
-- theorem must consume and produce.
------------------------------------------------------------------------

record KAMProblem : Set₁ where
  constructor kamProblem
  field
    PhaseSpace : Set
    IntegrableHamiltonian : Set
    Perturbation : Set
    FrequencyVector : Set
    InvariantTorus : Set

    nearIntegrable :
      IntegrableHamiltonian → Perturbation → Set

    twistNondegenerate :
      IntegrableHamiltonian → Set

    diophantine :
      FrequencyVector → Set

    torusHasFrequency :
      InvariantTorus → FrequencyVector → Set

open KAMProblem public

record KAMWitness (problem : KAMProblem) : Set₁ where
  constructor kamWitness
  field
    integrableHamiltonian : IntegrableHamiltonian problem
    perturbation : Perturbation problem
    frequency : FrequencyVector problem
    invariantTorus : InvariantTorus problem
    nearIntegrableWitness :
      nearIntegrable problem integrableHamiltonian perturbation
    twistWitness :
      twistNondegenerate problem integrableHamiltonian
    diophantineWitness :
      diophantine problem frequency
    invariantTorusWitness :
      torusHasFrequency problem invariantTorus frequency

open KAMWitness public

data CascadeComparison : Set where
  frequencyCascadeAnalogy : CascadeComparison

data KAMPromotion : Set where

cascadeComparisonDoesNotConstructKAMWitness :
  CascadeComparison →
  KAMPromotion →
  ⊥
cascadeComparisonDoesNotConstructKAMWitness comparison ()

record CarrierKAMBoundary : Set where
  constructor carrierKAMBoundary
  field
    finiteHelicalResonance :
      (phase : Helix.Phase3) → FiniteResonanceWitness
    finiteHelicalNoReturnImpossible :
      (phase : Helix.Phase3) → NoThreeStepReturn phase → ⊥
    cascadeAnalogyPromotesKAM : Bool
    cascadeAnalogyPromotesKAMIsFalse :
      cascadeAnalogyPromotesKAM ≡ false
    KAMRequiresSeparateWitness : Set₁

canonicalCarrierKAMBoundary : CarrierKAMBoundary
canonicalCarrierKAMBoundary =
  carrierKAMBoundary
    phaseThreeResonance
    orderThreeRotationRefutesNoReturn
    false refl
    (Σ KAMProblem KAMWitness)
