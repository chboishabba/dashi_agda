{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkErgodicityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Laws.QuantumFieldLaws as Quantum
import DASHI.Physics.Laws.ThermodynamicStatisticalLaws as Thermo
import DASHI.Quantum.QuantumBirthmarkSourceBoundaryExact as Source

------------------------------------------------------------------------
-- UNIVERSAL SYMMETRY FACTOR
------------------------------------------------------------------------

data TimeReversalClass : Set where
  noTRS : TimeReversalClass
  hasTRS : TimeReversalClass
  additionalSymmetry : TimeReversalClass

universalFactor : TimeReversalClass → Nat
universalFactor noTRS = Source.universalFactorWithoutTRS
universalFactor hasTRS = Source.universalFactorWithTRS
universalFactor additionalSymmetry = Source.universalFactorWithTRS

universalFactor-noTRS : universalFactor noTRS ≡ 2
universalFactor-noTRS = refl

universalFactor-hasTRS : universalFactor hasTRS ≡ 3
universalFactor-hasTRS = refl

------------------------------------------------------------------------
-- THIN REFINEMENT OF THE EXISTING QUANTUM-DYNAMICS OWNER
--
-- We do not replace State/Evolution/normalisation machinery.  The birthmark
-- layer adds the long-time comparison observable, symmetry factor, early-time
-- revival factor, and exploration-timescale predicates required by the PRX
-- framework.
------------------------------------------------------------------------

record QuantumBirthmarkModel
  (Q : Quantum.QuantumKinematics)
  (D : Quantum.QuantumDynamics Q) : Set₁ where

  open Quantum.QuantumKinematics Q
  open Quantum.QuantumDynamics D

  field
    -- State-selection / comparison boundary.
    Nonstationary : State → Set
    ClosedIsolatedRegime : State → Set
    AProriMatched : State → State → Set
    DynamicallyDistinguishable : State → State → Set

    -- Long-time occupation/fidelity-like observable.
    Occupation : Set
    Ratio : Set
    longTimeOccupation : State → State → Occupation
    occupationRatio : Occupation → Occupation → Ratio
    ClassicalErgodicBaseline : Ratio → Set
    AboveClassicalErgodicBaseline : Ratio → Set

    -- Birthmark decomposition.
    UniversalBirthmarkFactor : State → Nat
    symmetryClass : State → TimeReversalClass
    universalFactorReceipt :
      (state : State) →
      UniversalBirthmarkFactor state ≡ universalFactor (symmetryClass state)

    RevivalEnhancement : Set
    revivalEnhancement : State → RevivalEnhancement
    BirthmarkDecomposition : State → Ratio → Set

    -- Early/late dynamical scales.
    ThoulessTime : Time
    HeisenbergTime : Time
    EarlierThan : Time → Time → Set
    EarlyRecurrence : State → Time → Set
    ExploredRegion : State → Time → Set
    MaximumExplorationPrinciple : State → Set

    -- Core paper-facing receipts.  These are assumptions/interfaces whose
    -- concrete analytic/RMT proofs remain source-owned rather than fabricated
    -- from the generic DASHI carrier.
    universalMemory :
      (state : State) →
      Nonstationary state →
      ClosedIsolatedRegime state →
      Set

    revivalStrengthensBirthmark :
      (state : State) (time : Time) →
      EarlyRecurrence state time →
      EarlierThan time HeisenbergTime →
      Set

    maximumExplorationPrinciple :
      (state : State) →
      Nonstationary state →
      ClosedIsolatedRegime state →
      MaximumExplorationPrinciple state

    scarIsBirthmarkSpecialCase : State → Set

------------------------------------------------------------------------
-- DIRECT REUSE THEOREM: EVERY NORMALISED EVOLUTE REMAINS NORMALISED
--
-- This theorem is not imported from the birthmark paper.  It is already
-- provided by DASHI's generic QuantumDynamics law surface and is reused here
-- to keep the new layer attached to the same physical state evolution.
------------------------------------------------------------------------

normalisedEvolute :
  {Q : Quantum.QuantumKinematics} →
  (D : Quantum.QuantumDynamics Q) →
  let open Quantum.QuantumKinematics Q
      open Quantum.QuantumDynamics D
  in (time : Time) (state : State) →
     Normalised state →
     Normalised (Evolution time state)
normalisedEvolute D = Quantum.QuantumDynamics.normPreserved D

------------------------------------------------------------------------
-- PROMOTION / INTERPRETATION FIREWALL
------------------------------------------------------------------------

record QuantumBirthmarkAuthorityBoundary : Set where
  field
    birthmarkDoesNotByItselfRefuteThermodynamics : Bool
    birthmarkDoesNotMeanNoObservableThermalises : Bool
    genericClosedSystemResultIsNotOpenSystemResult : Bool
    universalFactorIsNotStadiumSpecific : Bool
    revivalEnhancementIsNotEquivalentToScar : Bool
    classicalErgodicityAndQuantumLongTimeMemoryRemainDistinctClaims : Bool
    extraSymmetriesNeedExplicitSectorAccounting : Bool
    experimentalObservationStillRequiresObservableAndProtocol : Bool

birthmarkAuthorityBoundary : QuantumBirthmarkAuthorityBoundary
birthmarkAuthorityBoundary = record
  { birthmarkDoesNotByItselfRefuteThermodynamics = true
  ; birthmarkDoesNotMeanNoObservableThermalises = true
  ; genericClosedSystemResultIsNotOpenSystemResult = true
  ; universalFactorIsNotStadiumSpecific = true
  ; revivalEnhancementIsNotEquivalentToScar = true
  ; classicalErgodicityAndQuantumLongTimeMemoryRemainDistinctClaims = true
  ; extraSymmetriesNeedExplicitSectorAccounting = true
  ; experimentalObservationStillRequiresObservableAndProtocol = true
  }

------------------------------------------------------------------------
-- CROSS-POLLINATION WITH THE EXISTING THERMODYNAMIC AUTHORITY BOUNDARY
--
-- ThermodynamicStatisticalLaws already insists that ergodicity is an explicit
-- assumption.  The quantum-birthmark result therefore refines the conditions
-- under which that assumption may be used; it does not erase the second-law,
-- ensemble, coarse-graining, or thermodynamic-limit layers.
------------------------------------------------------------------------

record BirthmarkThermodynamicBridge
  (T : Thermo.ThermodynamicStatisticalAuthorityBoundary) : Set₁ where
  field
    quantumMemoryConstrainsErgodicPromotion : Set
    coarseGrainedThermalisationMayRemainASeparateQuestion : Set
    noAutomaticSecondLawContradiction : Set
