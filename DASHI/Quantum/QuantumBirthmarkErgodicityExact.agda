{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkErgodicityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Laws.QuantumFieldLaws as Quantum
import DASHI.Physics.Laws.ThermodynamicStatisticalLaws as Thermo
import DASHI.Quantum.QuantumBirthmarkSourceBoundaryExact as Source

------------------------------------------------------------------------
-- UNIVERSAL SYMMETRY FACTOR WITHOUT ADDITIONAL SECTOR STRUCTURE
--
-- Extra symmetries are intentionally excluded from this two-case carrier and
-- handled by QuantumBirthmarkSymmetrySectorExact.  This avoids incorrectly
-- collapsing an intermediate sector-weighting problem to the GOE value 3.
------------------------------------------------------------------------

data TimeReversalClass : Set where
  noTRS : TimeReversalClass
  hasTRS : TimeReversalClass

universalFactor : TimeReversalClass → Nat
universalFactor noTRS = Source.universalFactorWithoutTRS
universalFactor hasTRS = Source.universalFactorWithTRS

universalFactor-noTRS : universalFactor noTRS ≡ 2
universalFactor-noTRS = refl

universalFactor-hasTRS : universalFactor hasTRS ≡ 3
universalFactor-hasTRS = refl

------------------------------------------------------------------------
-- THIN REFINEMENT OF THE EXISTING QUANTUM-DYNAMICS OWNER
------------------------------------------------------------------------

record QuantumBirthmarkModel
  (Q : Quantum.QuantumKinematics)
  (D : Quantum.QuantumDynamics Q) : Set₁ where

  open Quantum.QuantumKinematics Q
  open Quantum.QuantumDynamics D

  field
    Nonstationary : State → Set
    ClosedIsolatedRegime : State → Set
    APrioriMatched : State → State → Set
    DynamicallyDistinguishable : State → State → Set

    Occupation : Set
    Ratio : Set
    longTimeOccupation : State → State → Occupation
    occupationRatio : Occupation → Occupation → Ratio
    ClassicalErgodicBaseline : Ratio → Set
    AboveClassicalErgodicBaseline : Ratio → Set

    UniversalBirthmarkFactor : State → Nat
    symmetryClass : State → TimeReversalClass
    noAdditionalSymmetryDegeneracy : State → Set
    universalFactorReceipt :
      (state : State) →
      noAdditionalSymmetryDegeneracy state →
      UniversalBirthmarkFactor state ≡ universalFactor (symmetryClass state)

    RevivalEnhancement : Set
    revivalEnhancement : State → RevivalEnhancement
    BirthmarkDecomposition : State → Ratio → Set

    ThoulessTime : Time
    HeisenbergTime : Time
    EarlierThan : Time → Time → Set
    EarlyRecurrence : State → Time → Set
    ExploredRegion : State → Time → Set
    MaximumExplorationPrinciple : State → Set

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
-- DIRECT REUSE THEOREM: NORMALISED EVOLUTION STAYS ON THE SAME CARRIER
------------------------------------------------------------------------

normalisedEvolute :
  {Q : Quantum.QuantumKinematics} →
  (D : Quantum.QuantumDynamics Q) →
  (time : Quantum.QuantumDynamics.Time D) →
  (state : Quantum.QuantumKinematics.State Q) →
  Quantum.QuantumKinematics.Normalised Q state →
  Quantum.QuantumKinematics.Normalised Q
    (Quantum.QuantumDynamics.Evolution D time state)
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
------------------------------------------------------------------------

record BirthmarkThermodynamicBridge
  (T : Thermo.ThermodynamicStatisticalAuthorityBoundary) : Set₁ where
  field
    quantumMemoryConstrainsErgodicPromotion : Set
    coarseGrainedThermalisationMayRemainASeparateQuestion : Set
    noAutomaticSecondLawContradiction : Set
