{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayCanonicalMassGapConclusionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YMClayVacuumSectorSpectralGapParityExact as Spectral

------------------------------------------------------------------------
-- Preferred endpoint parity with Lean Clay.MassGapConclusion.
--
-- Unlike the compatibility record in YMClayMassGapAssemblyParityExact, the
-- resolvent output is not compressed into one opaque proposition and the unit
-- vacuum is explicit.
------------------------------------------------------------------------

record CanonicalMassGapConclusion
    (Hamiltonian Vacuum Gap : Set) : Set₁ where
  field
    hamiltonian : Hamiltonian
    vacuum : Vacuum
    gap : Gap

    GapPositive : Set
    gapPositive : GapPositive

    VacuumUnit : Set
    vacuumUnit : VacuumUnit

    VacuumFormGap : Set
    vacuumFormGap : VacuumFormGap

    NoEigenvalueBelowGap : Set
    noEigenvalueBelowGap : NoEigenvalueBelowGap

    UniqueVacuumSectorSolvability : Set
    uniqueVacuumSectorSolvability : UniqueVacuumSectorSolvability

    QuantitativeResolventBound : Set
    quantitativeResolventBound : QuantitativeResolventBound

open CanonicalMassGapConclusion public

canonicalMassGapConclusionFromVacuumGapDatum :
  ∀ {Hamiltonian Vacuum Gap}
    (datum : Spectral.VacuumGapDatum Hamiltonian Vacuum Gap) →
  Spectral.VacuumSectorSpectralConsequences datum →
  CanonicalMassGapConclusion Hamiltonian Vacuum Gap
canonicalMassGapConclusionFromVacuumGapDatum datum consequences = record
  { hamiltonian = Spectral.op datum
  ; vacuum = Spectral.vacuum datum
  ; gap = Spectral.gap datum
  ; GapPositive = Spectral.GapPositive datum
  ; gapPositive = Spectral.gapPositive datum
  ; VacuumUnit = Spectral.VacuumUnit datum
  ; vacuumUnit = Spectral.vacuumUnit datum
  ; VacuumFormGap = Spectral.VacuumFormGap datum
  ; vacuumFormGap = Spectral.vacuumFormGap datum
  ; NoEigenvalueBelowGap = Spectral.NoEigenvalueBelowGap consequences
  ; noEigenvalueBelowGap = Spectral.noEigenvalueBelowGap consequences
  ; UniqueVacuumSectorSolvability =
      Spectral.UniqueVacuumSectorSolvability consequences
  ; uniqueVacuumSectorSolvability =
      Spectral.uniqueVacuumSectorSolvability consequences
  ; QuantitativeResolventBound = Spectral.QuantitativeResolventBound consequences
  ; quantitativeResolventBound = Spectral.quantitativeResolventBound consequences
  }

canonicalMassGapConclusionFromLeanReceipt :
  ∀ {Hamiltonian Vacuum Gap}
    {datum : Spectral.VacuumGapDatum Hamiltonian Vacuum Gap} →
  Spectral.VacuumSectorLeanTheoremReceipt datum →
  CanonicalMassGapConclusion Hamiltonian Vacuum Gap
canonicalMassGapConclusionFromLeanReceipt {datum = datum} receipt =
  canonicalMassGapConclusionFromVacuumGapDatum datum
    (Spectral.vacuumSectorConsequencesFromLeanReceipt receipt)

data CanonicalEndgameCompilerPresent : Set where
  canonicalEndgameCompilerPresent : CanonicalEndgameCompilerPresent

canonicalEndgameCompilerWitness : CanonicalEndgameCompilerPresent
canonicalEndgameCompilerWitness = canonicalEndgameCompilerPresent

canonicalConclusionAssemblyLevel : ProofLevel
canonicalConclusionAssemblyLevel = machineChecked

-- The underlying analytic consequence theorem is paid by the verified Lean
-- donor but is not relabelled as native Agda kernel mathematics.
canonicalConclusionVacuumSectorAnalyticsLevel : ProofLevel
canonicalConclusionVacuumSectorAnalyticsLevel = standardImported

legacyOpaqueResolventPreferred : Bool
legacyOpaqueResolventPreferred = false

legacyOpaqueResolventPreferredIsFalse : legacyOpaqueResolventPreferred ≡ false
legacyOpaqueResolventPreferredIsFalse = refl
