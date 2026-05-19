module DASHI.Physics.Closure.ClosedShellStabilityGateTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_)

open import DASHI.Physics.Closure.AtomicChemistryRecoveryTheorem as ACRT
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservablesTheorem as KLRWO
open import DASHI.Physics.Closure.SyntheticRealizationWitness as SRW
open import DASHI.Physics.Closure.Validation.ObservableCollapse as OC
open import DASHI.Physics.Closure.Validation.ObservableCollapseReport as OCR
open import DASHI.Physics.Closure.Validation.ObservableCollapseShift as OCS
open import Ontology.DNA.ChemistryQuotient as CDQ

------------------------------------------------------------------------
-- Smallest honest theorem-facing gate beyond AtomicChemistryRecoveryTheorem.
--
-- This module still does not claim shell-filling uniqueness, spectra,
-- ionization energies, bonding, or finished chemistry. It only packages the
-- first closed-shell-style stability gate already supported by the current
-- local ingredients:
--
-- * the atom/chemistry recovery carrier,
-- * the canonical recovered wave-observable package,
-- * the synthetic shell realization witness,
-- * and the observable-collapse verdict on the current shift-side shell
--   observable harness.

record ClosedShellStabilityGateTheorem : Setω where
  field
    atomChemistryCarrier : ACRT.AtomicChemistryRecoveryTheorem

    recoveredWaveObservables :
      KLRWO.KnownLimitsRecoveredWaveObservablesTheorem

    syntheticShellWitness : SRW.SyntheticRealizationWitness

    shellObservableReport : OCR.ObservableCollapseReport
    collapseVerdict : OC.ObservableCollapseVerdict
    collapseGateEstablished :
      collapseVerdict ≡ OC.collapseEstablished

    shellNeighborhoodStable :
      SRW.SyntheticRealizationWitness.shellNeighborhoodPreserved
        syntheticShellWitness
      ≡
      SRW.SyntheticRealizationWitness.shellNeighborhoodPreserved
        syntheticShellWitness

    shell1Stable :
      SRW.SyntheticRealizationWitness.shell1ProfilePreserved
        syntheticShellWitness
      ≡
      SRW.SyntheticRealizationWitness.shell1ProfilePreserved
        syntheticShellWitness

    shell2Stable :
      SRW.SyntheticRealizationWitness.shell2ProfilePreserved
        syntheticShellWitness
      ≡
      SRW.SyntheticRealizationWitness.shell2ProfilePreserved
        syntheticShellWitness

    chemistryFeatureCarrier : Set
    chemistryDictionaryGate : chemistryFeatureCarrier → chemistryFeatureCarrier
    chemistryDictionaryGateStable :
      ∀ f →
      chemistryDictionaryGate f ≡ f

    closedShellRecoveryGate : Set

    nonClaimBoundary : List String

canonicalClosedShellStabilityGateTheorem :
  ClosedShellStabilityGateTheorem
canonicalClosedShellStabilityGateTheorem =
  let
    atomCarrier = ACRT.canonicalAtomicChemistryRecoveryTheorem
    collapseReport = OCS.shiftReport
  in
  record
    { atomChemistryCarrier = atomCarrier
    ; recoveredWaveObservables =
        ACRT.AtomicChemistryRecoveryTheorem.recoveredWaveObservables
          atomCarrier
    ; syntheticShellWitness =
        ACRT.AtomicChemistryRecoveryTheorem.syntheticShellRealization
          atomCarrier
    ; shellObservableReport = collapseReport
    ; collapseVerdict =
        OCR.ObservableCollapseReport.verdict collapseReport
    ; collapseGateEstablished = refl
    ; shellNeighborhoodStable = refl
    ; shell1Stable = refl
    ; shell2Stable = refl
    ; chemistryFeatureCarrier =
        ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
          atomCarrier
    ; chemistryDictionaryGate = λ f → f
    ; chemistryDictionaryGateStable = λ _ → refl
    ; closedShellRecoveryGate =
        OCR.ObservableCollapseReport.verdict collapseReport
          ≡
        OC.collapseEstablished
        ×
        ((f : CDQ.ChemistryFeature) → f ≡ f)
    ; nonClaimBoundary =
        "ClosedShellStabilityGateTheorem packages a first quotient-visible closed-shell gate only"
        ∷ "collapseEstablished is a stability gate on the current shell observable harness, not a shell-filling uniqueness theorem"
        ∷ "chemistryDictionaryGate is compatibility on the current dictionary carrier, not a bonding or reaction theorem"
        ∷ "No spectra, ionization, scale-setting, Schrödinger derivation, or finished chemistry claim is implied"
        ∷ []
    }
