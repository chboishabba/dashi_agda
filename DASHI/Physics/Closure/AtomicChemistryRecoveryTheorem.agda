module DASHI.Physics.Closure.AtomicChemistryRecoveryTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_)

open import DASHI.Physics.CliffordEvenLiftBridge as CE
open import DASHI.Physics.Closure.PhysicsClosureFullCanonicalBridgePackage as PCFCBP
open import DASHI.Physics.Closure.CliffordToEvenWaveLiftBridgeTheorem as CTEW
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservablesTheorem as KLRWO
open import DASHI.Physics.Closure.SyntheticRealizationWitness as SRW
open import DASHI.Physics.Closure.Validation.ObservableCollapse as OC
open import DASHI.Physics.Closure.Validation.ObservableCollapseReport as OCR
open import DASHI.Physics.Closure.Validation.ObservableCollapseShift as OCS
open import Ontology.DNA.ChemistryQuotient as CDQ

------------------------------------------------------------------------
-- Theorem-facing carrier for the local atom/chemistry interpretation layer.
--
-- This module does not claim atom recovery, spectra recovery, or chemistry
-- recovery from the canonical closure stack. It packages the strongest
-- currently landed local ingredients:
--
-- * the canonical full-closure-to-wave bridge package,
-- * the known-limits recovered wave-observable package,
-- * the synthetic shell/signature realization witness,
-- * and one theorem-facing chemistry quotient support surface.
--
-- The remaining gates are kept as explicit theorem obligations.

record AtomicChemistryRecoveryTheorem : Setω where
  field
    canonicalBridgePackage :
      PCFCBP.PhysicsClosureFullCanonicalBridgePackage

    recoveredWaveObservables :
      KLRWO.KnownLimitsRecoveredWaveObservablesTheorem

    syntheticShellRealization :
      SRW.SyntheticRealizationWitness

    chemistryDictionarySupport : Set

    canonicalWaveLiftIntoEven :
      CE.WaveLiftIntoEven
        (CTEW.CliffordToEvenWaveLiftBridgeTheorem.canonicalCliffordFromContractionQuadratic
          (PCFCBP.PhysicsClosureFullCanonicalBridgePackage.cliffordToEvenWaveLiftBridge
            canonicalBridgePackage))

    shellObservableReport :
      OCR.ObservableCollapseReport

    shellCollapseEstablished :
      OCR.ObservableCollapseReport.verdict shellObservableReport
      ≡
      OC.collapseEstablished

    shellProfileCompatibility : Set
    closedShellRecovery : Set
    chemistryDictionaryCompatibility : Set
    atomicChemistryRecovery : Set

canonicalAtomicChemistryRecoveryTheorem :
  AtomicChemistryRecoveryTheorem
canonicalAtomicChemistryRecoveryTheorem =
  let
    canonicalBridgePackage =
      PCFCBP.canonicalPhysicsClosureFullCanonicalBridgePackage
    waveBridge =
      PCFCBP.PhysicsClosureFullCanonicalBridgePackage.cliffordToEvenWaveLiftBridge
        canonicalBridgePackage
  in
  record
    { canonicalBridgePackage = canonicalBridgePackage
    ; recoveredWaveObservables =
        KLRWO.canonicalKnownLimitsRecoveredWaveObservablesTheorem
    ; syntheticShellRealization =
        SRW.syntheticRealizationWitness
    ; chemistryDictionarySupport =
        CDQ.ChemistryFeature
    ; canonicalWaveLiftIntoEven =
        CTEW.CliffordToEvenWaveLiftBridgeTheorem.canonicalWaveLiftIntoEvenFromContractionQuadratic
          waveBridge
    ; shellObservableReport = OCS.shiftReport
    ; shellCollapseEstablished = refl
    ; shellProfileCompatibility = SRW.SyntheticRealizationWitness
    ; closedShellRecovery = SRW.SyntheticRealizationWitness
    ; chemistryDictionaryCompatibility =
        CDQ.ChemistryFeature → CDQ.ChemistryFeature
    ; atomicChemistryRecovery =
        CE.WaveLiftIntoEven.State
          (CTEW.CliffordToEvenWaveLiftBridgeTheorem.canonicalWaveLiftIntoEvenFromContractionQuadratic
            waveBridge)
        →
        CDQ.ChemistryFeature
    }
