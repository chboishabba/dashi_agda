module DASHI.Physics.Closure.Validation.SnapThresholdLawSyntheticOneMinus where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.SeverityGuard.SyntheticOneMinus.Concrete as SGSOM
open import DASHI.Physics.Closure.Validation.SnapThresholdLaw as STL
open import DASHI.Physics.Closure.Validation.SnapThresholdLawReport as STLR
open import DASHI.Physics.Closure.Validation.SyntheticOneMinusDynamicsWitness as SOMDW

syntheticOneMinusLabel : String
syntheticOneMinusLabel = "synthetic-one-minus-snap-threshold"

syntheticOneMinusDynamicsCardinality : Nat
syntheticOneMinusDynamicsCardinality =
  SOMDW.SyntheticOneMinusDynamicsWitness.stateCardinality
    SOMDW.syntheticDynamicsWitness

syntheticOneMinusHarness : STL.SnapThresholdHarness
syntheticOneMinusHarness =
  record
    { label = syntheticOneMinusLabel
    ; X = SGSOM.State
    ; policy = SGSOM.policyᵒ
    ; witnessState = SGSOM.witnessState
    ; witnessSnap = SGSOM.witnessSnap
    }

syntheticOneMinusReport : STLR.SnapThresholdReport
syntheticOneMinusReport = STLR.buildReport syntheticOneMinusHarness

syntheticOneMinusVerdict : STL.SnapThresholdVerdict
syntheticOneMinusVerdict =
  STLR.SnapThresholdReport.verdict syntheticOneMinusReport
