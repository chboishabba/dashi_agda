module DASHI.Physics.Closure.Validation.FejerOverChiSquared where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC
open import DASHI.Physics.Closure.MDLFejerAxiomsShift as MDLFA

data Chi2FalsifierStatus : Set where
  pending : Chi2FalsifierStatus
  interfaceWired : Chi2FalsifierStatus
  formalized : Chi2FalsifierStatus

data FejerBenchmarkVerdict : Set where
  positiveSideEstablished : FejerBenchmarkVerdict
  chi2BoundaryWired : FejerBenchmarkVerdict
  fullyInstrumented : FejerBenchmarkVerdict

record FejerOverChi2Harness : Setω where
  field
    label : String
    seams : ∀ {m k : Nat} → SSC.ShiftSeams {m} {k}
    mdlFejerWitness : MDLFA.MDLFejerAxiomsShift
    chi2FalsifierStatus : Chi2FalsifierStatus

record FejerOverChi2Facts : Setω where
  field
    seamWitness : ∀ {m k : Nat} → SSC.ShiftSeams {m} {k}
    mdlFejerWitness : MDLFA.MDLFejerAxiomsShift
    chi2BoundaryReady : Bool
    chi2FalsifierReady : Bool

chi2BoundaryReady : Chi2FalsifierStatus → Bool
chi2BoundaryReady pending = false
chi2BoundaryReady interfaceWired = true
chi2BoundaryReady formalized = true

chi2StatusReady : Chi2FalsifierStatus → Bool
chi2StatusReady pending = false
chi2StatusReady interfaceWired = false
chi2StatusReady formalized = true

computeFacts : FejerOverChi2Harness → FejerOverChi2Facts
computeFacts harness =
  record
    { seamWitness = FejerOverChi2Harness.seams harness
    ; mdlFejerWitness = FejerOverChi2Harness.mdlFejerWitness harness
    ; chi2BoundaryReady =
        chi2BoundaryReady
          (FejerOverChi2Harness.chi2FalsifierStatus harness)
    ; chi2FalsifierReady =
        chi2StatusReady
          (FejerOverChi2Harness.chi2FalsifierStatus harness)
    }

classify : FejerOverChi2Facts → FejerBenchmarkVerdict
classify facts with FejerOverChi2Facts.chi2FalsifierReady facts
... | true = fullyInstrumented
... | false with FejerOverChi2Facts.chi2BoundaryReady facts
... | true = chi2BoundaryWired
... | false = positiveSideEstablished
