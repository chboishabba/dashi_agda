module DASHI.Unified.TOEQuantumInhabitantsExact where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (refl)

import DASHI.Unified.TOEConcreteInhabitantsExact as Inhabitants
open Inhabitants.FormalInhabitantReceipt

lean76GTPSProjectionInhabitant : Inhabitants.FormalInhabitantReceipt
lean76GTPSProjectionInhabitant =
  record
    { prover = "Lean4"
    ; repository = "chboishabba/dashi_lean4"
    ; pullRequest = 76
    ; headCommit = "7749ed96f03aeb0a8b59c108d8b3902b059acf0a"
    ; moduleName = "QuantumMereology.GTPSProjectionProducer"
    ; declaration = "localPlusCommutantProjection"
    ; propositionScope =
        "Every finite source g-TPS has a canonical Hilbert-Schmidt orthogonal projection onto A+A', and hence a fully instantiated finite short-time scrambling score."
    ; authority = Inhabitants.importedFormalInhabitant
    ; importedAsAgdaTheorem = false
    ; importedAsAgdaTheoremIsFalse = refl
    }

lean76GTPSMetricInhabitant : Inhabitants.FormalInhabitantReceipt
lean76GTPSMetricInhabitant =
  record
    { prover = "Lean4"
    ; repository = "chboishabba/dashi_lean4"
    ; pullRequest = 76
    ; headCommit = "7749ed96f03aeb0a8b59c108d8b3902b059acf0a"
    ; moduleName = "QuantumMereology.GTPSUnitaryMetric2026"
    ; declaration = "metricElementSq_eq_source_formula"
    ; propositionScope =
        "Finite source unitary-family g-TPS metric element equals kappa^2 times the canonical projected Hilbert-Schmidt residual norm on an explicit same-object tangent receipt."
    ; authority = Inhabitants.importedFormalInhabitant
    ; importedAsAgdaTheorem = false
    ; importedAsAgdaTheoremIsFalse = refl
    }
