{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologyGTPSUnitaryMetric2026Regression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Quantum.QuantumMereologyGTPSUnitaryMetric2026AuthorityExact as M

unitary-family-metric-source-written :
  M.UnitaryFamilyMetricFormulaSourceWritten
    M.canonicalGTPSUnitaryMetricStatus ≡ true
unitary-family-metric-source-written =
  M.UnitaryFamilyMetricFormulaSourceWrittenIsTrue
    M.canonicalGTPSUnitaryMetricStatus

minimizer-pullback-remains-open :
  M.MinimizerMapPullbackDifferentiated
    M.canonicalGTPSUnitaryMetricStatus ≡ false
minimizer-pullback-remains-open =
  M.MinimizerMapPullbackDifferentiatedIsFalse
    M.canonicalGTPSUnitaryMetricStatus

thermodynamic-mqpt-remains-open :
  M.ThermodynamicMQPTSourceWritten
    M.canonicalGTPSUnitaryMetricStatus ≡ false
thermodynamic-mqpt-remains-open =
  M.ThermodynamicMQPTSourceWrittenIsFalse
    M.canonicalGTPSUnitaryMetricStatus
