module DASHI.Interop.SmithChartLeanParityExact where

------------------------------------------------------------------------
-- LEAN / AGDA PARITY RECEIPT FOR THE SMITH-CHART COMPLEX CORE
--
-- Lean source owner:
--   chboishabba/dashi_lean4
--   Integration/SmithChartComplexReflection.lean
--
-- Lean target:
--   ordinary Mathlib complex numbers.
--
-- Source-written Lean theorems:
--   engineeringJ_sq
--   gamma_conj
--   gamma_admittance
--
-- Agda source owner:
--   DASHI.Physics.Foundations.SmithChartComplexReflectionExact
--
-- FIREWALL
-- This receipt records theorem parity only.  It does not identify an Agda
-- complex carrier with Lean Complex, and it does not identify engineering
-- j=sqrt(-1), Smith Gamma, or the modular j-invariant.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

record SmithChartLeanParity : Set where
  constructor smith-chart-lean-parity
  field
    leanRepository : String
    leanSourcePath : String
    leanEngineeringJTheorem : String
    leanConjugationTheorem : String
    leanAdmittanceHalfTurnTheorem : String

    agdaSourcePath : String

    engineeringJImaginaryUnitParity : Bool
    smithGammaConjugationParity : Bool
    smithAdmittanceHalfTurnParity : Bool

    leanKernelReceiptObserved : Bool
    agdaLeanComplexSameObjectProved : Bool
    engineeringJIdentifiedWithModularJ : Bool
    smithGammaIdentifiedWithModularJ : Bool

open SmithChartLeanParity public

canonicalSmithChartLeanParity : SmithChartLeanParity
canonicalSmithChartLeanParity =
  smith-chart-lean-parity
    "chboishabba/dashi_lean4"
    "Integration/SmithChartComplexReflection.lean"
    "Integration.SmithChartComplexReflection.engineeringJ_sq"
    "Integration.SmithChartComplexReflection.gamma_conj"
    "Integration.SmithChartComplexReflection.gamma_admittance"
    "DASHI/Physics/Foundations/SmithChartComplexReflectionExact.agda"
    true true true
    false false false false
