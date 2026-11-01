module DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact where

------------------------------------------------------------------------
-- CMP122 EQUATION (1.71): SOURCE T-OPERATION AS A LOCALIZED INTEGRAL
--
-- Primary source:
-- T. Bałaban, "Large Field Renormalization. II. Localization,
-- Exponentiation, and Bounds for the R Operation", CMP 122 (1989), 355--392.
--
-- Equation (1.71), pp. 378--379, defines the new T-operation on a component X
-- as a composition of localized integrations.  The integrand is an exponential
-- density containing the Wilson/action/quadratic/localized remainder terms.
--
-- Crucially, this is NOT the assertion
--
--     T_k(X) 1 = exp(-A_k(V))
--
-- for a pre-existing global action A_k.  T_k(X) is the RESULT of the localized
-- constrained integration.  This owner records that source semantics directly.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record CMP122Equation171TOperationSemantics
    (Fine SlowField : Set) : Set₁ where
  field
    -- The source-localized exponential density appearing inside Eq. (1.71).
    equation171ExponentialDensity :
      Nat → SlowField → Fine → ℝ

    -- The localized/constrained integration operation represented by Eq. (1.71).
    equation171ConstrainedIntegral :
      Nat → SlowField → (Fine → ℝ) → ℝ

    -- The resulting selected source T-operation mass at the unit observable.
    sourceTOperationMass :
      Nat → SlowField → ℝ

    equation171DefinesTOperationMass :
      ∀ cutoff slow →
      sourceTOperationMass cutoff slow
      ≡
      equation171ConstrainedIntegral cutoff slow
        (equation171ExponentialDensity cutoff slow)

open CMP122Equation171TOperationSemantics public

sourceTOperationMassIsEquation171Integral :
  ∀ {Fine SlowField}
    (source : CMP122Equation171TOperationSemantics Fine SlowField)
    cutoff slow →
  sourceTOperationMass source cutoff slow
  ≡
  equation171ConstrainedIntegral source cutoff slow
    (equation171ExponentialDensity source cutoff slow)
sourceTOperationMassIsEquation171Integral =
  equation171DefinesTOperationMass

cmp122Equation171TOperationSemanticsCompilerLevel : ProofLevel
cmp122Equation171TOperationSemanticsCompilerLevel = machineChecked

-- Genuine source leaf: instantiate the finite component/fibre carrier and the
-- literal Eq. (1.71) exponential density/integration semantics.
literalCMP122Equation171FiniteRealizationLevel : ProofLevel
literalCMP122Equation171FiniteRealizationLevel = conditional
