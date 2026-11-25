module DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact where

------------------------------------------------------------------------
-- CMP122 EQUATION (1.71): SOURCE T-OPERATION AS A LOCALIZED INTEGRAL
--
-- Primary source:
-- T. Bałaban, "Large Field Renormalization. II. Localization,
-- Exponentiation, and Bounds for the R Operation", CMP 122 (1989), 355--392,
-- DOI 10.1007/BF01238433 (https://doi.org/10.1007/BF01238433).
--
-- Visually verified original scan (26 Nov 2026):
-- https://scispace.com/pdf/large-field-renormalization-ii-localization-exponentiation-h8b7ih93xo.pdf
-- CMP122-II, printed pp. 378--379, PDF pages 24--25 (1-indexed).
-- Equations (1.71)--(1.72) define the NEW component-local T'-operation.
-- The exact printed (1.71) contains 1/(2^d d!) symmetry averaging; localized
-- integration in Lie-algebra B and group-valued V_h; gauge/tree deltas;
-- source-domain characteristic functions and inherited T_h; quadratic
-- fluctuation and Wilson/action terms; localized V/E, vacuum and logarithmic
-- gauge-tree normalization.  The operator is the RESULT of that integral.
-- On p. 379, T = T_0 ∩ X; rT is the axial tree transformed by a Euclidean
-- symmetry r (2^d coordinate reflections and d! coordinate permutations).
--
-- CRITICAL Eq. (1.71) COLLISION: CMP122-I (1989), printed p. 192, has a
-- DIFFERENT Eq. (1.71), an ordered preliminary T''-operation expression.
-- See Docs/physics/YMClayW0PrimaryVisualEquationCrosswalk20261126.md
-- and do NOT identify them just because both papers number an equation (1.71).
--
-- CRITICAL equality scope: CMP122-II p. 378 explicitly says reversed
-- Faddeev-Popov removal produces densities which are EQUIVALENT AFTER THE
-- PROPER GAUGE INTEGRATION, NOT POINTWISE EQUAL integrands.  A concrete
-- original-Wilson/F19 source step must prove that literal measure/constraint
-- equivalence to inhabit 'sourceStepIsEquation171Mass'.  No such inhabitant
-- is constructed by this record/alias.
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
