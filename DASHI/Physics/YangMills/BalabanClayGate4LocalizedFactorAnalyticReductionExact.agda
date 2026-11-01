module DASHI.Physics.YangMills.BalabanClayGate4LocalizedFactorAnalyticReductionExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- The reduction is the standard normed-algebra chain
--   ||1+r|| <= 1+||r|| <= exp(||r||).
-- It does not install the physical factor identity or the analytic norm estimate
-- as consequences of the abstract exponential laws.
------------------------------------------------------------------------

record LocalizedFactorRemainderReduction (Term Bound : Set) : Set₁ where
  field
    one : Bound
    add : Bound → Bound → Bound
    exponential : Bound → Bound
    LessEqual : Bound → Bound → Set

    localizedFactor : Term → Bound
    remainderNorm termNorm : Term → Bound

    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    addOneMonotone : ∀ {left right} →
      LessEqual left right → LessEqual (add one left) (add one right)

    physicalFactorBelowOnePlusRemainder : ∀ term →
      LessEqual (localizedFactor term) (add one (remainderNorm term))

    remainderNormBelowTermNorm : ∀ term →
      LessEqual (remainderNorm term) (termNorm term)

    onePlusBelowExponential : ∀ value →
      LessEqual (add one value) (exponential value)

open LocalizedFactorRemainderReduction public

localizedFactorBelowExponential :
  ∀ {Term Bound}
    (dataSet : LocalizedFactorRemainderReduction Term Bound)
    term →
  LessEqual dataSet
    (localizedFactor dataSet term)
    (exponential dataSet (termNorm dataSet term))
localizedFactorBelowExponential dataSet term =
  transitive dataSet
    (physicalFactorBelowOnePlusRemainder dataSet term)
    (transitive dataSet
      (addOneMonotone dataSet
        (remainderNormBelowTermNorm dataSet term))
      (onePlusBelowExponential dataSet (termNorm dataSet term)))

record LocalizedFactorEstimateMeaning
    (PhysicalTerm AnalyticTerm Bound : Set) : Set₁ where
  field
    physicalToAnalyticTerm : PhysicalTerm → AnalyticTerm
    physicalFactor analyticFactor : PhysicalTerm → Bound
    physicalFactorMeaning : ∀ term →
      physicalFactor term ≡ analyticFactor term

open LocalizedFactorEstimateMeaning public

localizedFactorRemainderReductionLevel : ProofLevel
localizedFactorRemainderReductionLevel = machineChecked

localizedFactorExponentialAssemblyLevel : ProofLevel
localizedFactorExponentialAssemblyLevel = machineChecked

physicalLocalizedFactorRemainderMeaningInputsLevel : ProofLevel
physicalLocalizedFactorRemainderMeaningInputsLevel = conditional

physicalLocalizedTriangleNormInputsLevel : ProofLevel
physicalLocalizedTriangleNormInputsLevel = conditional

physicalOnePlusExponentialInputsLevel : ProofLevel
physicalOnePlusExponentialInputsLevel = conditional
