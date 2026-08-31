module DASHI.Physics.YangMills.BalabanCMP109QRConstraintAnnihilatorReductionExact where

------------------------------------------------------------------------
-- ROW A1: Q/R CONSTRAINT-VARIATION REDUCTION
--
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- HIGHEST-ALPHA REDUCTION
--
-- The constrained Gaussian first variation has source-native W/Q/R pieces.
-- Paying |Q|+|R| on a positive momentum patch is unnecessary if Q and R are
-- pure constraint/gauge variations.  Existing KKT machinery proves exactly:
--
--   covector annihilates ker L  =>  P covector = 0  => covector in im L*.
--
-- This file specializes that theorem to two supplied Q/R variation covectors.
-- The remaining source question is now finite and geometric: prove that the
-- literal CMP98 averaging derivative and CMP99 gauge/projection derivative each
-- annihilate every admissible tangent of the SAME constrained carrier.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanSelectedConstraintAnnihilatorKKTExact as Ann

record CMP109QRConstraintAnnihilatorData (Multiplier : Set) : Set₁ where
  field
    pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier
    qVariation rVariation : KKT.StateVector

    qAnnihilatesAdmissibleTangent :
      Ann.AnnihilatesConstraintKernel pseudoData qVariation
    rAnnihilatesAdmissibleTangent :
      Ann.AnnihilatesConstraintKernel pseudoData rVariation

open CMP109QRConstraintAnnihilatorData public

projectedQVariationZero :
  ∀ {Multiplier}
    (dataSet : CMP109QRConstraintAnnihilatorData Multiplier)
    coordinate →
  Pseudo.admissibleProject (pseudoData dataSet) (qVariation dataSet) coordinate
  ≡ 0ℚ
projectedQVariationZero dataSet =
  Ann.projectedCovectorPointwiseZero
    (pseudoData dataSet) (qVariation dataSet)
    (qAnnihilatesAdmissibleTangent dataSet)

projectedRVariationZero :
  ∀ {Multiplier}
    (dataSet : CMP109QRConstraintAnnihilatorData Multiplier)
    coordinate →
  Pseudo.admissibleProject (pseudoData dataSet) (rVariation dataSet) coordinate
  ≡ 0ℚ
projectedRVariationZero dataSet =
  Ann.projectedCovectorPointwiseZero
    (pseudoData dataSet) (rVariation dataSet)
    (rAnnihilatesAdmissibleTangent dataSet)

qVariationIsConstraintAdjointImage :
  ∀ {Multiplier}
    (dataSet : CMP109QRConstraintAnnihilatorData Multiplier) →
  Ann.KKTMultiplierWitness (pseudoData dataSet) (qVariation dataSet)
qVariationIsConstraintAdjointImage dataSet =
  Ann.selectedKKTMultiplierExistence
    (pseudoData dataSet) (qVariation dataSet)
    (qAnnihilatesAdmissibleTangent dataSet)

rVariationIsConstraintAdjointImage :
  ∀ {Multiplier}
    (dataSet : CMP109QRConstraintAnnihilatorData Multiplier) →
  Ann.KKTMultiplierWitness (pseudoData dataSet) (rVariation dataSet)
rVariationIsConstraintAdjointImage dataSet =
  Ann.selectedKKTMultiplierExistence
    (pseudoData dataSet) (rVariation dataSet)
    (rAnnihilatesAdmissibleTangent dataSet)

cmp109QRConstraintAnnihilatorReductionLevel : ProofLevel
cmp109QRConstraintAnnihilatorReductionLevel = machineChecked

-- Literal/source producers still required.
cmp98LiteralAveragingVariationAnnihilatesConstraintKernelLevel : ProofLevel
cmp98LiteralAveragingVariationAnnihilatesConstraintKernelLevel = conditional

cmp99LiteralGaugeProjectionVariationAnnihilatesConstraintKernelLevel : ProofLevel
cmp99LiteralGaugeProjectionVariationAnnihilatesConstraintKernelLevel = conditional

-- Final trace weld: identify the KKT admissible projection with the same
-- constrained propagator/restriction entering CMP109 (1.4)-(1.5), so the
-- projected-zero Q/R variations disappear inside the trace-log Hessian.
cmp109KKTProjectionToConstrainedTraceWeldLevel : ProofLevel
cmp109KKTProjectionToConstrainedTraceWeldLevel = conditional
