module DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound5SourceTheoremLedger where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4BackgroundFieldVariationalTheoremExact as Background
import DASHI.Physics.YangMills.BalabanClayGate4BackgroundPropagatorDecayTheoremsExact as Propagator
import DASHI.Physics.YangMills.BalabanClayGate4BalabanGaugeFixingProposition5Exact as GaugeFixing
import DASHI.Physics.YangMills.BalabanClayGate4ConstraintProjectionSecondVariationExact as Constraint

------------------------------------------------------------------------
-- Source theorem and exact differentiation supplement for physical round five.
--
-- This ledger distinguishes imported Bałaban theorems from the repository-
-- specific identifications needed to consume them. The constraint projection
-- formulas are exact algebra, whereas background existence, gauge fixing and
-- propagator decay retain their primary-source proof level.
------------------------------------------------------------------------

balabanBackgroundFieldExistenceUniquenessLevel =
  Background.balabanBackgroundFieldExistenceUniquenessLevel
balabanBackgroundFieldFineBondEstimateLevel =
  Background.balabanBackgroundFieldFineBondEstimateLevel
balabanBackgroundFieldAnalyticityLevel =
  Background.balabanBackgroundFieldAnalyticityLevel

balabanBackgroundPropagatorTheorem31Level =
  Propagator.balabanBackgroundPropagatorTheorem31Level
balabanBackgroundConstrainedInverseTheorem32Level =
  Propagator.balabanBackgroundConstrainedInverseTheorem32Level
balabanBackgroundGaugePropagatorTheorem33Level =
  Propagator.balabanBackgroundGaugePropagatorTheorem33Level
balabanBackgroundAnalyticityTheorem34Level =
  Propagator.balabanBackgroundAnalyticityTheorem34Level

balabanGaugeFixingProposition5SourceLevel =
  GaugeFixing.balabanGaugeFixingProposition5SourceLevel
balabanGaugeFixingHalfContractionProfileLevel =
  GaugeFixing.balabanGaugeFixingHalfContractionProfileLevel

constraintInverseDerivativeFormulaLevel =
  Constraint.constraintInverseDerivativeFormulaLevel
constraintProjectionNineTermSecondVariationLevel =
  Constraint.constraintProjectionNineTermSecondVariationLevel

physicalBackgroundActionConstraintIdentificationInputsLevel =
  Background.physicalBackgroundActionConstraintIdentificationInputsLevel
physicalBackgroundNormConventionInputsLevel =
  Background.physicalBackgroundNormConventionInputsLevel

physicalBackgroundPropagatorRepositoryIdentificationInputsLevel =
  Propagator.physicalBackgroundPropagatorRepositoryIdentificationInputsLevel
physicalBackgroundPropagatorScaleWeightInputsLevel =
  Propagator.physicalBackgroundPropagatorScaleWeightInputsLevel

physicalGaugeFixingRepositoryIdentificationInputsLevel =
  GaugeFixing.physicalGaugeFixingRepositoryIdentificationInputsLevel

physicalAveragingJetIdentificationInputsLevel =
  Constraint.physicalAveragingJetIdentificationInputsLevel
physicalConstraintNormalInverseInputsLevel =
  Constraint.physicalConstraintNormalInverseInputsLevel

physicalClosureRound5SourceTheoremLedgerLevel : ProofLevel
physicalClosureRound5SourceTheoremLedgerLevel = machineChecked
