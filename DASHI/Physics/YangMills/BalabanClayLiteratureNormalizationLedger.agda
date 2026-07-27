module DASHI.Physics.YangMills.BalabanClayLiteratureNormalizationLedger where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT2ClusterCriterionComparisonExact
import DASHI.Physics.YangMills.BalabanClayT2EightWayFernandezProcacciExact
import DASHI.Physics.YangMills.BalabanClayT3OperatorSchurComplementExact
import DASHI.Physics.YangMills.BalabanClayT3UniformFluctuationSchurExact
import DASHI.Physics.YangMills.BalabanClayT4BetaNormalizationConventionExact
import DASHI.Physics.YangMills.BalabanClayT4RunningCouplingConventionBridgeExact
import DASHI.Physics.YangMills.BalabanClayT4SUNWilsonActionConventionExact
import DASHI.Physics.YangMills.BalabanDashenGrossCalibration
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact
import DASHI.Physics.YangMills.BalabanClayT5OSGramClosedPropertyExact

------------------------------------------------------------------------
-- This ledger records only implications and convention identities checked in
-- the cited modules.  It does not promote any literal Wilson/Haar analytic leaf.
------------------------------------------------------------------------

kpDobrushinFernandezProcacciHierarchyLevel : ProofLevel
kpDobrushinFernandezProcacciHierarchyLevel = machineChecked

extendedGruberKunzIdentificationSurfaceLevel : ProofLevel
extendedGruberKunzIdentificationSurfaceLevel = machineChecked

absoluteActivitySignConventionLevel : ProofLevel
absoluteActivitySignConventionLevel = machineChecked

eightWayFPCliqueArithmeticLevel : ProofLevel
eightWayFPCliqueArithmeticLevel = machineChecked

oneSixteenthToOneTwelfthFPSlackLevel : ProofLevel
oneSixteenthToOneTwelfthFPSlackLevel = machineChecked

rootedShellVersusFPConvergenceSeparationLevel : ProofLevel
rootedShellVersusFPConvergenceSeparationLevel = machineChecked

operatorSchurAlgebraLevel : ProofLevel
operatorSchurAlgebraLevel = machineChecked

uniformFluctuationCoercivityReductionLevel : ProofLevel
uniformFluctuationCoercivityReductionLevel = machineChecked

betaConventionFactorOfTwoLevel : ProofLevel
betaConventionFactorOfTwoLevel = machineChecked

betaZeroOverEightEqualsElevenOverTwentyFourLevel : ProofLevel
betaZeroOverEightEqualsElevenOverTwentyFourLevel = machineChecked

scaledSUNWilsonActionConventionLevel : ProofLevel
scaledSUNWilsonActionConventionLevel = machineChecked

scaledSUNWilsonGaugeInvarianceLevel : ProofLevel
scaledSUNWilsonGaugeInvarianceLevel = machineChecked

wilsonActionBetaConventionBridgeLevel : ProofLevel
wilsonActionBetaConventionBridgeLevel = machineChecked

dashenGrossConventionMetadataLevel : ProofLevel
dashenGrossConventionMetadataLevel = machineChecked

osGramTopologyClosureLevel : ProofLevel
osGramTopologyClosureLevel = machineChecked

osReflectionSequentialClosednessLevel : ProofLevel
osReflectionSequentialClosednessLevel = machineChecked

literalCriterionMajorantIdentificationLevel : ProofLevel
literalCriterionMajorantIdentificationLevel = conditional

literalEightExtensionCliqueGeometryLevel : ProofLevel
literalEightExtensionCliqueGeometryLevel = conditional

literalUniformFluctuationCoercivityLevel : ProofLevel
literalUniformFluctuationCoercivityLevel = conditional

literalWilsonPlaquetteCoefficientLevel : ProofLevel
literalWilsonPlaquetteCoefficientLevel = conditional

literalOSGramConvergenceLevel : ProofLevel
literalOSGramConvergenceLevel = conditional
