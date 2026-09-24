{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayGoal1ExactResidualMaxCutRound496Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND496: EXACT RESIDUAL CLAY MAX-CUT
--
-- This is the authoritative proof-search board after:
--
--   * source-correct Wilson B frontier R491-R493;
--   * WEXT decomposition R494;
--   * representation-first continuum R476/R480/R481/R483/R484;
--   * cylinder-measure representation decomposition R495;
--   * fixed-G / SU(2)-validation firewalls R477/R478;
--   * current A1 and C source-cut decompositions R473/R475.
--
-- No constructor-choice equality appears as a research leaf.
-- No projective-Prokhorov/coercivity fallback is counted when the preferred
-- source-native route bypasses it.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayGoal1A1SourceCutRound473Exact as A1
import DASHI.Physics.YangMills.BalabanA2BetaMarkSourceCoordinateRound250Exact as A2
import DASHI.Physics.YangMills.YangMillsClayGoal1SourceNativeContinuumRound457Exact as A3Source
import DASHI.Physics.YangMills.YangMillsClaySourceNativeA3MaxCutRound504Exact as A3SourceCut
import DASHI.Physics.YangMills.YangMillsCylinderMeasureRepresentationMaxCutRound495Exact as Measure
import DASHI.Physics.YangMills.YangMillsCylinderPremeasureFromFiniteExpectationRound498Exact as Premeasure
import DASHI.Physics.YangMills.YangMillsPhysicalCylinderRepresentationRound499Exact as PhysicalRep
import DASHI.Physics.YangMills.YangMillsClayRepresentedSourceNativeA3Round497Exact as A3Direct
import DASHI.Physics.YangMills.YangMillsClayT5MomentToOS05Round464Exact as A45
import DASHI.Physics.YangMills.YangMillsClayMomentOS05MaxCutRound500Exact as A45Cut
import DASHI.Physics.YangMills.YangMillsClayPublishedFiniteOSMaxCutRound505Exact as FiniteOSCut
import DASHI.Physics.YangMills.YangMillsClayRepresentedOS05Round481Exact as A45Rep
import DASHI.Physics.YangMills.YangMillsClayRepresentedOSExtensionalityMaxCutRound501Exact as A45Ext

import DASHI.Physics.YangMills.BalabanWilsonWEXTMaxCutRound494Exact as WEXT
import DASHI.Physics.YangMills.BalabanClayCanonicalBMaxCutRound493Exact as B
import DASHI.Physics.YangMills.YangMillsClayGoal1MassGapSemanticAttachmentRound458Exact as BSem
import DASHI.Physics.YangMills.YangMillsClayMassGapSemanticMaxCutRound503Exact as BSemCut

import DASHI.Physics.YangMills.YangMillsClayGoal1CSourceCutRound475Exact as C

import DASHI.Physics.YangMills.BalabanGroupParametricFiveBlockSignedG2Exact as G1
import DASHI.Physics.YangMills.YangMillsClayGoal1NontrivialityAttachmentRound468Exact as G2
import DASHI.Physics.YangMills.YangMillsClayNontrivialitySemanticMaxCutRound502Exact as G2Cut

import DASHI.Physics.YangMills.YangMillsClayRepresentedTerminalRound484Exact as Terminal
import DASHI.Physics.YangMills.YangMillsClayTerminalContractSemanticMaxCutRound506Exact as Contract

data ResidualLeaf : Set where
  -- Terminal structural/T1 semantic contract.
  structuralCompactSimpleSemantics : ResidualLeaf
  structuralFourDimensionalEuclideanSemantics : ResidualLeaf
  structuralCompactSimpleParameterizationSemantics : ResidualLeaf
  t1FiniteVolumeCutoffMeasureSemantics : ResidualLeaf
  t1ReflectionPositiveRegularizationSemantics : ResidualLeaf
  t1UltravioletNormalizationSemantics : ResidualLeaf
  t1AsymptoticallyFreeTrajectorySemantics : ResidualLeaf
  t1GaugeSymmetryPreservedSemantics : ResidualLeaf
  t1LocalityPreservedSemantics : ResidualLeaf
  t1EuclideanCovariancePreservedSemantics : ResidualLeaf
  t1ReflectionPositivityPreservedSemantics : ResidualLeaf
  t1PositivityNormalizationPreservedSemantics : ResidualLeaf
  t1VolumeCutoffCompatibilitySemantics : ResidualLeaf
  t3AcceptedWightmanOrOSSemantics : ResidualLeaf
  t3ReconstructedHilbertSpaceSemantics : ResidualLeaf
  t3PositiveSelfAdjointHamiltonianSemantics : ResidualLeaf
  t4GaugeInvariantLocalObservableSemantics : ResidualLeaf
  t4CurvatureCorrespondenceSemantics : ResidualLeaf
  t4CurvatureGaugeInvariantSemantics : ResidualLeaf
  t4CurvatureLocalitySemantics : ResidualLeaf
  t4ShortDistanceAFSemantics : ResidualLeaf
  t4StressTensorAndOPESemantics : ResidualLeaf
  t4PhysicalOPECoefficientSemantics : ResidualLeaf
  t4PhysicalOPERemainderSemantics : ResidualLeaf

  -- Published finite OS same-object attachments.
  aFiniteEuclideanSameObjectAttachment : ResidualLeaf
  aFiniteBosonicSameObjectAttachment : ResidualLeaf
  aFiniteWilsonRPSameObjectAttachment : ResidualLeaf

  -- A1 current-step beta source.
  a1WilsonHessianVariation : ResidualLeaf
  a1AveragingConstraintVariation : ResidualLeaf
  a1GaugeProjectionVariation : ResidualLeaf
  a1WQRAssembly : ResidualLeaf
  a1ConstrainedGaussianMixedCoefficient : ResidualLeaf
  a1PhysicalJetFiveChannelSplit : ResidualLeaf
  a1FourJointReceiptEvaluation : ResidualLeaf

  -- A2 history-shell/source coordinate.
  a2BetaMarkGeneratedHistoryShell : ResidualLeaf

  -- A3 represented continuum.
  a3StressDensityIsLiteralFiniteMeasure : ResidualLeaf
  a3FiniteFamilyContinuumLimit : ResidualLeaf
  a3LiteralSchwingerBelongs : ResidualLeaf
  a3SourceOSIsLiteralSchwinger : ResidualLeaf
  a3CylinderEventIndicatorSemantics : ResidualLeaf
  a3ProjectiveEventExpectationConsistency : ResidualLeaf
  a3ContinuityAtEmpty : ResidualLeaf
  a3CylinderExpectationIntegralIdentification : ResidualLeaf

  -- A4/A5.
  a45QuantitativeFiniteExpectationAttachment : ResidualLeaf
  a4FiniteRegularityFromQuantitativeBounds : ResidualLeaf
  a5FiniteGrowthFromQuantitativeBounds : ResidualLeaf
  a4RepresentedRegularityExtensionality : ResidualLeaf
  a5RepresentedGrowthExtensionality : ResidualLeaf

  -- B source-correct Wilson + same-H.
  bWilsonTwoMarkExpansion : ResidualLeaf
  bWilsonConnectingWeightTail : ResidualLeaf
  bSameHamiltonianTransferCoordinate : ResidualLeaf
  bVacuumSectorPositiveEnergySemantics : ResidualLeaf
  bStrictPositiveMassGapSemantics : ResidualLeaf
  bPhysicalScaleLowerBoundSemantics : ResidualLeaf
  bNoSpectralPollutionSemantics : ResidualLeaf
  bGapAndClusteringDerivedSemantics : ResidualLeaf

  -- C local QFT.
  c1MarkedSourceHilbertModulus : ResidualLeaf
  c1CurvatureGaugeLocalSemantics : ResidualLeaf
  c2PhysicalRemainderIsCompositeTail : ResidualLeaf
  c3OneStepAFRGIdentification : ResidualLeaf
  c4FiniteStressInsertionIsCMP119Local : ResidualLeaf
  c4StressCompletionIsCompletedMarkedStress : ResidualLeaf
  c4CompletedStressIsClayStress : ResidualLeaf
  c4LiteralDensityMetricDerivative : ResidualLeaf
  c4DensityAnchoredLaneInstantiation : ResidualLeaf

  -- G / all groups + same-system nontriviality.
  g1ArbitraryCompactSimpleSourceMap : ResidualLeaf
  g2WitnessIsLiteralNontriviality : ResidualLeaf
  g2WitnessPreservedInLiteralLimit : ResidualLeaf

leafLevel : ResidualLeaf → ProofLevel
leafLevel structuralCompactSimpleSemantics =
  Contract.literalCompactSimpleGroupSemanticsLevel
leafLevel structuralFourDimensionalEuclideanSemantics =
  Contract.literalFourDimensionalEuclideanSpacetimeSemanticsLevel
leafLevel structuralCompactSimpleParameterizationSemantics =
  Contract.literalCompactSimpleParameterizationPreservedSemanticsLevel
leafLevel t1FiniteVolumeCutoffMeasureSemantics =
  Contract.literalFiniteVolumeCutoffMeasureSemanticsLevel
leafLevel t1ReflectionPositiveRegularizationSemantics =
  Contract.literalReflectionPositiveRegularizationSemanticsLevel
leafLevel t1UltravioletNormalizationSemantics =
  Contract.literalUltravioletYangMillsNormalizationSemanticsLevel
leafLevel t1AsymptoticallyFreeTrajectorySemantics =
  Contract.literalAsymptoticallyFreeScaleTrajectorySemanticsLevel
leafLevel t1GaugeSymmetryPreservedSemantics =
  Contract.literalGaugeSymmetryPreservedSemanticsLevel
leafLevel t1LocalityPreservedSemantics =
  Contract.literalLocalityPreservedSemanticsLevel
leafLevel t1EuclideanCovariancePreservedSemantics =
  Contract.literalEuclideanCovariancePreservedSemanticsLevel
leafLevel t1ReflectionPositivityPreservedSemantics =
  Contract.literalReflectionPositivityPreservedSemanticsLevel
leafLevel t1PositivityNormalizationPreservedSemantics =
  Contract.literalPositivityNormalizationPreservedSemanticsLevel
leafLevel t1VolumeCutoffCompatibilitySemantics =
  Contract.literalVolumeCutoffCompatibilitySemanticsLevel
leafLevel t3AcceptedWightmanOrOSSemantics =
  Contract.literalAcceptedWightmanOrOSAxiomsSemanticsLevel
leafLevel t3ReconstructedHilbertSpaceSemantics =
  Contract.literalReconstructedHilbertSpaceSemanticsLevel
leafLevel t3PositiveSelfAdjointHamiltonianSemantics =
  Contract.literalPositiveSelfAdjointHamiltonianSemanticsLevel
leafLevel t4GaugeInvariantLocalObservableSemantics =
  Contract.literalGaugeInvariantLocalObservableSemanticsLevel
leafLevel t4CurvatureCorrespondenceSemantics =
  Contract.literalCurvatureOperatorCorrespondenceSemanticsLevel
leafLevel t4CurvatureGaugeInvariantSemantics =
  Contract.literalCurvatureOperatorGaugeInvariantSemanticsLevel
leafLevel t4CurvatureLocalitySemantics =
  Contract.literalCurvatureOperatorLocalitySemanticsLevel
leafLevel t4ShortDistanceAFSemantics =
  Contract.literalShortDistanceAsymptoticFreedomSemanticsLevel
leafLevel t4StressTensorAndOPESemantics =
  Contract.literalStressTensorAndOPESemanticsLevel
leafLevel t4PhysicalOPECoefficientSemantics =
  Contract.literalPhysicalOPECoefficientSemanticsLevel
leafLevel t4PhysicalOPERemainderSemantics =
  Contract.literalPhysicalOPERemainderSemanticsLevel

leafLevel aFiniteEuclideanSameObjectAttachment =
  FiniteOSCut.literalRound505EuclideanSameObjectAttachmentLevel
leafLevel aFiniteBosonicSameObjectAttachment =
  FiniteOSCut.literalRound505BosonicSameObjectAttachmentLevel
leafLevel aFiniteWilsonRPSameObjectAttachment =
  FiniteOSCut.literalRound505WilsonRPSameObjectAttachmentLevel

leafLevel a1WilsonHessianVariation =
  A1.a1aLiteralWilsonHessianVariationLevel
leafLevel a1AveragingConstraintVariation =
  A1.a1aLiteralAveragingConstraintVariationLevel
leafLevel a1GaugeProjectionVariation =
  A1.a1aLiteralGaugeProjectionVariationLevel
leafLevel a1WQRAssembly =
  A1.a1aLiteralWQRAssemblyLevel
leafLevel a1ConstrainedGaussianMixedCoefficient =
  A1.a1bConstrainedGaussianMixedCoefficientLevel
leafLevel a1PhysicalJetFiveChannelSplit =
  A1.a1cPhysicalJetFiveChannelSplitLevel
leafLevel a1FourJointReceiptEvaluation =
  A1.a1dFourJointReceiptEvaluationLevel

leafLevel a2BetaMarkGeneratedHistoryShell =
  A2.literalCMP116BetaMarkIsGeneratedHistoryShellLevel

leafLevel a3StressDensityIsLiteralFiniteMeasure =
  A3SourceCut.literalRound504StressDensityIsLiteralFiniteMeasureLevel
leafLevel a3FiniteFamilyContinuumLimit =
  A3SourceCut.literalRound504FiniteFamilyContinuumLimitLevel
leafLevel a3LiteralSchwingerBelongs =
  A3SourceCut.literalRound504LiteralSchwingerBelongsLevel
leafLevel a3SourceOSIsLiteralSchwinger =
  A3SourceCut.literalRound504SourceOSIsLiteralSchwingerLevel
leafLevel a3CylinderEventIndicatorSemantics =
  PhysicalRep.literalRound499CylinderEventIndicatorSemanticsLevel
leafLevel a3ProjectiveEventExpectationConsistency =
  PhysicalRep.literalRound499ProjectiveEventExpectationConsistencyLevel
leafLevel a3ContinuityAtEmpty =
  PhysicalRep.literalRound499ContinuityAtEmptyLevel
leafLevel a3CylinderExpectationIntegralIdentification =
  PhysicalRep.literalRound499CylinderExpectationIdentificationLevel
leafLevel a45QuantitativeFiniteExpectationAttachment =
  A45Cut.literalRound500QuantitativeFiniteExpectationAttachmentLevel
leafLevel a4FiniteRegularityFromQuantitativeBounds =
  A45Cut.literalRound500FiniteRegularityFromQuantitativeBoundsLevel
leafLevel a5FiniteGrowthFromQuantitativeBounds =
  A45Cut.literalRound500FiniteGrowthFromQuantitativeBoundsLevel
leafLevel a4RepresentedRegularityExtensionality =
  A45Ext.literalRound501RegularityExtensionalityLevel
leafLevel a5RepresentedGrowthExtensionality =
  A45Ext.literalRound501GrowthExtensionalityLevel

leafLevel bWilsonTwoMarkExpansion =
  WEXT.literalRound494WilsonTwoMarkExpansionLevel
leafLevel bWilsonConnectingWeightTail =
  WEXT.literalRound494WilsonConnectingWeightTailLevel
leafLevel bSameHamiltonianTransferCoordinate =
  B.bSameHamiltonianLevel
leafLevel bVacuumSectorPositiveEnergySemantics =
  BSemCut.literalRound503VacuumSectorPositiveEnergySemanticsLevel
leafLevel bStrictPositiveMassGapSemantics =
  BSemCut.literalRound503StrictPositiveMassGapSemanticsLevel
leafLevel bPhysicalScaleLowerBoundSemantics =
  BSemCut.literalRound503PhysicalScaleLowerBoundSemanticsLevel
leafLevel bNoSpectralPollutionSemantics =
  BSemCut.literalRound503NoSpectralPollutionSemanticsLevel
leafLevel bGapAndClusteringDerivedSemantics =
  BSemCut.literalRound503GapAndClusteringDerivedSemanticsLevel

leafLevel c1MarkedSourceHilbertModulus =
  C.c1MarkedSourceHilbertModulusLevel
leafLevel c1CurvatureGaugeLocalSemantics =
  C.c1CurvatureGaugeLocalSemanticsLevel
leafLevel c2PhysicalRemainderIsCompositeTail =
  C.c2PhysicalRemainderIsCompositeTailLevel
leafLevel c3OneStepAFRGIdentification =
  C.c3OneStepAFRGIdentificationLevel
leafLevel c4FiniteStressInsertionIsCMP119Local =
  C.c4FiniteStressInsertionIsCMP119LocalLevel
leafLevel c4StressCompletionIsCompletedMarkedStress =
  C.c4StressCompletionIsCompletedMarkedStressLevel
leafLevel c4CompletedStressIsClayStress =
  C.c4CompletedStressIsClayStressLevel
leafLevel c4LiteralDensityMetricDerivative =
  C.c4LiteralDensityMetricDerivativeLevel
leafLevel c4DensityAnchoredLaneInstantiation =
  C.c4DensityAnchoredLaneInstantiationLevel

leafLevel g1ArbitraryCompactSimpleSourceMap =
  G1.physicalGroupParametricFiveBlockSourceMapLevel
leafLevel g2WitnessIsLiteralNontriviality =
  G2Cut.literalRound502WitnessIsLiteralNontrivialityLevel
leafLevel g2WitnessPreservedInLiteralLimit =
  G2Cut.literalRound502WitnessPreservedInLiteralLimitLevel

residualLeaves : List ResidualLeaf
residualLeaves =
    structuralCompactSimpleSemantics
  ∷ structuralFourDimensionalEuclideanSemantics
  ∷ structuralCompactSimpleParameterizationSemantics
  ∷ t1FiniteVolumeCutoffMeasureSemantics
  ∷ t1ReflectionPositiveRegularizationSemantics
  ∷ t1UltravioletNormalizationSemantics
  ∷ t1AsymptoticallyFreeTrajectorySemantics
  ∷ t1GaugeSymmetryPreservedSemantics
  ∷ t1LocalityPreservedSemantics
  ∷ t1EuclideanCovariancePreservedSemantics
  ∷ t1ReflectionPositivityPreservedSemantics
  ∷ t1PositivityNormalizationPreservedSemantics
  ∷ t1VolumeCutoffCompatibilitySemantics
  ∷ t3AcceptedWightmanOrOSSemantics
  ∷ t3ReconstructedHilbertSpaceSemantics
  ∷ t3PositiveSelfAdjointHamiltonianSemantics
  ∷ t4GaugeInvariantLocalObservableSemantics
  ∷ t4CurvatureCorrespondenceSemantics
  ∷ t4CurvatureGaugeInvariantSemantics
  ∷ t4CurvatureLocalitySemantics
  ∷ t4ShortDistanceAFSemantics
  ∷ t4StressTensorAndOPESemantics
  ∷ t4PhysicalOPECoefficientSemantics
  ∷ t4PhysicalOPERemainderSemantics
  ∷     aFiniteEuclideanSameObjectAttachment
  ∷ aFiniteBosonicSameObjectAttachment
  ∷ aFiniteWilsonRPSameObjectAttachment
  ∷ a1WilsonHessianVariation
  ∷ a1AveragingConstraintVariation
  ∷ a1GaugeProjectionVariation
  ∷ a1WQRAssembly
  ∷ a1ConstrainedGaussianMixedCoefficient
  ∷ a1PhysicalJetFiveChannelSplit
  ∷ a1FourJointReceiptEvaluation
  ∷ a2BetaMarkGeneratedHistoryShell
  ∷ a3StressDensityIsLiteralFiniteMeasure
  ∷ a3FiniteFamilyContinuumLimit
  ∷ a3LiteralSchwingerBelongs
  ∷ a3SourceOSIsLiteralSchwinger
  ∷ a3CylinderEventIndicatorSemantics
  ∷ a3ProjectiveEventExpectationConsistency
  ∷ a3ContinuityAtEmpty
  ∷ a3CylinderExpectationIntegralIdentification
  ∷ a45QuantitativeFiniteExpectationAttachment
  ∷ a4FiniteRegularityFromQuantitativeBounds
  ∷ a5FiniteGrowthFromQuantitativeBounds
  ∷ a4RepresentedRegularityExtensionality
  ∷ a5RepresentedGrowthExtensionality
  ∷ bWilsonTwoMarkExpansion
  ∷ bWilsonConnectingWeightTail
  ∷ bSameHamiltonianTransferCoordinate
  ∷ bVacuumSectorPositiveEnergySemantics
  ∷ bStrictPositiveMassGapSemantics
  ∷ bPhysicalScaleLowerBoundSemantics
  ∷ bNoSpectralPollutionSemantics
  ∷ bGapAndClusteringDerivedSemantics
  ∷ c1MarkedSourceHilbertModulus
  ∷ c1CurvatureGaugeLocalSemantics
  ∷ c2PhysicalRemainderIsCompositeTail
  ∷ c3OneStepAFRGIdentification
  ∷ c4FiniteStressInsertionIsCMP119Local
  ∷ c4StressCompletionIsCompletedMarkedStress
  ∷ c4CompletedStressIsClayStress
  ∷ c4LiteralDensityMetricDerivative
  ∷ c4DensityAnchoredLaneInstantiation
  ∷ g1ArbitraryCompactSimpleSourceMap
  ∷ g2WitnessIsLiteralNontriviality
  ∷ g2WitnessPreservedInLiteralLimit
  ∷ []

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

residualLeafCount : Nat
residualLeafCount = listLength residualLeaves

------------------------------------------------------------------------
-- Compiler/non-research payments deliberately excluded from the live leaves.
------------------------------------------------------------------------

finiteProjectivePremeasureAssemblyLevel : ProofLevel
finiteProjectivePremeasureAssemblyLevel =
  Premeasure.round498ProjectivePremeasureCompilerLevel

physicalRepresentationAssemblyLevel : ProofLevel
physicalRepresentationAssemblyLevel =
  PhysicalRep.round499PhysicalRepresentationCompilerLevel

finiteOS05AssemblyLevel : ProofLevel
finiteOS05AssemblyLevel =
  A45Cut.round500OS05CompilerLevel

publishedFiniteOSAssemblyLevel : ProofLevel
publishedFiniteOSAssemblyLevel =
  FiniteOSCut.round505FiniteOSAssemblyCompilerLevel

representedOSExtensionalityCompilerLevel : ProofLevel
representedOSExtensionalityCompilerLevel =
  A45Ext.round501RepresentedOSTransportCompilerLevel

massGapSemanticAssemblyLevel : ProofLevel
massGapSemanticAssemblyLevel =
  BSemCut.round503T2SemanticCompilerLevel

nontrivialitySemanticAssemblyLevel : ProofLevel
nontrivialitySemanticAssemblyLevel =
  G2Cut.round502GaussianWardGapCompilerLevel

caratheodoryExtensionLevel : ProofLevel
caratheodoryExtensionLevel =
  Measure.round495CaratheodoryExtensionAuthorityLevel

wextFiniteTriangleLevel : ProofLevel
wextFiniteTriangleLevel =
  WEXT.round494FiniteTriangleLevel

wextAssemblyLevel : ProofLevel
wextAssemblyLevel =
  WEXT.round494WEXTCompilerLevel

bGeometricDecayCompilerLevel : ProofLevel
bGeometricDecayCompilerLevel =
  B.bGeometricDecayCompilerLevel

bSpectralTransferLevel : ProofLevel
bSpectralTransferLevel =
  B.bStandardSpectralTransferLevel

terminalRepresentationFirstCompilerLevel : ProofLevel
terminalRepresentationFirstCompilerLevel =
  Terminal.round484RepresentedTerminalCompilerLevel

terminalSemanticInventoryCompilerLevel : ProofLevel
terminalSemanticInventoryCompilerLevel =
  Contract.round506TerminalSemanticInventoryCompilerLevel

representedA3SemanticCompilerLevel : ProofLevel
representedA3SemanticCompilerLevel =
  A3Direct.round497RepresentedSourceNativeA3CompilerLevel

sourceNativeA3AssemblyLevel : ProofLevel
sourceNativeA3AssemblyLevel =
  A3SourceCut.round504SameFamilyRecoveryCompilerLevel

------------------------------------------------------------------------
-- Max-cut firewalls.
------------------------------------------------------------------------

constructorChoiceEqualitiesCountedAsResidualLeaves : Bool
constructorChoiceEqualitiesCountedAsResidualLeaves = false

projectiveProkhorovFallbackCountedAsResidualLeaf : Bool
projectiveProkhorovFallbackCountedAsResidualLeaf = false

globalCoercivityFallbackCountedAsResidualLeaf : Bool
globalCoercivityFallbackCountedAsResidualLeaf = false

su2ValidationCountedAsGenericCompactSimplePremise : Bool
su2ValidationCountedAsGenericCompactSimplePremise = false

uniformConstantAcrossAllCompactSimpleGroupsRequired : Bool
uniformConstantAcrossAllCompactSimpleGroupsRequired = false

printedJEqualsWilsonObservableCountedAsResidualLeaf : Bool
printedJEqualsWilsonObservableCountedAsResidualLeaf = false

wholeMeasureRecordEqualityCountedAsResidualLeaf : Bool
wholeMeasureRecordEqualityCountedAsResidualLeaf = false

independentContinuumSchwingerChoiceCountedAsResidualLeaf : Bool
independentContinuumSchwingerChoiceCountedAsResidualLeaf = false

independentFourthCumulantCountedAsResidualLeaf : Bool
independentFourthCumulantCountedAsResidualLeaf = false

round496ResidualMaxCutCompilerLevel : ProofLevel
round496ResidualMaxCutCompilerLevel = machineChecked

clayCompletionClaimed : Bool
clayCompletionClaimed = false
