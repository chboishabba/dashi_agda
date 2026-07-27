module DASHI.Physics.YangMills.BalabanClayT2LiteralPhysicalLossWitnessExact where

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT2LiteralActivityLossConstantsExact as Loss

------------------------------------------------------------------------
-- Literature normalization.
--
-- Tadeusz Bałaban, "Ultraviolet Stability of Three-Dimensional Lattice Pure
-- Gauge Field Theories", Communications in Mathematical Physics 102 (1985),
-- 255--275. DOI: 10.1007/BF01229380
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. II. Cluster Expansions", Communications in Mathematical Physics
-- 116 (1988), 1--22. DOI: 10.1007/BF01239022
--
-- Barry Simon, "Trace Ideals and Their Applications", second edition,
-- American Mathematical Society (2005). DOI: 10.1090/surv/120
--
-- Sergio Blanes and Fernando Casas, "On the Convergence and Optimization of
-- the Baker--Campbell--Hausdorff Formula", Linear Algebra and its Applications
-- 378 (2004), 135--158. DOI: 10.1016/j.laa.2003.09.010
--
-- Relationship: Balaban owns the physical small/large-field and cluster
-- architecture; Simon owns the trace-log estimate; Blanes--Casas is a generic
-- BCH comparison only.  The literal SU(2) plaquette owner remains quaternionic.
------------------------------------------------------------------------

record LiteralPhysicalActivityLossWitness
    (Link Polymer Scalar Index Operator Scale Activity Regime Lie Quaternion : Set)
    : Set₂ where
  field
    haarData : Loss.SU2HaarLossData Link Polymer Scalar
    determinantData :
      Loss.RelativeDeterminantLossData Index Polymer Operator Scalar
    bchData :
      Loss.SU2QuaternionPlaquetteBCHData
        Link Lie Quaternion Scalar Polymer
    localizationData :
      Loss.LocalizationLossData Scale Polymer Activity Scalar
    patchData :
      Loss.PatchActivityLossData Regime Polymer Activity Scalar
    netGainData : Loss.LiteralActivityNetGainData Scale Polymer Scalar

    -- Physical incidence/normalization facts not present in the abstract loss
    -- records.
    linksPerBlockUniformBound : ∀ polymer → Set
    plaquettesPerBlockUniformBound : ∀ polymer → Set
    determinantBlockDimensionUniform : ∀ index polymer → Set

open LiteralPhysicalActivityLossWitness public

negativeLogSinOverXQuadraticBoundLiteral :
  ∀ {Link Polymer Scalar Index Operator Scale Activity Regime Lie Quaternion}
    (dataSet : LiteralPhysicalActivityLossWitness
      Link Polymer Scalar Index Operator Scale Activity Regime Lie Quaternion)
    link → Loss.InChart (haarData dataSet) link →
  Loss.LessEqual (haarData dataSet)
    (Loss.negativeLogSinc (haarData dataSet) link)
    (Loss.multiply (haarData dataSet)
      (Loss.haarQuadraticConstant (haarData dataSet) link)
      (Loss.square (haarData dataSet)
        (Loss.norm (haarData dataSet) link)
        (Loss.one (haarData dataSet))))
negativeLogSinOverXQuadraticBoundLiteral dataSet =
  Loss.negativeLogSinOverXQuadraticBound (haarData dataSet)

haarLogDensityQuadraticBoundLiteral dataSet =
  Loss.haarLogDensityQuadraticBound (haarData dataSet)

haarJacobianPolymerLossBoundLiteral dataSet =
  Loss.haarJacobianPolymerLossBound (haarData dataSet)

physicalRelativeHessianNormBelowHalfLiteral :
  ∀ {Link Polymer Scalar Index Operator Scale Activity Regime Lie Quaternion}
    (dataSet : LiteralPhysicalActivityLossWitness
      Link Polymer Scalar Index Operator Scale Activity Regime Lie Quaternion)
    index → Loss.SmallFieldIndex (determinantData dataSet) index →
  Loss.LessEqual (determinantData dataSet)
    (Loss.operatorNorm (determinantData dataSet)
      (Loss.relativeHessian (determinantData dataSet) index))
    (Loss.half (determinantData dataSet))
physicalRelativeHessianNormBelowHalfLiteral dataSet =
  Loss.relativeHessianNormBelowHalf (determinantData dataSet)

localizedTraceNormPerBlockBoundLiteral dataSet =
  Loss.traceNormPerPolymerBlockBound (determinantData dataSet)

finiteRangeTraceLocalizationLiteral dataSet =
  Loss.finiteRangeTraceLocalization (determinantData dataSet)

determinantPolymerConnectedDecompositionLiteral dataSet =
  Loss.determinantPolymerConnectedDecomposition (determinantData dataSet)

fluctuationDeterminantPolymerLossBoundLiteral dataSet =
  Loss.fluctuationDeterminantPolymerLossBound (determinantData dataSet)

fourLinkQuaternionLogExpansionExact dataSet =
  Loss.fourLinkPlaquetteBCHSecondOrderExact (bchData dataSet)

plaquetteQuaternionRemainderCubicBoundLiteral dataSet =
  Loss.plaquetteBCHRemainderCubicBound (bchData dataSet)

polymerBCHRemainderSumBoundLiteral dataSet =
  Loss.polymerBCHRemainderSumBound (bchData dataSet)

bchActionExponentialLossBoundLiteral dataSet =
  Loss.bchActionExponentialLossBound (bchData dataSet)

localizationDerivativeOrderGainLiteral dataSet =
  Loss.localizationDerivativeOrderGain (localizationData dataSet)

localizationCollarCountingBoundLiteral dataSet =
  Loss.localizationCollarCountingBound (localizationData dataSet)

localizationPolymerLossBoundLiteral dataSet =
  Loss.localizationPolymerLossBound (localizationData dataSet)

boundaryPatchNormComparisonLiteral dataSet =
  Loss.boundaryPatchNormComparison (patchData dataSet)

interfacePatchNormComparisonLiteral dataSet =
  Loss.interfacePatchNormComparison (patchData dataSet)

cornerPatchNormComparisonLiteral dataSet =
  Loss.cornerPatchNormComparison (patchData dataSet)

nestedPatchNormComparisonLiteral dataSet =
  Loss.nestedPatchNormComparison (patchData dataSet)

patchLossUniformAcrossRegimesLiteral dataSet =
  Loss.patchLossUniformAcrossRegimes (patchData dataSet)

physicalNetGainAtLeastLogSixteenLiteral dataSet =
  Loss.physicalNetGainAtLeastLogSixteen (netGainData dataSet)

literalWilsonActivityPerTraversalBelowOneSixteenth :
  ∀ {Link Polymer Scalar Index Operator Scale Activity Regime Lie Quaternion}
    (dataSet : LiteralPhysicalActivityLossWitness
      Link Polymer Scalar Index Operator Scale Activity Regime Lie Quaternion)
    scale polymer →
  Loss.LessEqual (netGainData dataSet)
    (Loss.activity (netGainData dataSet) scale polymer)
    (Loss.oneSixteenth (netGainData dataSet) scale polymer)
literalWilsonActivityPerTraversalBelowOneSixteenth dataSet =
  Loss.literalWilsonActivityPerTraversalBelowOneSixteenth (netGainData dataSet)

literalHaarLossAdapterLevel : ProofLevel
literalHaarLossAdapterLevel = machineChecked

literalDeterminantLossAdapterLevel : ProofLevel
literalDeterminantLossAdapterLevel = machineChecked

literalQuaternionLocalizationPatchAdapterLevel : ProofLevel
literalQuaternionLocalizationPatchAdapterLevel = machineChecked

literalOneSixteenthClosureAdapterLevel : ProofLevel
literalOneSixteenthClosureAdapterLevel = machineChecked

literalPhysicalLossConstantInputsLevel : ProofLevel
literalPhysicalLossConstantInputsLevel = conditional
