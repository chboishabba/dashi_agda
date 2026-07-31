module DASHI.Physics.YangMills.BalabanClayGate4SevenGroupFrontierReceipt where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4SevenGroupFrontierLedger as Ledger

record SevenGroupFrontierReceipt : Set where
  constructor sevenGroupFrontierReceipt
  field
    repositoryHead : String
    sourceAuditChecked : Bool
    cmp109LiteralIdentificationChecked : Bool
    projectedEndpointGeometryChecked : Bool
    localityDerivativeSupportChecked : Bool
    constantWeightSchurChecked : Bool
    finiteWeightCertificateChecked : Bool
    contractionResidualChecked : Bool
    fiveChannelSumChecked : Bool
    t3FiveChannelReuseChecked : Bool
    treeGaugeCoordinatesChecked : Bool
    treeGaugeBasisChecked : Bool
    t3SpectralDeterminantChecked : Bool
    hrBetaDominanceChecked : Bool

    printedCMP109PathFormulaChecked : Bool
    periodicPathWordChecked : Bool
    periodicWordPathConstructionChecked : Bool
    printedCMP109MapInstantiationChecked : Bool
    finiteHolonomyDerivativeChecked : Bool
    su2DexpInverseClosedFormChecked : Bool
    supportOverlapCompletionChecked : Bool
    weightedAdjointFubiniChecked : Bool
    weightedAdjointFormulaChecked : Bool
    totalSchurCertificateDecisionChecked : Bool
    spanningTreeGaugeSliceChecked : Bool
    canonicalOffTreeFreeBasisChecked : Bool
    canonicalOffTreeSU2BasisChecked : Bool
    coordinateMatrixEquivalenceChecked : Bool
    coordinateMatrixCompositionChecked : Bool
    determinantFactorizationChecked : Bool
    similaritySpectrumDeterminantChecked : Bool
    spectrumDeterminantCompletionChecked : Bool
    finiteProofEngineeringLedgerChecked : Bool

    validationWrapperChecked : Bool
    producerWrapperChecked : Bool
    sevenGroupTranchePostulateFree : Bool

open SevenGroupFrontierReceipt public

record AuthoritativeSevenGroupEvidence
    (receipt : SevenGroupFrontierReceipt) : Set₁ where
  field
    sourceAuditTypechecks : Set
    cmp109LiteralIdentificationTypechecks : Set
    projectedEndpointGeometryTypechecks : Set
    localityDerivativeSupportTypechecks : Set
    constantWeightSchurTypechecks : Set
    finiteWeightCertificateTypechecks : Set
    contractionResidualTypechecks : Set
    fiveChannelSumTypechecks : Set
    t3FiveChannelReuseTypechecks : Set
    treeGaugeCoordinatesTypechecks : Set
    treeGaugeBasisTypechecks : Set
    t3SpectralDeterminantTypechecks : Set
    hrBetaDominanceTypechecks : Set

    printedCMP109PathFormulaTypechecks : Set
    periodicPathWordTypechecks : Set
    periodicWordPathConstructionTypechecks : Set
    printedCMP109MapInstantiationTypechecks : Set
    finiteHolonomyDerivativeTypechecks : Set
    su2DexpInverseClosedFormTypechecks : Set
    supportOverlapCompletionTypechecks : Set
    weightedAdjointFubiniTypechecks : Set
    weightedAdjointFormulaTypechecks : Set
    totalSchurCertificateDecisionTypechecks : Set
    spanningTreeGaugeSliceTypechecks : Set
    canonicalOffTreeFreeBasisTypechecks : Set
    canonicalOffTreeSU2BasisTypechecks : Set
    coordinateMatrixEquivalenceTypechecks : Set
    coordinateMatrixCompositionTypechecks : Set
    determinantFactorizationTypechecks : Set
    similaritySpectrumDeterminantTypechecks : Set
    spectrumDeterminantCompletionTypechecks : Set
    finiteProofEngineeringLedgerTypechecks : Set

    validationWrapperTypechecks : Set
    producerWrapperTypechecks : Set
    trancheHasNoPostulatesOrUnsolvedMetas : Set

open AuthoritativeSevenGroupEvidence public

sevenGroupSourceAuditTypecheckLevel : ProofLevel
sevenGroupSourceAuditTypecheckLevel = conditional

sevenGroupCMP109LiteralTypecheckLevel : ProofLevel
sevenGroupCMP109LiteralTypecheckLevel = conditional

sevenGroupEndpointGeometryTypecheckLevel : ProofLevel
sevenGroupEndpointGeometryTypecheckLevel = conditional

sevenGroupLocalityDerivativeTypecheckLevel : ProofLevel
sevenGroupLocalityDerivativeTypecheckLevel = conditional

sevenGroupWeightedKernelTypecheckLevel : ProofLevel
sevenGroupWeightedKernelTypecheckLevel = conditional

sevenGroupFiveChannelTypecheckLevel : ProofLevel
sevenGroupFiveChannelTypecheckLevel = conditional

sevenGroupTreeGaugeTypecheckLevel : ProofLevel
sevenGroupTreeGaugeTypecheckLevel = conditional

sevenGroupSpectralDeterminantTypecheckLevel : ProofLevel
sevenGroupSpectralDeterminantTypecheckLevel = conditional

sevenGroupHRBetaTypecheckLevel : ProofLevel
sevenGroupHRBetaTypecheckLevel = conditional

finiteProofEngineeringTypecheckLevel : ProofLevel
finiteProofEngineeringTypecheckLevel = conditional

sevenGroupValidationWrapperTypecheckLevel : ProofLevel
sevenGroupValidationWrapperTypecheckLevel = conditional

sevenGroupProducerWrapperTypecheckLevel : ProofLevel
sevenGroupProducerWrapperTypecheckLevel = conditional

sevenGroupPostulateFreeLevel : ProofLevel
sevenGroupPostulateFreeLevel = conditional
