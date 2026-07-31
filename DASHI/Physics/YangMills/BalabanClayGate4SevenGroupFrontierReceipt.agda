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

sevenGroupValidationWrapperTypecheckLevel : ProofLevel
sevenGroupValidationWrapperTypecheckLevel = conditional

sevenGroupProducerWrapperTypecheckLevel : ProofLevel
sevenGroupProducerWrapperTypecheckLevel = conditional

sevenGroupPostulateFreeLevel : ProofLevel
sevenGroupPostulateFreeLevel = conditional
