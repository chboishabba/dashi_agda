module DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound3Receipt where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound3Ledger as Ledger

record PhysicalClosureRound3Receipt : Set where
  constructor physicalClosureRound3Receipt
  field
    repositoryHead : String

    centeredOffsetCarrierChecked : Bool
    centeredFourBlockEnumerationChecked : Bool
    centeredBlockCardinalityChecked : Bool
    centeredPeriodicPathChecked : Bool
    centeredPermutationEndpointChecked : Bool
    centeredNoWrapInterfaceChecked : Bool
    centeredEndpointDecisionChecked : Bool
    centeredCompleteFamilyCertificateChecked : Bool

    dimockTrilogyScopeAudited : Bool
    normalizedReblockingAssemblyChecked : Bool
    largeFieldSlackAssemblyChecked : Bool
    clusterWithHolesSplitChecked : Bool
    rootedDecayVolumeAssemblyChecked : Bool
    connectedActivityStabilityChecked : Bool

    su2FixedRadiusEnvelopeChecked : Bool
    physicalChannelNamingAuditChecked : Bool
    hrBetaDimockAdapterChecked : Bool
    integratedRound3CarrierChecked : Bool

    validationWrapperChecked : Bool
    producerWrapperChecked : Bool
    roundPostulateFree : Bool

open PhysicalClosureRound3Receipt public

record AuthoritativePhysicalClosureRound3Evidence
    (receipt : PhysicalClosureRound3Receipt) : Set₁ where
  field
    centeredOffsetCarrierTypechecks : Set
    centeredFourBlockEnumerationTypechecks : Set
    centeredBlockCardinalityTypechecks : Set
    centeredPeriodicPathTypechecks : Set
    centeredPermutationEndpointTypechecks : Set
    centeredNoWrapInterfaceTypechecks : Set
    centeredEndpointDecisionTypechecks : Set
    centeredCompleteFamilyCertificateTypechecks : Set

    dimockTrilogyScopeAuditTypechecks : Set
    normalizedReblockingAssemblyTypechecks : Set
    largeFieldSlackAssemblyTypechecks : Set
    clusterWithHolesSplitTypechecks : Set
    rootedDecayVolumeAssemblyTypechecks : Set
    connectedActivityStabilityTypechecks : Set

    su2FixedRadiusEnvelopeTypechecks : Set
    physicalChannelNamingAuditTypechecks : Set
    hrBetaDimockAdapterTypechecks : Set
    integratedRound3CarrierTypechecks : Set

    validationWrapperTypechecks : Set
    producerWrapperTypechecks : Set
    roundHasNoPostulatesOrUnsolvedMetas : Set

open AuthoritativePhysicalClosureRound3Evidence public

physicalClosureRound3LedgerLevel = Ledger.physicalClosureRound3LedgerLevel

physicalClosureRound3TypecheckLevel : ProofLevel
physicalClosureRound3TypecheckLevel = conditional

physicalClosureRound3PostulateFreeLevel : ProofLevel
physicalClosureRound3PostulateFreeLevel = conditional
