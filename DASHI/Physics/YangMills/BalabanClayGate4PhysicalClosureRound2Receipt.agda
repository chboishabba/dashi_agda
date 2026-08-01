module DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound2Receipt where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound2Ledger as Ledger

record PhysicalClosureRound2Receipt : Set where
  constructor physicalClosureRound2Receipt
  field
    repositoryHead : String

    bfAverageScopeAudited : Bool
    cmp109CenteredNormalizationSeparated : Bool
    centeredDyadicConventionInequalityChecked : Bool
    dyadicTwoStepWeightChecked : Bool

    shortestContourEnumerationChecked : Bool
    contourPermutationSoundnessChecked : Bool
    contourEndpointIndependenceChecked : Bool
    fourDirectionCount24Checked : Bool

    exactFrechetChainRemainderChecked : Bool
    exactBilinearProductRemainderChecked : Bool
    operatorNormPipelineChecked : Bool

    quantitativeContractionUniquenessChecked : Bool
    relativeInverseKernelChecked : Bool
    federbushAndFaddeevPopovIFTReuseChecked : Bool
    finiteSquareInverseUpgradeChecked : Bool

    hrBetaFiveLocalChannelsChecked : Bool
    hrBetaFiveChannelUniformAssemblyChecked : Bool
    integratedRound2CarrierChecked : Bool

    validationWrapperChecked : Bool
    producerWrapperChecked : Bool
    roundPostulateFree : Bool

open PhysicalClosureRound2Receipt public

record AuthoritativePhysicalClosureRound2Evidence
    (receipt : PhysicalClosureRound2Receipt) : Set₁ where
  field
    bfAverageScopeTypechecks : Set
    centeredNormalizationSeparationTypechecks : Set
    centeredDyadicConventionInequalityTypechecks : Set
    dyadicTwoStepWeightTypechecks : Set

    shortestContourEnumerationTypechecks : Set
    contourPermutationSoundnessTypechecks : Set
    contourEndpointIndependenceTypechecks : Set
    fourDirectionCount24Typechecks : Set

    exactFrechetChainRemainderTypechecks : Set
    exactBilinearProductRemainderTypechecks : Set
    operatorNormPipelineTypechecks : Set

    quantitativeContractionUniquenessTypechecks : Set
    relativeInverseKernelTypechecks : Set
    sharedIFTReuseTypechecks : Set
    finiteSquareInverseUpgradeTypechecks : Set

    hrBetaFiveLocalChannelsTypechecks : Set
    hrBetaFiveChannelUniformAssemblyTypechecks : Set
    integratedRound2CarrierTypechecks : Set

    validationWrapperTypechecks : Set
    producerWrapperTypechecks : Set
    roundHasNoPostulatesOrUnsolvedMetas : Set

open AuthoritativePhysicalClosureRound2Evidence public

physicalClosureRound2LedgerLevel = Ledger.physicalClosureRound2LedgerLevel

physicalClosureRound2TypecheckLevel : ProofLevel
physicalClosureRound2TypecheckLevel = conditional

physicalClosureRound2PostulateFreeLevel : ProofLevel
physicalClosureRound2PostulateFreeLevel = conditional
