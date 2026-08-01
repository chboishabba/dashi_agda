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
    periodicContourFamilyChecked : Bool

    exactFrechetChainRemainderChecked : Bool
    exactBilinearProductRemainderChecked : Bool
    operatorNormPipelineChecked : Bool
    dyadicSchurFromNormPipelineChecked : Bool

    quantitativeContractionUniquenessChecked : Bool
    quantitativeBallConstructionChecked : Bool
    relativeInverseKernelChecked : Bool
    federbushAndFaddeevPopovIFTReuseChecked : Bool
    finiteSquareInverseUpgradeChecked : Bool

    su2DefectPipelineChecked : Bool
    resolventDefectPipelineChecked : Bool
    resolvedTwoFamilyDefectsChecked : Bool
    t3ResolvedFiveChannelReuseChecked : Bool

    hrBetaFiveLocalChannelsChecked : Bool
    hrBetaFiveChannelUniformAssemblyChecked : Bool
    integratedRound2CarrierChecked : Bool
    analyticReductionLedgerChecked : Bool

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
    periodicContourFamilyTypechecks : Set

    exactFrechetChainRemainderTypechecks : Set
    exactBilinearProductRemainderTypechecks : Set
    operatorNormPipelineTypechecks : Set
    dyadicSchurFromNormPipelineTypechecks : Set

    quantitativeContractionUniquenessTypechecks : Set
    quantitativeBallConstructionTypechecks : Set
    relativeInverseKernelTypechecks : Set
    sharedIFTReuseTypechecks : Set
    finiteSquareInverseUpgradeTypechecks : Set

    su2DefectPipelineTypechecks : Set
    resolventDefectPipelineTypechecks : Set
    resolvedTwoFamilyDefectsTypechecks : Set
    t3ResolvedFiveChannelReuseTypechecks : Set

    hrBetaFiveLocalChannelsTypechecks : Set
    hrBetaFiveChannelUniformAssemblyTypechecks : Set
    integratedRound2CarrierTypechecks : Set
    analyticReductionLedgerTypechecks : Set

    validationWrapperTypechecks : Set
    producerWrapperTypechecks : Set
    roundHasNoPostulatesOrUnsolvedMetas : Set

open AuthoritativePhysicalClosureRound2Evidence public

physicalClosureRound2LedgerLevel = Ledger.physicalClosureRound2LedgerLevel

physicalClosureRound2TypecheckLevel : ProofLevel
physicalClosureRound2TypecheckLevel = conditional

physicalClosureRound2PostulateFreeLevel : ProofLevel
physicalClosureRound2PostulateFreeLevel = conditional
