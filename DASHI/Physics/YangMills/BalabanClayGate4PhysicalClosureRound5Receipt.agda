module DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound5Receipt where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound5Ledger as Ledger

record PhysicalClosureRound5Receipt : Set where
  constructor physicalClosureRound5Receipt
  field
    repositoryHead : String

    cmp109RadiusOneCalibrationChecked : Bool
    cmp109MinimalL13RepositoryScaleChecked : Bool
    cmp109MinimalWeightChecked : Bool

    alternatingTaylorEnvelopeChecked : Bool
    BishopSeriesFunctionIdentificationChecked : Bool
    signedTailSU2EnvelopeChecked : Bool
    seriesLipschitzAssemblyChecked : Bool
    FederbushFourChannelQuarterChecked : Bool

    BalabanGaugeProposition5Checked : Bool
    gaugeHalfContractionBallChecked : Bool

    WilsonQuadraticSecondDifferenceChecked : Bool
    functionalSecondVariationChecked : Bool
    sandwichFormBoundChecked : Bool
    fiveSandwichChannelAssemblyChecked : Bool

    WilsonBadCubePenaltyChecked : Bool
    gaugeCubicTaylorSumChecked : Bool
    weakeningProductSupportChecked : Bool
    connectedTreeDecayChecked : Bool
    dyadicRandomWalkTailChecked : Bool
    dyadicRootedSumChecked : Bool
    fiveActivityTenthAllocationChecked : Bool

    integratedRound5CarrierChecked : Bool
    validationWrapperChecked : Bool
    producerWrapperChecked : Bool
    roundPostulateFree : Bool

open PhysicalClosureRound5Receipt public

record AuthoritativePhysicalClosureRound5Evidence
    (receipt : PhysicalClosureRound5Receipt) : Set₁ where
  field
    cmp109RadiusOneCalibrationTypechecks : Set
    cmp109MinimalL13RepositoryScaleTypechecks : Set
    cmp109MinimalWeightTypechecks : Set

    alternatingTaylorEnvelopeTypechecks : Set
    BishopSeriesFunctionIdentificationTypechecks : Set
    signedTailSU2EnvelopeTypechecks : Set
    seriesLipschitzAssemblyTypechecks : Set
    FederbushFourChannelQuarterTypechecks : Set

    BalabanGaugeProposition5Typechecks : Set
    gaugeHalfContractionBallTypechecks : Set

    WilsonQuadraticSecondDifferenceTypechecks : Set
    functionalSecondVariationTypechecks : Set
    sandwichFormBoundTypechecks : Set
    fiveSandwichChannelAssemblyTypechecks : Set

    WilsonBadCubePenaltyTypechecks : Set
    gaugeCubicTaylorSumTypechecks : Set
    weakeningProductSupportTypechecks : Set
    connectedTreeDecayTypechecks : Set
    dyadicRandomWalkTailTypechecks : Set
    dyadicRootedSumTypechecks : Set
    fiveActivityTenthAllocationTypechecks : Set

    integratedRound5CarrierTypechecks : Set
    validationWrapperTypechecks : Set
    producerWrapperTypechecks : Set
    roundHasNoPostulatesOrUnsolvedMetas : Set

open AuthoritativePhysicalClosureRound5Evidence public

physicalClosureRound5LedgerLevel = Ledger.physicalClosureRound5LedgerLevel

physicalClosureRound5TypecheckLevel : ProofLevel
physicalClosureRound5TypecheckLevel = conditional

physicalClosureRound5PostulateFreeLevel : ProofLevel
physicalClosureRound5PostulateFreeLevel = conditional
