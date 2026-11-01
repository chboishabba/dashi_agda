module DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound4Receipt where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound4Ledger as Ledger

record PhysicalClosureRound4Receipt : Set where
  constructor physicalClosureRound4Receipt
  field
    repositoryHead : String

    cmp109PhysicalScaleGeometryChecked : Bool
    cmp109SiteWeightIdentificationChecked : Bool
    cmp109ContourMultiplicityChecked : Bool

    pauliNormConventionChecked : Bool
    halfRadiusScalarLedgerChecked : Bool
    dyadicNewtonBudgetChecked : Bool

    channelOwnershipCorrectionChecked : Bool
    physicalHessianSplitChecked : Bool
    factorizedSelfAdjointnessChecked : Bool
    oneSixteenthBudgetChecked : Bool

    gaugeTaylorLocalizationChecked : Bool
    gaugeLargeFieldAdapterChecked : Bool
    gaugeRandomWalkAdapterChecked : Bool
    gaugeClusterInfluenceChecked : Bool
    gaugeRootedDecayChecked : Bool
    gaugeFiveActivityAllocationChecked : Bool

    integratedRound4CarrierChecked : Bool
    validationWrapperChecked : Bool
    producerWrapperChecked : Bool
    roundPostulateFree : Bool

open PhysicalClosureRound4Receipt public

record AuthoritativePhysicalClosureRound4Evidence
    (receipt : PhysicalClosureRound4Receipt) : Set₁ where
  field
    cmp109PhysicalScaleGeometryTypechecks : Set
    cmp109SiteWeightIdentificationTypechecks : Set
    cmp109ContourMultiplicityTypechecks : Set

    pauliNormConventionTypechecks : Set
    halfRadiusScalarLedgerTypechecks : Set
    dyadicNewtonBudgetTypechecks : Set

    channelOwnershipCorrectionTypechecks : Set
    physicalHessianSplitTypechecks : Set
    factorizedSelfAdjointnessTypechecks : Set
    oneSixteenthBudgetTypechecks : Set

    gaugeTaylorLocalizationTypechecks : Set
    gaugeLargeFieldAdapterTypechecks : Set
    gaugeRandomWalkAdapterTypechecks : Set
    gaugeClusterInfluenceTypechecks : Set
    gaugeRootedDecayTypechecks : Set
    gaugeFiveActivityAllocationTypechecks : Set

    integratedRound4CarrierTypechecks : Set
    validationWrapperTypechecks : Set
    producerWrapperTypechecks : Set
    roundHasNoPostulatesOrUnsolvedMetas : Set

open AuthoritativePhysicalClosureRound4Evidence public

physicalClosureRound4LedgerLevel = Ledger.physicalClosureRound4LedgerLevel

physicalClosureRound4TypecheckLevel : ProofLevel
physicalClosureRound4TypecheckLevel = conditional

physicalClosureRound4PostulateFreeLevel : ProofLevel
physicalClosureRound4PostulateFreeLevel = conditional
