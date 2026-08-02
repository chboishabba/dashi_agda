module DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound6Receipt where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound6Ledger as Ledger

record PhysicalClosureRound6Receipt : Set where
  constructor physicalClosureRound6Receipt
  field
    repositoryHead : String

    nestedThresholdCompatibilityChecked : Bool
    contourSwapDiameterChecked : Bool
    cmp109SwapSmallDiameterAdapterChecked : Bool
    BishopHalfRadiusConstantsChecked : Bool
    FederbushAsymmetricBudgetChecked : Bool
    backgroundGaugeMixedNormChecked : Bool

    plaquetteDerivativeCombinatoricsChecked : Bool
    localWilsonThirdDerivativeChecked : Bool
    constraintNormalInversePerturbationChecked : Bool
    fiveChannelSmallFieldRadiusChecked : Bool
    su2HaarJacobianDefectChecked : Bool

    integratedGaussianFluctuationChecked : Bool
    rOperationPrimarySourceAuditChecked : Bool
    pointwiseSmallFactorEntropyChecked : Bool
    oscillationAnimalInfluenceChecked : Bool
    threeWayRemainderChecked : Bool
    weakeningDependencyGraphChecked : Bool
    WilsonAnimalEntropyLedgerChecked : Bool
    fiveActivityEngineOwnershipChecked : Bool

    exactRound6CutsetChecked : Bool
    round6LedgerChecked : Bool
    validationWrapperChecked : Bool
    producerWrapperChecked : Bool
    round6PostulateFree : Bool

open PhysicalClosureRound6Receipt public

record AuthoritativePhysicalClosureRound6Evidence
    (receipt : PhysicalClosureRound6Receipt) : Set₁ where
  field
    nestedThresholdCompatibilityTypechecks : Set
    contourSwapDiameterTypechecks : Set
    cmp109SwapSmallDiameterAdapterTypechecks : Set
    BishopHalfRadiusConstantsTypechecks : Set
    FederbushAsymmetricBudgetTypechecks : Set
    backgroundGaugeMixedNormTypechecks : Set

    plaquetteDerivativeCombinatoricsTypechecks : Set
    localWilsonThirdDerivativeTypechecks : Set
    constraintNormalInversePerturbationTypechecks : Set
    fiveChannelSmallFieldRadiusTypechecks : Set
    su2HaarJacobianDefectTypechecks : Set

    integratedGaussianFluctuationTypechecks : Set
    rOperationPrimarySourceAuditTypechecks : Set
    pointwiseSmallFactorEntropyTypechecks : Set
    oscillationAnimalInfluenceTypechecks : Set
    threeWayRemainderTypechecks : Set
    weakeningDependencyGraphTypechecks : Set
    WilsonAnimalEntropyLedgerTypechecks : Set
    fiveActivityEngineOwnershipTypechecks : Set

    exactRound6CutsetTypechecks : Set
    round6LedgerTypechecks : Set
    validationWrapperTypechecks : Set
    producerWrapperTypechecks : Set
    round6HasNoPostulatesOrUnsolvedMetas : Set

open AuthoritativePhysicalClosureRound6Evidence public

physicalClosureRound6LedgerLevel = Ledger.physicalClosureRound6LedgerLevel

physicalClosureRound6TypecheckLevel : ProofLevel
physicalClosureRound6TypecheckLevel = conditional

physicalClosureRound6PostulateFreeLevel : ProofLevel
physicalClosureRound6PostulateFreeLevel = conditional
