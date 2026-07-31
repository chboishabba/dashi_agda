module DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound1Receipt where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound1Ledger as Ledger

record PhysicalClosureRound1Receipt : Set where
  constructor physicalClosureRound1Receipt
  field
    repositoryHead : String

    dyadicProjectionChecked : Bool
    dyadicFibreCardinalityChecked : Bool
    dyadicNormalizationChecked : Bool
    dyadicSupport128By8Checked : Bool
    dyadicCellWeightChecked : Bool
    dyadicSchurEnvelopeChecked : Bool

    cmp109GroupAverageAxiomsChecked : Bool
    cmp109ImplicitAverageDerivativeChecked : Bool
    equation011ContourAdapterChecked : Bool
    printedPhysicalInstanceChecked : Bool
    dyadicGroupAverageInstanceChecked : Bool
    principalLogPathBoundChecked : Bool
    frechetAssemblyChecked : Bool

    twoFamilyChannelReductionChecked : Bool
    t3TwoFamilyReuseChecked : Bool

    treeBackgroundSliceTransitionChecked : Bool
    treeBackgroundSpectralDeterminantChecked : Bool

    localToUniformHRBetaChecked : Bool
    wilsonReflectionPositivitySourceChecked : Bool

    validationWrapperChecked : Bool
    producerWrapperChecked : Bool
    roundPostulateFree : Bool

open PhysicalClosureRound1Receipt public

record AuthoritativePhysicalClosureRound1Evidence
    (receipt : PhysicalClosureRound1Receipt) : Set₁ where
  field
    dyadicProjectionTypechecks : Set
    dyadicFibreCardinalityTypechecks : Set
    dyadicNormalizationTypechecks : Set
    dyadicSupport128By8Typechecks : Set
    dyadicCellWeightTypechecks : Set
    dyadicSchurEnvelopeTypechecks : Set

    cmp109GroupAverageAxiomsTypechecks : Set
    cmp109ImplicitAverageDerivativeTypechecks : Set
    equation011ContourAdapterTypechecks : Set
    printedPhysicalInstanceTypechecks : Set
    dyadicGroupAverageInstanceTypechecks : Set
    principalLogPathBoundTypechecks : Set
    frechetAssemblyTypechecks : Set

    twoFamilyChannelReductionTypechecks : Set
    t3TwoFamilyReuseTypechecks : Set

    treeBackgroundSliceTransitionTypechecks : Set
    treeBackgroundSpectralDeterminantTypechecks : Set

    localToUniformHRBetaTypechecks : Set
    wilsonReflectionPositivitySourceTypechecks : Set

    validationWrapperTypechecks : Set
    producerWrapperTypechecks : Set
    roundHasNoPostulatesOrUnsolvedMetas : Set

open AuthoritativePhysicalClosureRound1Evidence public

physicalClosureRound1LedgerLevel = Ledger.physicalClosureRound1LedgerLevel

physicalClosureRound1TypecheckLevel : ProofLevel
physicalClosureRound1TypecheckLevel = conditional

physicalClosureRound1PostulateFreeLevel : ProofLevel
physicalClosureRound1PostulateFreeLevel = conditional
