module DASHI.Physics.Closure.BcStarObservableContract where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.BcStarShellPredictionLadder as Ladder
import DASHI.Physics.Closure.BcStarLatticeAuthorityReceipt as Lattice

------------------------------------------------------------------------
-- Bc lane empirical authority/contact contract.
--
-- This module wires the existing Bc*+/Bc+ toy shell ladder to external
-- authority obligations.  It fixes the measured Bc+ mass as an external
-- authority field, requires a lattice-QCD authority packet for the
-- Bc*+ - Bc+ splitting, and keeps the toy energy functional
-- non-promotable until a physically meaningful Hamiltonian is supplied.

data BcObservableContractStatus : Set where
  bcLaneExternalAuthorityContactOpenNonPromoting :
    BcObservableContractStatus

data BcMeasuredObservable : Set where
  measuredBcPlusMass :
    BcMeasuredObservable
  latticeBcStarMinusBcPlusSplitting :
    BcMeasuredObservable

data BcMassUnitConvention : Set where
  mevOverCSquared :
    BcMassUnitConvention
  mevNaturalUnits :
    BcMassUnitConvention

data BcExternalAuthoritySource : Set where
  lhcbJhep2020BcPlusMass :
    BcExternalAuthoritySource
  latticeQcdAuthorityRequired :
    BcExternalAuthoritySource

data BcAuthorityField : Set where
  requiredAuthoritySource :
    BcAuthorityField
  requiredParticleAndCharge :
    BcAuthorityField
  requiredObservableDefinition :
    BcAuthorityField
  requiredCentralValue :
    BcAuthorityField
  requiredStatisticalUncertainty :
    BcAuthorityField
  requiredSystematicUncertainty :
    BcAuthorityField
  requiredUnitConvention :
    BcAuthorityField
  requiredStableCitationOrDigest :
    BcAuthorityField
  requiredLatticeActionAndEnsembles :
    BcAuthorityField
  requiredHeavyQuarkTreatment :
    BcAuthorityField
  requiredContinuumChiralVolumeSystematics :
    BcAuthorityField

canonicalBcPlusMassAuthorityFields :
  List BcAuthorityField
canonicalBcPlusMassAuthorityFields =
  requiredAuthoritySource
  ∷ requiredParticleAndCharge
  ∷ requiredObservableDefinition
  ∷ requiredCentralValue
  ∷ requiredStatisticalUncertainty
  ∷ requiredSystematicUncertainty
  ∷ requiredUnitConvention
  ∷ requiredStableCitationOrDigest
  ∷ []

canonicalLatticeSplittingAuthorityFields :
  List BcAuthorityField
canonicalLatticeSplittingAuthorityFields =
  requiredAuthoritySource
  ∷ requiredParticleAndCharge
  ∷ requiredObservableDefinition
  ∷ requiredCentralValue
  ∷ requiredStatisticalUncertainty
  ∷ requiredSystematicUncertainty
  ∷ requiredUnitConvention
  ∷ requiredStableCitationOrDigest
  ∷ requiredLatticeActionAndEnsembles
  ∷ requiredHeavyQuarkTreatment
  ∷ requiredContinuumChiralVolumeSystematics
  ∷ []

data BcFreezeBeforeCompareGate : Set where
  ladderParametersFrozenBeforeAuthorityComparison :
    BcFreezeBeforeCompareGate

data BcEnergyFunctionalBoundary : Set where
  currentEnergyFunctionalToyOnly :
    BcEnergyFunctionalBoundary
  noPhysicalHamiltonianSupplied :
    BcEnergyFunctionalBoundary
  noQcdPotentialOrLatticeSpectrumDerivedHere :
    BcEnergyFunctionalBoundary
  noMassPredictionPromotionFromToyFunctional :
    BcEnergyFunctionalBoundary
  realEnergyFunctionalObligationOpen :
    BcEnergyFunctionalBoundary

canonicalBcEnergyFunctionalBoundaries :
  List BcEnergyFunctionalBoundary
canonicalBcEnergyFunctionalBoundaries =
  currentEnergyFunctionalToyOnly
  ∷ noPhysicalHamiltonianSupplied
  ∷ noQcdPotentialOrLatticeSpectrumDerivedHere
  ∷ noMassPredictionPromotionFromToyFunctional
  ∷ realEnergyFunctionalObligationOpen
  ∷ []

data BcRealEnergyFunctionalObligation : Set where
  constructQcdHilbertSpace :
    BcRealEnergyFunctionalObligation
  defineRenormalizedQcdHamiltonian :
    BcRealEnergyFunctionalObligation
  bindHeavyQuarkEffectiveAction :
    BcRealEnergyFunctionalObligation
  proveSelfAdjointEnergyOperator :
    BcRealEnergyFunctionalObligation
  deriveBcSpectrumExtractionMap :
    BcRealEnergyFunctionalObligation
  bindLatticeContinuumLimitReceipt :
    BcRealEnergyFunctionalObligation
  separateToyEnergyFromPhysicalEnergy :
    BcRealEnergyFunctionalObligation

canonicalBcRealEnergyFunctionalObligations :
  List BcRealEnergyFunctionalObligation
canonicalBcRealEnergyFunctionalObligations =
  constructQcdHilbertSpace
  ∷ defineRenormalizedQcdHamiltonian
  ∷ bindHeavyQuarkEffectiveAction
  ∷ proveSelfAdjointEnergyOperator
  ∷ deriveBcSpectrumExtractionMap
  ∷ bindLatticeContinuumLimitReceipt
  ∷ separateToyEnergyFromPhysicalEnergy
  ∷ []

data BcComparisonPromotionToken : Set where

bcComparisonPromotionImpossibleHere :
  BcComparisonPromotionToken →
  ⊥
bcComparisonPromotionImpossibleHere ()

data BcRealEnergyFunctionalPromotionToken : Set where

bcRealEnergyFunctionalPromotionImpossibleHere :
  BcRealEnergyFunctionalPromotionToken →
  ⊥
bcRealEnergyFunctionalPromotionImpossibleHere ()

record BcRealEnergyFunctionalObligationReceipt : Set where
  constructor mkBcRealEnergyFunctionalObligationReceipt
  field
    toyFunctional :
      Ladder.ToyEnergyParameters →
      Ladder.BcMesonCarrier →
      Ladder.BcShellLabel →
      Nat

    toyFunctionalIsCanonical :
      toyFunctional ≡ Ladder.toyShellEnergy

    toyFunctionalPromotable :
      Bool

    toyFunctionalPromotableIsFalse :
      toyFunctionalPromotable ≡ false

    realEnergyFunctionalSupplied :
      Bool

    realEnergyFunctionalSuppliedIsFalse :
      realEnergyFunctionalSupplied ≡ false

    physicalHamiltonianSupplied :
      Bool

    physicalHamiltonianSuppliedIsFalse :
      physicalHamiltonianSupplied ≡ false

    obligations :
      List BcRealEnergyFunctionalObligation

    obligationsAreCanonical :
      obligations ≡ canonicalBcRealEnergyFunctionalObligations

    promotionTokenBlocked :
      BcRealEnergyFunctionalPromotionToken →
      ⊥

    receiptText :
      List String

open BcRealEnergyFunctionalObligationReceipt public

canonicalBcRealEnergyFunctionalObligationReceipt :
  BcRealEnergyFunctionalObligationReceipt
canonicalBcRealEnergyFunctionalObligationReceipt =
  mkBcRealEnergyFunctionalObligationReceipt
    Ladder.toyShellEnergy
    refl
    false
    refl
    false
    refl
    false
    refl
    canonicalBcRealEnergyFunctionalObligations
    refl
    bcRealEnergyFunctionalPromotionImpossibleHere
    ( "The current Bc energy functional is Ladder.toyShellEnergy only"
      ∷ "A real energy functional must supply the QCD Hilbert space, Hamiltonian, heavy-quark action, self-adjointness, and spectrum-extraction map"
      ∷ "The toy functional is explicitly non-promotable and cannot carry physical mass authority"
      ∷ [] )

record BcMeasuredMassAuthorityField : Set where
  constructor mkBcMeasuredMassAuthorityField
  field
    observable :
      BcMeasuredObservable

    observableIsBcPlusMass :
      observable ≡ measuredBcPlusMass

    authoritySource :
      BcExternalAuthoritySource

    authoritySourceIsLhcb :
      authoritySource ≡ lhcbJhep2020BcPlusMass

    particleLabel :
      String

    valueMeVTimes100 :
      Nat

    valueMeVTimes100IsLhcb2020 :
      valueMeVTimes100 ≡ 627447

    statisticalUncertaintyMeVTimes100 :
      Nat

    statisticalUncertaintyMeVTimes100Is27 :
      statisticalUncertaintyMeVTimes100 ≡ 27

    systematicUncertaintyMeVTimes100 :
      Nat

    systematicUncertaintyMeVTimes100Is17 :
      systematicUncertaintyMeVTimes100 ≡ 17

    unit :
      BcMassUnitConvention

    unitIsMeVOverCSquared :
      unit ≡ mevOverCSquared

    stableCitation :
      String

    authorityFields :
      List BcAuthorityField

    authorityFieldsAreCanonical :
      authorityFields ≡ canonicalBcPlusMassAuthorityFields

open BcMeasuredMassAuthorityField public

canonicalBcPlusMeasuredMassAuthorityField :
  BcMeasuredMassAuthorityField
canonicalBcPlusMeasuredMassAuthorityField =
  mkBcMeasuredMassAuthorityField
    measuredBcPlusMass
    refl
    lhcbJhep2020BcPlusMass
    refl
    "Bc+"
    627447
    refl
    27
    refl
    17
    refl
    mevOverCSquared
    refl
    "LHCb Collaboration, JHEP 07 (2020) 123, doi:10.1007/JHEP07(2020)123"
    canonicalBcPlusMassAuthorityFields
    refl

record BcLatticeSplittingAuthorityObligation : Set where
  constructor mkBcLatticeSplittingAuthorityObligation
  field
    observable :
      BcMeasuredObservable

    observableIsSplitting :
      observable ≡ latticeBcStarMinusBcPlusSplitting

    authoritySource :
      BcExternalAuthoritySource

    authoritySourceIsLatticeRequired :
      authoritySource ≡ latticeQcdAuthorityRequired

    splittingLabel :
      String

    unit :
      BcMassUnitConvention

    unitIsMeVNaturalUnits :
      unit ≡ mevNaturalUnits

    acceptedLatticeAuthorityPresent :
      Bool

    acceptedLatticeAuthorityPresentIsFalse :
      acceptedLatticeAuthorityPresent ≡ false

    requiredFields :
      List BcAuthorityField

    requiredFieldsAreCanonical :
      requiredFields ≡ canonicalLatticeSplittingAuthorityFields

open BcLatticeSplittingAuthorityObligation public

canonicalBcStarBcLatticeSplittingAuthorityObligation :
  BcLatticeSplittingAuthorityObligation
canonicalBcStarBcLatticeSplittingAuthorityObligation =
  mkBcLatticeSplittingAuthorityObligation
    latticeBcStarMinusBcPlusSplitting
    refl
    latticeQcdAuthorityRequired
    refl
    "Bc*+ - Bc+ mass splitting"
    mevNaturalUnits
    refl
    false
    refl
    canonicalLatticeSplittingAuthorityFields
    refl

record BcStarObservableContractReceipt : Setω where
  field
    status :
      BcObservableContractStatus

    ladderReceipt :
      Ladder.BcStarShellPredictionLadderReceipt

    ladderReceiptCanonical :
      Bool

    ladderReceiptCanonicalIsTrue :
      ladderReceiptCanonical ≡ true

    measuredMassAuthority :
      BcMeasuredMassAuthorityField

    measuredMassAuthorityIsCanonical :
      measuredMassAuthority ≡ canonicalBcPlusMeasuredMassAuthorityField

    latticeSplittingAuthorityObligation :
      BcLatticeSplittingAuthorityObligation

    latticeSplittingAuthorityObligationIsCanonical :
      latticeSplittingAuthorityObligation
      ≡
      canonicalBcStarBcLatticeSplittingAuthorityObligation

    latticeAuthorityReceipt :
      Lattice.BcStarLatticeAuthorityReceipt

    latticeAuthorityReceiptIsCanonical :
      latticeAuthorityReceipt
      ≡
      Lattice.canonicalBcStarLatticeAuthorityReceipt

    freezeBeforeCompareGate :
      BcFreezeBeforeCompareGate

    ladderParametersFrozen :
      Bool

    ladderParametersFrozenIsTrue :
      ladderParametersFrozen ≡ true

    empiricalComparisonBeforeFreeze :
      Bool

    empiricalComparisonBeforeFreezeIsFalse :
      empiricalComparisonBeforeFreeze ≡ false

    toyDeltaFromLadder :
      Nat

    toyDeltaFromLadderIs42 :
      toyDeltaFromLadder ≡ 42

    toyFunctionalPromotable :
      Bool

    toyFunctionalPromotableIsFalse :
      toyFunctionalPromotable ≡ false

    physicallyMeaningfulHamiltonianSupplied :
      Bool

    physicallyMeaningfulHamiltonianSuppliedIsFalse :
      physicallyMeaningfulHamiltonianSupplied ≡ false

    realEnergyFunctionalObligationReceipt :
      BcRealEnergyFunctionalObligationReceipt

    realEnergyFunctionalObligationReceiptIsCanonical :
      realEnergyFunctionalObligationReceipt
      ≡
      canonicalBcRealEnergyFunctionalObligationReceipt

    energyFunctionalBoundaries :
      List BcEnergyFunctionalBoundary

    energyFunctionalBoundariesAreCanonical :
      energyFunctionalBoundaries ≡ canonicalBcEnergyFunctionalBoundaries

    comparisonPromotionClaimed :
      Bool

    comparisonPromotionClaimedIsFalse :
      comparisonPromotionClaimed ≡ false

    comparisonPromotionBlocked :
      BcComparisonPromotionToken →
      ⊥

    receiptText :
      List String

open BcStarObservableContractReceipt public

canonicalBcStarObservableContractReceipt :
  BcStarObservableContractReceipt
canonicalBcStarObservableContractReceipt =
  record
    { status =
        bcLaneExternalAuthorityContactOpenNonPromoting
    ; ladderReceipt =
        Ladder.canonicalBcStarShellPredictionLadderReceipt
    ; ladderReceiptCanonical =
        true
    ; ladderReceiptCanonicalIsTrue =
        refl
    ; measuredMassAuthority =
        canonicalBcPlusMeasuredMassAuthorityField
    ; measuredMassAuthorityIsCanonical =
        refl
    ; latticeSplittingAuthorityObligation =
        canonicalBcStarBcLatticeSplittingAuthorityObligation
    ; latticeSplittingAuthorityObligationIsCanonical =
        refl
    ; latticeAuthorityReceipt =
        Lattice.canonicalBcStarLatticeAuthorityReceipt
    ; latticeAuthorityReceiptIsCanonical =
        refl
    ; freezeBeforeCompareGate =
        ladderParametersFrozenBeforeAuthorityComparison
    ; ladderParametersFrozen =
        Ladder.parametersFrozen Ladder.canonicalBcStarShellPredictionLadderReceipt
    ; ladderParametersFrozenIsTrue =
        refl
    ; empiricalComparisonBeforeFreeze =
        false
    ; empiricalComparisonBeforeFreezeIsFalse =
        refl
    ; toyDeltaFromLadder =
        Ladder.canonicalBcStarPredictionDelta
    ; toyDeltaFromLadderIs42 =
        refl
    ; toyFunctionalPromotable =
        false
    ; toyFunctionalPromotableIsFalse =
        refl
    ; physicallyMeaningfulHamiltonianSupplied =
        false
    ; physicallyMeaningfulHamiltonianSuppliedIsFalse =
        refl
    ; realEnergyFunctionalObligationReceipt =
        canonicalBcRealEnergyFunctionalObligationReceipt
    ; realEnergyFunctionalObligationReceiptIsCanonical =
        refl
    ; energyFunctionalBoundaries =
        canonicalBcEnergyFunctionalBoundaries
    ; energyFunctionalBoundariesAreCanonical =
        refl
    ; comparisonPromotionClaimed =
        false
    ; comparisonPromotionClaimedIsFalse =
        refl
    ; comparisonPromotionBlocked =
        bcComparisonPromotionImpossibleHere
    ; receiptText =
        "External authority field fixes the measured Bc+ mass observable to 6274.47 MeV/c^2 with 0.27 stat and 0.17 syst MeV uncertainty from the cited LHCb JHEP 2020 receipt"
        ∷ "The Bc*+ - Bc+ splitting is not accepted here: a lattice-QCD authority packet remains required"
        ∷ "The lattice authority packet surface is concretely exported by BcStarLatticeAuthorityReceipt and remains fail-closed"
        ∷ "Freeze-before-compare gate consumes the existing frozen ladder parameters before any empirical comparison"
        ∷ "The current energy functional is the ladder toy functional only and is non-promotable"
        ∷ "A physically meaningful Hamiltonian or lattice-spectrum derivation must be supplied before any physics promotion"
        ∷ []
    }

bcStarObservableContractExportsFrozenGate :
  ladderParametersFrozen canonicalBcStarObservableContractReceipt ≡ true
bcStarObservableContractExportsFrozenGate =
  refl

bcStarObservableContractKeepsToyDelta :
  toyDeltaFromLadder canonicalBcStarObservableContractReceipt ≡ 42
bcStarObservableContractKeepsToyDelta =
  refl

bcStarObservableContractBlocksPromotion :
  comparisonPromotionClaimed canonicalBcStarObservableContractReceipt ≡ false
bcStarObservableContractBlocksPromotion =
  refl

bcStarObservableContractHasNoPhysicalHamiltonian :
  physicallyMeaningfulHamiltonianSupplied canonicalBcStarObservableContractReceipt
  ≡
  false
bcStarObservableContractHasNoPhysicalHamiltonian =
  refl

bcStarObservableContractHasLatticeAuthorityReceipt :
  latticeAuthorityReceipt canonicalBcStarObservableContractReceipt
  ≡
  Lattice.canonicalBcStarLatticeAuthorityReceipt
bcStarObservableContractHasLatticeAuthorityReceipt =
  refl

bcStarObservableContractRealEnergyFunctionalOpen :
  realEnergyFunctionalSupplied
    (realEnergyFunctionalObligationReceipt canonicalBcStarObservableContractReceipt)
  ≡
  false
bcStarObservableContractRealEnergyFunctionalOpen =
  refl

bcStarObservableContractToyFunctionalNonPromotable :
  BcRealEnergyFunctionalObligationReceipt.toyFunctionalPromotable
    (realEnergyFunctionalObligationReceipt canonicalBcStarObservableContractReceipt)
  ≡
  false
bcStarObservableContractToyFunctionalNonPromotable =
  refl
