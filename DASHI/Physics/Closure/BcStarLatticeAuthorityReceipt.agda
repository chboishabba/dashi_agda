module DASHI.Physics.Closure.BcStarLatticeAuthorityReceipt where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Bc*+ - Bc+ lattice-QCD authority receipt surface.
--
-- This module records the concrete authority packet required before the
-- Bc*+ - Bc+ splitting can be compared against the local toy ladder.  It is
-- intentionally non-promoting: no accepted lattice value, no accepted
-- authority token, and no physical Hamiltonian promotion is constructed here.

data BcStarLatticeAuthorityReceiptStatus : Set where
  latticeQcdAuthorityPacketRequiredNonPromoting :
    BcStarLatticeAuthorityReceiptStatus

data BcStarLatticeObservable : Set where
  bcStarPlusMinusBcPlusHyperfineSplitting :
    BcStarLatticeObservable

data BcStarLatticeAuthoritySourceClass : Set where
  peerReviewedLatticeQcdPaper :
    BcStarLatticeAuthoritySourceClass
  collaborationDataRelease :
    BcStarLatticeAuthoritySourceClass
  reproducibleEnsembleArchive :
    BcStarLatticeAuthoritySourceClass

data BcStarLatticeRequiredAuthorityField : Set where
  requiredSourceClass :
    BcStarLatticeRequiredAuthorityField
  requiredStableCitation :
    BcStarLatticeRequiredAuthorityField
  requiredObservableDefinition :
    BcStarLatticeRequiredAuthorityField
  requiredCentralValueMeV :
    BcStarLatticeRequiredAuthorityField
  requiredStatisticalUncertaintyMeV :
    BcStarLatticeRequiredAuthorityField
  requiredSystematicUncertaintyMeV :
    BcStarLatticeRequiredAuthorityField
  requiredLatticeAction :
    BcStarLatticeRequiredAuthorityField
  requiredSeaQuarkContent :
    BcStarLatticeRequiredAuthorityField
  requiredLatticeSpacings :
    BcStarLatticeRequiredAuthorityField
  requiredVolumes :
    BcStarLatticeRequiredAuthorityField
  requiredCharmTreatment :
    BcStarLatticeRequiredAuthorityField
  requiredBottomTreatment :
    BcStarLatticeRequiredAuthorityField
  requiredScaleSetting :
    BcStarLatticeRequiredAuthorityField
  requiredContinuumExtrapolation :
    BcStarLatticeRequiredAuthorityField
  requiredChiralExtrapolation :
    BcStarLatticeRequiredAuthorityField
  requiredFiniteVolumeBudget :
    BcStarLatticeRequiredAuthorityField
  requiredElectromagneticIsospinConvention :
    BcStarLatticeRequiredAuthorityField
  requiredCorrelatorFitWindow :
    BcStarLatticeRequiredAuthorityField
  requiredEnsembleDigest :
    BcStarLatticeRequiredAuthorityField
  requiredReproducibilityAttestation :
    BcStarLatticeRequiredAuthorityField

canonicalBcStarLatticeRequiredAuthorityFields :
  List BcStarLatticeRequiredAuthorityField
canonicalBcStarLatticeRequiredAuthorityFields =
  requiredSourceClass
  ∷ requiredStableCitation
  ∷ requiredObservableDefinition
  ∷ requiredCentralValueMeV
  ∷ requiredStatisticalUncertaintyMeV
  ∷ requiredSystematicUncertaintyMeV
  ∷ requiredLatticeAction
  ∷ requiredSeaQuarkContent
  ∷ requiredLatticeSpacings
  ∷ requiredVolumes
  ∷ requiredCharmTreatment
  ∷ requiredBottomTreatment
  ∷ requiredScaleSetting
  ∷ requiredContinuumExtrapolation
  ∷ requiredChiralExtrapolation
  ∷ requiredFiniteVolumeBudget
  ∷ requiredElectromagneticIsospinConvention
  ∷ requiredCorrelatorFitWindow
  ∷ requiredEnsembleDigest
  ∷ requiredReproducibilityAttestation
  ∷ []

data BcStarLatticePacketBoundary : Set where
  noAcceptedLatticeSplittingValue :
    BcStarLatticePacketBoundary
  noAuthorityTokenMinted :
    BcStarLatticePacketBoundary
  noToyFunctionalPromotion :
    BcStarLatticePacketBoundary
  noComparisonUntilFreezeAndReceipt :
    BcStarLatticePacketBoundary

canonicalBcStarLatticePacketBoundaries :
  List BcStarLatticePacketBoundary
canonicalBcStarLatticePacketBoundaries =
  noAcceptedLatticeSplittingValue
  ∷ noAuthorityTokenMinted
  ∷ noToyFunctionalPromotion
  ∷ noComparisonUntilFreezeAndReceipt
  ∷ []

data BcStarAcceptedLatticeSplittingAuthorityToken : Set where

bcStarAcceptedLatticeSplittingAuthorityTokenImpossibleHere :
  BcStarAcceptedLatticeSplittingAuthorityToken →
  ⊥
bcStarAcceptedLatticeSplittingAuthorityTokenImpossibleHere ()

record BcStarLatticeAuthorityReceipt : Set where
  field
    status :
      BcStarLatticeAuthorityReceiptStatus

    observable :
      BcStarLatticeObservable

    observableIsHyperfineSplitting :
      observable ≡ bcStarPlusMinusBcPlusHyperfineSplitting

    sourceClasses :
      List BcStarLatticeAuthoritySourceClass

    sourceClassesAreCanonical :
      sourceClasses
      ≡
      ( peerReviewedLatticeQcdPaper
        ∷ collaborationDataRelease
        ∷ reproducibleEnsembleArchive
        ∷ [] )

    requiredAuthorityFields :
      List BcStarLatticeRequiredAuthorityField

    requiredAuthorityFieldsAreCanonical :
      requiredAuthorityFields
      ≡
      canonicalBcStarLatticeRequiredAuthorityFields

    acceptedAuthorityPresent :
      Bool

    acceptedAuthorityPresentIsFalse :
      acceptedAuthorityPresent ≡ false

    acceptedSplittingMeVTimes100 :
      Nat

    acceptedSplittingMeVTimes100IsZeroPlaceholder :
      acceptedSplittingMeVTimes100 ≡ 0

    packetBoundaries :
      List BcStarLatticePacketBoundary

    packetBoundariesAreCanonical :
      packetBoundaries
      ≡
      canonicalBcStarLatticePacketBoundaries

    acceptedTokenBlocked :
      BcStarAcceptedLatticeSplittingAuthorityToken →
      ⊥

    receiptText :
      List String

open BcStarLatticeAuthorityReceipt public

canonicalBcStarLatticeAuthorityReceipt :
  BcStarLatticeAuthorityReceipt
canonicalBcStarLatticeAuthorityReceipt =
  record
    { status =
        latticeQcdAuthorityPacketRequiredNonPromoting
    ; observable =
        bcStarPlusMinusBcPlusHyperfineSplitting
    ; observableIsHyperfineSplitting =
        refl
    ; sourceClasses =
        peerReviewedLatticeQcdPaper
        ∷ collaborationDataRelease
        ∷ reproducibleEnsembleArchive
        ∷ []
    ; sourceClassesAreCanonical =
        refl
    ; requiredAuthorityFields =
        canonicalBcStarLatticeRequiredAuthorityFields
    ; requiredAuthorityFieldsAreCanonical =
        refl
    ; acceptedAuthorityPresent =
        false
    ; acceptedAuthorityPresentIsFalse =
        refl
    ; acceptedSplittingMeVTimes100 =
        0
    ; acceptedSplittingMeVTimes100IsZeroPlaceholder =
        refl
    ; packetBoundaries =
        canonicalBcStarLatticePacketBoundaries
    ; packetBoundariesAreCanonical =
        refl
    ; acceptedTokenBlocked =
        bcStarAcceptedLatticeSplittingAuthorityTokenImpossibleHere
    ; receiptText =
        "Bc*+ - Bc+ comparison requires a peer-reviewed lattice-QCD authority packet or equivalent accepted collaboration release"
        ∷ "Required packet includes action, ensembles, heavy-quark treatments, continuum/chiral/volume budgets, scale setting, and uncertainty decomposition"
        ∷ "acceptedSplittingMeVTimes100 is a zero placeholder because no accepted authority value is constructed in this module"
        ∷ "The receipt is non-promoting and cannot turn the toy ladder energy into a physical mass prediction"
        ∷ []
    }

bcStarLatticeAuthorityReceiptBlocksToken :
  acceptedAuthorityPresent canonicalBcStarLatticeAuthorityReceipt ≡ false
bcStarLatticeAuthorityReceiptBlocksToken =
  refl

bcStarLatticeAuthorityReceiptHasCanonicalFields :
  requiredAuthorityFields canonicalBcStarLatticeAuthorityReceipt
  ≡
  canonicalBcStarLatticeRequiredAuthorityFields
bcStarLatticeAuthorityReceiptHasCanonicalFields =
  refl
