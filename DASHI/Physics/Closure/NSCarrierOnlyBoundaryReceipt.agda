module DASHI.Physics.Closure.NSCarrierOnlyBoundaryReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Navier-Stokes carrier-only boundary receipt.
--
-- This receipt records the boundary of the present NS result honestly:
-- the global bound is for carrier-structured initial data whose Fourier
-- support lies on the carrier prime spectrum.  General H^{11/8} data is not
-- shown here to have that structure.  Bridging the carrier result to the Clay
-- Navier-Stokes target still needs a separate structural argument.

data NSCarrierOnlyBoundaryStatus : Set where
  carrierOnlyBoundaryRecorded :
    NSCarrierOnlyBoundaryStatus

data NSCarrierOnlyBoundScope : Set where
  carrierStructuredInitialDataScope :
    NSCarrierOnlyBoundScope

  fourierSupportOnCarrierPrimeSpectrumScope :
    NSCarrierOnlyBoundScope

  globalBoundForCarrierStructuredU0Scope :
    NSCarrierOnlyBoundScope

canonicalNSCarrierOnlyBoundScope :
  List NSCarrierOnlyBoundScope
canonicalNSCarrierOnlyBoundScope =
  carrierStructuredInitialDataScope
  ∷ fourierSupportOnCarrierPrimeSpectrumScope
  ∷ globalBoundForCarrierStructuredU0Scope
  ∷ []

data NSCarrierOnlyExcludedScope : Set where
  arbitraryH118InitialDataNotStructuredHere :
    NSCarrierOnlyExcludedScope

  noProofGeneralH118HasCarrierPrimeSupport :
    NSCarrierOnlyExcludedScope

  noClayGeneralCaseClosedHere :
    NSCarrierOnlyExcludedScope

canonicalNSCarrierOnlyExcludedScope :
  List NSCarrierOnlyExcludedScope
canonicalNSCarrierOnlyExcludedScope =
  arbitraryH118InitialDataNotStructuredHere
  ∷ noProofGeneralH118HasCarrierPrimeSupport
  ∷ noClayGeneralCaseClosedHere
  ∷ []

data NSCarrierToGeneralOpenBridge : Set where
  approximateAllH118DataByCarrierDataPreservingGlobalBound :
    NSCarrierToGeneralOpenBridge

  carrierStructuredSolutionsDenseInRelevantSolutionSpace :
    NSCarrierToGeneralOpenBridge

canonicalNSCarrierToGeneralOpenBridge :
  List NSCarrierToGeneralOpenBridge
canonicalNSCarrierToGeneralOpenBridge =
  approximateAllH118DataByCarrierDataPreservingGlobalBound
  ∷ carrierStructuredSolutionsDenseInRelevantSolutionSpace
  ∷ []

data NSCarrierOnlyPromotion : Set where

nsCarrierOnlyPromotionImpossibleHere :
  NSCarrierOnlyPromotion →
  ⊥
nsCarrierOnlyPromotionImpossibleHere ()

nsCarrierOnlyBoundaryStatement : String
nsCarrierOnlyBoundaryStatement =
  "The NS global bound recorded here is carrier-only: it holds for carrier-structured u0 whose Fourier support lies on the carrier prime spectrum. General H^{11/8} data is not proved to have this structure. The gap to Clay NS remains open until a structural approximation/density argument preserves the global bound or proves carrier-structured solutions dense in the relevant solution space."

record NSCarrierOnlyBoundaryReceipt : Setω where
  field
    status :
      NSCarrierOnlyBoundaryStatus

    boundScope :
      List NSCarrierOnlyBoundScope

    boundScopeIsCanonical :
      boundScope ≡ canonicalNSCarrierOnlyBoundScope

    excludedScope :
      List NSCarrierOnlyExcludedScope

    excludedScopeIsCanonical :
      excludedScope ≡ canonicalNSCarrierOnlyExcludedScope

    openBridge :
      List NSCarrierToGeneralOpenBridge

    openBridgeIsCanonical :
      openBridge ≡ canonicalNSCarrierToGeneralOpenBridge

    h118SobolevNumerator :
      Nat

    h118SobolevNumeratorIs11 :
      h118SobolevNumerator ≡ 11

    h118SobolevDenominator :
      Nat

    h118SobolevDenominatorIs8 :
      h118SobolevDenominator ≡ 8

    globalBoundForCarrierStructuredU0 :
      Bool

    globalBoundForCarrierStructuredU0IsTrue :
      globalBoundForCarrierStructuredU0 ≡ true

    fourierSupportOnCarrierPrimeSpectrum :
      Bool

    fourierSupportOnCarrierPrimeSpectrumIsTrue :
      fourierSupportOnCarrierPrimeSpectrum ≡ true

    generalH118DataHasCarrierStructure :
      Bool

    generalH118DataHasCarrierStructureIsFalse :
      generalH118DataHasCarrierStructure ≡ false

    approximationPreservingGlobalBoundProved :
      Bool

    approximationPreservingGlobalBoundProvedIsFalse :
      approximationPreservingGlobalBoundProved ≡ false

    carrierStructuredSolutionsDenseProved :
      Bool

    carrierStructuredSolutionsDenseProvedIsFalse :
      carrierStructuredSolutionsDenseProved ≡ false

    carrierStructuredOnlyBound :
      Bool

    carrierStructuredOnlyBoundIsTrue :
      carrierStructuredOnlyBound ≡ true

    carrierToGeneralGapOpen :
      Bool

    carrierToGeneralGapOpenIsTrue :
      carrierToGeneralGapOpen ≡ true

    clayNSRequiresGeneralCase :
      Bool

    clayNSRequiresGeneralCaseIsTrue :
      clayNSRequiresGeneralCase ≡ true

    noClayPromotion :
      Bool

    noClayPromotionIsTrue :
      noClayPromotion ≡ true

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    globalTerminalPromotion :
      Bool

    globalTerminalPromotionIsFalse :
      globalTerminalPromotion ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsCarrierOnlyBoundaryStatement

    promotionFlags :
      List NSCarrierOnlyPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSCarrierOnlyBoundaryReceipt public

canonicalNSCarrierOnlyBoundaryReceipt :
  NSCarrierOnlyBoundaryReceipt
canonicalNSCarrierOnlyBoundaryReceipt =
  record
    { status =
        carrierOnlyBoundaryRecorded
    ; boundScope =
        canonicalNSCarrierOnlyBoundScope
    ; boundScopeIsCanonical =
        refl
    ; excludedScope =
        canonicalNSCarrierOnlyExcludedScope
    ; excludedScopeIsCanonical =
        refl
    ; openBridge =
        canonicalNSCarrierToGeneralOpenBridge
    ; openBridgeIsCanonical =
        refl
    ; h118SobolevNumerator =
        11
    ; h118SobolevNumeratorIs11 =
        refl
    ; h118SobolevDenominator =
        8
    ; h118SobolevDenominatorIs8 =
        refl
    ; globalBoundForCarrierStructuredU0 =
        true
    ; globalBoundForCarrierStructuredU0IsTrue =
        refl
    ; fourierSupportOnCarrierPrimeSpectrum =
        true
    ; fourierSupportOnCarrierPrimeSpectrumIsTrue =
        refl
    ; generalH118DataHasCarrierStructure =
        false
    ; generalH118DataHasCarrierStructureIsFalse =
        refl
    ; approximationPreservingGlobalBoundProved =
        false
    ; approximationPreservingGlobalBoundProvedIsFalse =
        refl
    ; carrierStructuredSolutionsDenseProved =
        false
    ; carrierStructuredSolutionsDenseProvedIsFalse =
        refl
    ; carrierStructuredOnlyBound =
        true
    ; carrierStructuredOnlyBoundIsTrue =
        refl
    ; carrierToGeneralGapOpen =
        true
    ; carrierToGeneralGapOpenIsTrue =
        refl
    ; clayNSRequiresGeneralCase =
        true
    ; clayNSRequiresGeneralCaseIsTrue =
        refl
    ; noClayPromotion =
        true
    ; noClayPromotionIsTrue =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; globalTerminalPromotion =
        false
    ; globalTerminalPromotionIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; statement =
        nsCarrierOnlyBoundaryStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Global bound is recorded only for carrier-structured u0"
        ∷ "Carrier structure means Fourier support on the carrier prime spectrum"
        ∷ "General H^{11/8} initial data is not proved here to have carrier structure"
        ∷ "The carrier-to-general gap remains open"
        ∷ "Closing the gap needs approximation preserving the global bound or density of carrier-structured solutions"
        ∷ "No Clay Navier-Stokes, global terminal, or terminal Clay claim is promoted"
        ∷ []
    }

nsCarrierOnlyBoundaryIsCarrierOnly :
  carrierStructuredOnlyBound canonicalNSCarrierOnlyBoundaryReceipt ≡ true
nsCarrierOnlyBoundaryIsCarrierOnly =
  refl

nsCarrierOnlyBoundaryKeepsGapOpen :
  carrierToGeneralGapOpen canonicalNSCarrierOnlyBoundaryReceipt ≡ true
nsCarrierOnlyBoundaryKeepsGapOpen =
  refl

nsCarrierOnlyBoundaryKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSCarrierOnlyBoundaryReceipt ≡ false
nsCarrierOnlyBoundaryKeepsClayFalse =
  refl
