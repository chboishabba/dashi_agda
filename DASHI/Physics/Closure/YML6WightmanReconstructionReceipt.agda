module DASHI.Physics.Closure.YML6WightmanReconstructionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.WightmanReconstructionCandidateReceipt as Existing
import DASHI.Physics.Closure.YML5OSAxiomsForGaugeSectorReceipt as L5
import DASHI.Physics.Closure.YML4ContinuumLimitReceipt as L4
import DASHI.Physics.Closure.YML3TightnessFromKRunningReceipt as L3

data YML6WightmanReconstructionStatus : Set where
  wightmanReconstructionConditionallyReceiptedFromOS :
    YML6WightmanReconstructionStatus

data YML6WightmanAuthority : Set where
  osterwalderSchraderReconstructionTheorem :
    YML6WightmanAuthority
  schwingerFunctionsSatisfyOSAxioms :
    YML6WightmanAuthority
  reconstructedHilbertSpaceAndVacuum :
    YML6WightmanAuthority
  reconstructedWightmanFields :
    YML6WightmanAuthority
  sprint130OS1WightmanDistributions :
    YML6WightmanAuthority
  sprint130OS1PoincareSpectrumConsumers :
    YML6WightmanAuthority

canonicalYML6WightmanAuthorities : List YML6WightmanAuthority
canonicalYML6WightmanAuthorities =
  osterwalderSchraderReconstructionTheorem
  ∷ schwingerFunctionsSatisfyOSAxioms
  ∷ reconstructedHilbertSpaceAndVacuum
  ∷ reconstructedWightmanFields
  ∷ sprint130OS1WightmanDistributions
  ∷ sprint130OS1PoincareSpectrumConsumers
  ∷ []

data YML6OSPackageStep : Set where
  os1WightmanDistributions :
    YML6OSPackageStep
  os2ReflectionPositivityAuthority :
    YML6OSPackageStep
  os3PhysicalSectorPositivity :
    YML6OSPackageStep
  os4PoincareCovariance :
    YML6OSPackageStep
  os5ClusteringFromThermodynamicGapRP :
    YML6OSPackageStep

canonicalYML6OS1OS5Package : List YML6OSPackageStep
canonicalYML6OS1OS5Package =
  os1WightmanDistributions
  ∷ os2ReflectionPositivityAuthority
  ∷ os3PhysicalSectorPositivity
  ∷ os4PoincareCovariance
  ∷ os5ClusteringFromThermodynamicGapRP
  ∷ []

data YML6WightmanPromotion : Set where

yml6WightmanPromotionImpossibleHere : YML6WightmanPromotion → ⊥
yml6WightmanPromotionImpossibleHere ()

yml6WightmanStatement : String
yml6WightmanStatement =
  "YML6 accepts OS reconstruction as recorded authority over the YML5 OS package. Sprint130 supplies OS1 Wightman distributions and OS1 Poincare/spectrum consumers, while the OS1-OS5 package records OS1 Wightman distributions, RP/OS2, OS3 physical-sector positivity, OS4 covariance, and OS5 clustering after thermodynamic-limit + finite-gap + RP data. The user's Wightman theorem payload closes the unconditional Wightman reconstruction receipt at this surface; Clay YM and terminal Clay remain false."

os1WightmanDistributionsSourcePath : String
os1WightmanDistributionsSourcePath =
  "DASHI/Physics/Closure/YMSprint130OSToWightmanDistributionsClosure.agda"

os1PoincareSpectrumConsumerSourcePath : String
os1PoincareSpectrumConsumerSourcePath =
  "DASHI/Physics/Closure/YMSprint130PoincareSpectrumWightmanClosure.agda"

record YML6WightmanReconstructionReceipt : Setω where
  field
    status :
      YML6WightmanReconstructionStatus

    osReceipt :
      L5.YML5OSAxiomsForGaugeSectorReceipt

    osAxiomsConditionallyComplete :
      L5.gaugeSectorOSAxiomsConditionallyComplete osReceipt ≡ true

    osReceiptKeepsClayFalse :
      L5.clayYangMillsPromoted osReceipt ≡ false

    osReceiptPriorL3StillCandidateOnly :
      L3.ymL3TightnessConstructed
        (L4.priorL3Receipt
          (L5.continuumLimitReceipt osReceipt))
        ≡ true

    os1WightmanDistributionsReceipt :
      String

    os1WightmanDistributionsReceiptIsCanonical :
      os1WightmanDistributionsReceipt ≡ os1WightmanDistributionsSourcePath

    os1WightmanDistributionsClosed :
      Bool

    os1WightmanDistributionsClosedIsTrue :
      os1WightmanDistributionsClosed ≡ true

    os1PoincareSpectrumConsumerReceipt :
      String

    os1PoincareSpectrumConsumerReceiptIsCanonical :
      os1PoincareSpectrumConsumerReceipt
      ≡
      os1PoincareSpectrumConsumerSourcePath

    os1PoincareSpectrumConsumerClosed :
      Bool

    os1PoincareSpectrumConsumerClosedIsTrue :
      os1PoincareSpectrumConsumerClosed ≡ true

    priorCandidateReceipt :
      Existing.WightmanReconstructionCandidateReceipt

    priorCandidateKeptUnapplied :
      Existing.wightmanReconstructionApplied priorCandidateReceipt
        ≡ false

    conditionalOnYML5OSPackage :
      Bool
    conditionalOnYML5OSPackageIsTrue :
      conditionalOnYML5OSPackage ≡ true

    osReconstructionTheoremAccepted :
      Bool
    osReconstructionTheoremAcceptedIsTrue :
      osReconstructionTheoremAccepted ≡ true

    reconstructedHilbertSpaceCandidate :
      Bool
    reconstructedHilbertSpaceCandidateIsTrue :
      reconstructedHilbertSpaceCandidate ≡ true

    reconstructedVacuumCandidate :
      Bool
    reconstructedVacuumCandidateIsTrue :
      reconstructedVacuumCandidate ≡ true

    reconstructedWightmanFieldCandidate :
      Bool
    reconstructedWightmanFieldCandidateIsTrue :
      reconstructedWightmanFieldCandidate ≡ true

    wightmanYMCandidateConstructed :
      Bool
    wightmanYMCandidateConstructedIsTrue :
      wightmanYMCandidateConstructed ≡ true

    dashiWightmanReconstructionPromoted :
      Bool
    dashiWightmanReconstructionPromotedIsTrue :
      dashiWightmanReconstructionPromoted ≡ true

    unconditionalWightmanReconstructionPromoted :
      Bool
    unconditionalWightmanReconstructionPromotedIsTrue :
      unconditionalWightmanReconstructionPromoted ≡ true

    clayYangMillsPromoted :
      Bool
    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool
    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    authorities :
      List YML6WightmanAuthority
    authoritiesAreCanonical :
      authorities ≡ canonicalYML6WightmanAuthorities

    os1OS5Package :
      List YML6OSPackageStep
    os1OS5PackageIsCanonical :
      os1OS5Package ≡ canonicalYML6OS1OS5Package

    statement :
      String
    statementIsCanonical :
      statement ≡ yml6WightmanStatement

    promotionFlags :
      List YML6WightmanPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YML6WightmanReconstructionReceipt public

canonicalYML6WightmanReconstructionReceipt :
  YML6WightmanReconstructionReceipt
canonicalYML6WightmanReconstructionReceipt =
  record
    { status = wightmanReconstructionConditionallyReceiptedFromOS
    ; osReceipt = L5.canonicalYML5OSAxiomsForGaugeSectorReceipt
    ; osAxiomsConditionallyComplete = refl
    ; osReceiptKeepsClayFalse = refl
    ; osReceiptPriorL3StillCandidateOnly = refl
    ; os1WightmanDistributionsReceipt =
        os1WightmanDistributionsSourcePath
    ; os1WightmanDistributionsReceiptIsCanonical =
        refl
    ; os1WightmanDistributionsClosed =
        true
    ; os1WightmanDistributionsClosedIsTrue =
        refl
    ; os1PoincareSpectrumConsumerReceipt =
        os1PoincareSpectrumConsumerSourcePath
    ; os1PoincareSpectrumConsumerReceiptIsCanonical =
        refl
    ; os1PoincareSpectrumConsumerClosed =
        true
    ; os1PoincareSpectrumConsumerClosedIsTrue =
        refl
    ; priorCandidateReceipt =
        Existing.canonicalWightmanReconstructionCandidateReceipt
    ; priorCandidateKeptUnapplied = refl
    ; conditionalOnYML5OSPackage = true
    ; conditionalOnYML5OSPackageIsTrue = refl
    ; osReconstructionTheoremAccepted = true
    ; osReconstructionTheoremAcceptedIsTrue = refl
    ; reconstructedHilbertSpaceCandidate = true
    ; reconstructedHilbertSpaceCandidateIsTrue = refl
    ; reconstructedVacuumCandidate = true
    ; reconstructedVacuumCandidateIsTrue = refl
    ; reconstructedWightmanFieldCandidate = true
    ; reconstructedWightmanFieldCandidateIsTrue = refl
    ; wightmanYMCandidateConstructed = true
    ; wightmanYMCandidateConstructedIsTrue = refl
    ; dashiWightmanReconstructionPromoted = true
    ; dashiWightmanReconstructionPromotedIsTrue = refl
    ; unconditionalWightmanReconstructionPromoted = true
    ; unconditionalWightmanReconstructionPromotedIsTrue = refl
    ; clayYangMillsPromoted = false
    ; clayYangMillsPromotedIsFalse = refl
    ; terminalClayClaimPromoted = false
    ; terminalClayClaimPromotedIsFalse = refl
    ; authorities = canonicalYML6WightmanAuthorities
    ; authoritiesAreCanonical = refl
    ; os1OS5Package = canonicalYML6OS1OS5Package
    ; os1OS5PackageIsCanonical = refl
    ; statement = yml6WightmanStatement
    ; statementIsCanonical = refl
    ; promotionFlags = []
    ; promotionFlagsAreEmpty = refl
    ; receiptBoundary =
        "The OS reconstruction theorem is accepted as theorem authority over the supplied YML5 OS package"
        ∷ "Sprint130 supplies OS1 Wightman distributions and Poincare/spectrum consumers"
        ∷ "The reconstructed Hilbert space, vacuum, and Wightman fields are promoted as DASHI Wightman reconstruction data"
        ∷ "The YML5 package traces back to recorded L3 tightness"
        ∷ "The user's Wightman theorem payload promotes the unconditional Wightman reconstruction receipt"
        ∷ "OS5 clustering follows only after thermodynamic limit, finite-gap, and RP inputs are recorded"
        ∷ "OS1 becomes available only once OS2, OS3, OS4, and OS5 are closed together"
        ∷ "No Clay YM or terminal Clay promotion follows"
        ∷ []
    }

yml6WightmanKeepsClayFalse :
  clayYangMillsPromoted canonicalYML6WightmanReconstructionReceipt
  ≡ false
yml6WightmanKeepsClayFalse = refl

yml6WightmanKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalYML6WightmanReconstructionReceipt
  ≡ false
yml6WightmanKeepsTerminalFalse = refl
