module DASHI.Physics.Closure.NSCarrierVsClayGapReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Carrier regularity versus Clay Navier-Stokes gap receipt.
--
-- This receipt records the exact boundary between a carrier-structured
-- Fourier-support regularity candidate and the Clay Navier-Stokes target.  It
-- deliberately does not close the density/approximation lane assigned to A6.

data NSCarrierVsClayGapStatus : Set where
  carrierStructuredRegularityRecordedClayGapOpen :
    NSCarrierVsClayGapStatus

data NSCarrierRegularityScope : Set where
  carrierStructuredFourierSupport :
    NSCarrierRegularityScope

  restrictedInitialDataClass :
    NSCarrierRegularityScope

  carrierAdaptedEstimateFamily :
    NSCarrierRegularityScope

canonicalNSCarrierRegularityScope :
  List NSCarrierRegularityScope
canonicalNSCarrierRegularityScope =
  carrierStructuredFourierSupport
  ∷ restrictedInitialDataClass
  ∷ carrierAdaptedEstimateFamily
  ∷ []

data ClayNSRequirement : Set where
  allSmoothInitialData :
    ClayNSRequirement

  globalSmoothSolution :
    ClayNSRequirement

  noCarrierSupportRestriction :
    ClayNSRequirement

canonicalClayNSRequirements : List ClayNSRequirement
canonicalClayNSRequirements =
  allSmoothInitialData
  ∷ globalSmoothSolution
  ∷ noCarrierSupportRestriction
  ∷ []

data NSCarrierToClayGapItem : Set where
  densityAndApproximationOfCarrierData :
    NSCarrierToClayGapItem

  uniformityOfEstimatesUnderApproximation :
    NSCarrierToClayGapItem

canonicalNSCarrierToClayGapItems : List NSCarrierToClayGapItem
canonicalNSCarrierToClayGapItems =
  densityAndApproximationOfCarrierData
  ∷ uniformityOfEstimatesUnderApproximation
  ∷ []

data NSCarrierRegularityToClayOpenProblem : Set where
  densityApproximationUniformityOpen :
    NSCarrierRegularityToClayOpenProblem

data NSCarrierVsClayPromotion : Set where

nsCarrierVsClayPromotionImpossibleHere :
  NSCarrierVsClayPromotion →
  ⊥
nsCarrierVsClayPromotionImpossibleHere ()

nsCarrierVsClayGapStatement : String
nsCarrierVsClayGapStatement =
  "Carrier-structured Fourier-support regularity applies to a restricted class; Clay Navier-Stokes requires all smooth initial data. The open bridge is density/approximation plus uniformity of estimates."

record NSCarrierVsClayGapReceipt : Setω where
  field
    status :
      NSCarrierVsClayGapStatus

    carrierRegularityScope :
      List NSCarrierRegularityScope

    carrierRegularityScopeIsCanonical :
      carrierRegularityScope ≡ canonicalNSCarrierRegularityScope

    clayRequirements :
      List ClayNSRequirement

    clayRequirementsAreCanonical :
      clayRequirements ≡ canonicalClayNSRequirements

    initiallyIdentifiedGap :
      List NSCarrierToClayGapItem

    initiallyIdentifiedGapIsCanonical :
      initiallyIdentifiedGap ≡ canonicalNSCarrierToClayGapItems

    carrierStructuredFourierSupportResultRecorded :
      Bool

    carrierStructuredFourierSupportResultRecordedIsTrue :
      carrierStructuredFourierSupportResultRecorded ≡ true

    appliesOnlyToRestrictedClass :
      Bool

    appliesOnlyToRestrictedClassIsTrue :
      appliesOnlyToRestrictedClass ≡ true

    clayRequiresAllSmoothInitialData :
      Bool

    clayRequiresAllSmoothInitialDataIsTrue :
      clayRequiresAllSmoothInitialData ≡ true

    densityOfCarrierDataOpen :
      Bool

    densityOfCarrierDataOpenIsTrue :
      densityOfCarrierDataOpen ≡ true

    uniformityOfEstimatesOpen :
      Bool

    uniformityOfEstimatesOpenIsTrue :
      uniformityOfEstimatesOpen ≡ true

    nsCarrierRegularityToClayGap :
      NSCarrierRegularityToClayOpenProblem

    nsCarrierRegularityToClayGapIsCanonical :
      nsCarrierRegularityToClayGap ≡ densityApproximationUniformityOpen

    densityLaneAssignedElsewhere :
      Bool

    densityLaneAssignedElsewhereIsTrue :
      densityLaneAssignedElsewhere ≡ true

    densityClosedHere :
      Bool

    densityClosedHereIsFalse :
      densityClosedHere ≡ false

    carrierRegularityDoesNotImplyClayNS :
      Bool

    carrierRegularityDoesNotImplyClayNSIsTrue :
      carrierRegularityDoesNotImplyClayNS ≡ true

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsCarrierVsClayGapStatement

    promotionFlags :
      List NSCarrierVsClayPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSCarrierVsClayGapReceipt public

canonicalNSCarrierVsClayGapReceipt :
  NSCarrierVsClayGapReceipt
canonicalNSCarrierVsClayGapReceipt =
  record
    { status =
        carrierStructuredRegularityRecordedClayGapOpen
    ; carrierRegularityScope =
        canonicalNSCarrierRegularityScope
    ; carrierRegularityScopeIsCanonical =
        refl
    ; clayRequirements =
        canonicalClayNSRequirements
    ; clayRequirementsAreCanonical =
        refl
    ; initiallyIdentifiedGap =
        canonicalNSCarrierToClayGapItems
    ; initiallyIdentifiedGapIsCanonical =
        refl
    ; carrierStructuredFourierSupportResultRecorded =
        true
    ; carrierStructuredFourierSupportResultRecordedIsTrue =
        refl
    ; appliesOnlyToRestrictedClass =
        true
    ; appliesOnlyToRestrictedClassIsTrue =
        refl
    ; clayRequiresAllSmoothInitialData =
        true
    ; clayRequiresAllSmoothInitialDataIsTrue =
        refl
    ; densityOfCarrierDataOpen =
        true
    ; densityOfCarrierDataOpenIsTrue =
        refl
    ; uniformityOfEstimatesOpen =
        true
    ; uniformityOfEstimatesOpenIsTrue =
        refl
    ; nsCarrierRegularityToClayGap =
        densityApproximationUniformityOpen
    ; nsCarrierRegularityToClayGapIsCanonical =
        refl
    ; densityLaneAssignedElsewhere =
        true
    ; densityLaneAssignedElsewhereIsTrue =
        refl
    ; densityClosedHere =
        false
    ; densityClosedHereIsFalse =
        refl
    ; carrierRegularityDoesNotImplyClayNS =
        true
    ; carrierRegularityDoesNotImplyClayNSIsTrue =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; statement =
        nsCarrierVsClayGapStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Carrier-structured Fourier support gives only a restricted-class regularity candidate"
        ∷ "Clay Navier-Stokes requires global smooth regularity for all smooth initial data"
        ∷ "The identified bridge problem is density/approximation plus uniformity of estimates"
        ∷ "A6 owns density; this receipt keeps densityOfCarrierDataOpen true and promotes no Clay claim"
        ∷ []
    }

nsCarrierVsClayGapKeepsDensityOpen :
  densityOfCarrierDataOpen canonicalNSCarrierVsClayGapReceipt ≡ true
nsCarrierVsClayGapKeepsDensityOpen =
  refl

nsCarrierRegularityDoesNotImplyClay :
  carrierRegularityDoesNotImplyClayNS canonicalNSCarrierVsClayGapReceipt
  ≡
  true
nsCarrierRegularityDoesNotImplyClay =
  refl

nsCarrierVsClayGapKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSCarrierVsClayGapReceipt ≡ false
nsCarrierVsClayGapKeepsClayFalse =
  refl
