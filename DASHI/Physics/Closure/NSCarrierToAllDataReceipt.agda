module DASHI.Physics.Closure.NSCarrierToAllDataReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSCarrierRegularityThresholdReceipt as Carrier
import DASHI.Physics.Closure.NSDensityApproximationReceipt as Density

------------------------------------------------------------------------
-- Navier-Stokes carrier-to-all-data H^{11/8} extension receipt.
--
-- This receipt records the conditional extension route only.  Dense
-- prime-LP projections approximate arbitrary H^{11/8} data by
-- carrier-structured data; assuming uniform H^{11/8} bounds independent of
-- projection depth, Aubin-Lions compactness extracts a subsequence and
-- yields a limit solution candidate.  The all-data statement is therefore
-- conditional-candidate status only.  No Clay/global terminal promotion is
-- made here.

data NSCarrierToAllDataStatus : Set where
  carrierStructuredPositiveSobolevCandidateImported :
    NSCarrierToAllDataStatus

  densePrimeLPProjectionApproximationRecorded :
    NSCarrierToAllDataStatus

  uniformH118BoundsIndependentOfDepthRequired :
    NSCarrierToAllDataStatus

  aubinLionsSubsequenceExtractionRecorded :
    NSCarrierToAllDataStatus

  limitSolutionCandidateRecorded :
    NSCarrierToAllDataStatus

  allH118DataConditionalCandidateNoClayPromotion :
    NSCarrierToAllDataStatus

canonicalNSCarrierToAllDataStatus :
  List NSCarrierToAllDataStatus
canonicalNSCarrierToAllDataStatus =
  carrierStructuredPositiveSobolevCandidateImported
  ∷ densePrimeLPProjectionApproximationRecorded
  ∷ uniformH118BoundsIndependentOfDepthRequired
  ∷ aubinLionsSubsequenceExtractionRecorded
  ∷ limitSolutionCandidateRecorded
  ∷ allH118DataConditionalCandidateNoClayPromotion
  ∷ []

data NSCarrierToAllDataStep : Set where
  arbitraryH118InitialData :
    NSCarrierToAllDataStep

  densePrimeLPCarrierProjections :
    NSCarrierToAllDataStep

  carrierStructuredSolutionsAtEachDepth :
    NSCarrierToAllDataStep

  uniformH118AprioriBoundsIndependentOfDepth :
    NSCarrierToAllDataStep

  aubinLionsCompactnessSubsequence :
    NSCarrierToAllDataStep

  limitSolutionCandidateForOriginalData :
    NSCarrierToAllDataStep

canonicalNSCarrierToAllDataSteps :
  List NSCarrierToAllDataStep
canonicalNSCarrierToAllDataSteps =
  arbitraryH118InitialData
  ∷ densePrimeLPCarrierProjections
  ∷ carrierStructuredSolutionsAtEachDepth
  ∷ uniformH118AprioriBoundsIndependentOfDepth
  ∷ aubinLionsCompactnessSubsequence
  ∷ limitSolutionCandidateForOriginalData
  ∷ []

data NSAllH118ClaimStatus : Set where
  candidate :
    NSAllH118ClaimStatus

  conditionalCandidate :
    NSAllH118ClaimStatus

  notPromoted :
    NSAllH118ClaimStatus

data NSCarrierToAllDataFormalisationGap : Set where
  uniformH118BoundProofNeeded :
    NSCarrierToAllDataFormalisationGap

  aubinLionsPassageProofNeeded :
    NSCarrierToAllDataFormalisationGap

  limitSatisfiesNavierStokesProofNeeded :
    NSCarrierToAllDataFormalisationGap

  uniquenessOrSmoothnessNotClaimed :
    NSCarrierToAllDataFormalisationGap

canonicalNSCarrierToAllDataFormalisationGaps :
  List NSCarrierToAllDataFormalisationGap
canonicalNSCarrierToAllDataFormalisationGaps =
  uniformH118BoundProofNeeded
  ∷ aubinLionsPassageProofNeeded
  ∷ limitSatisfiesNavierStokesProofNeeded
  ∷ uniquenessOrSmoothnessNotClaimed
  ∷ []

data NSCarrierToAllDataPromotion : Set where

nsCarrierToAllDataPromotionImpossibleHere :
  NSCarrierToAllDataPromotion →
  ⊥
nsCarrierToAllDataPromotionImpossibleHere ()

nsCarrierToAllDataStatement : String
nsCarrierToAllDataStatement =
  "For arbitrary H^{11/8} initial data, dense prime-LP carrier projections reduce to carrier-structured data at finite depth.  If the carrier solutions obey uniform H^{11/8} bounds independent of depth, Aubin-Lions compactness gives a convergent subsequence and a limit solution candidate for the original data.  Thus nsGlobalRegularityForAllH118Data has conditional-candidate status only; no Clay, global terminal, or smoothness promotion is made."

canonicalNSGlobalRegularityForAllH118Data : String
canonicalNSGlobalRegularityForAllH118Data =
  "conditional candidate"

record NSCarrierToAllDataReceipt : Setω where
  field
    carrierReceipt :
      Carrier.NSCarrierRegularityThresholdReceipt

    carrierReceiptStatusCanonical :
      Carrier.status carrierReceipt
      ≡
      Carrier.canonicalNSCarrierRegularityThresholdStatus

    carrierStructuredCandidateImported :
      Carrier.nsGlobalRegularityForCarrierStructuredData carrierReceipt
      ≡
      Carrier.canonicalNSGlobalRegularityForCarrierStructuredData

    carrierReceiptNoClayPromotion :
      Carrier.clayNavierStokesPromoted carrierReceipt ≡ false

    densityReceipt :
      Density.NSDensityApproximationReceipt

    densityReceiptComponentsCanonical :
      Density.components densityReceipt
      ≡
      Density.canonicalNSDensityApproximationComponents

    densePrimeLPProjectionImported :
      Density.primeLPApproximatesArbitraryHs densityReceipt ≡ true

    carrierProjectionDensityImported :
      Density.carrierProjectionDenseInHs densityReceipt ≡ true

    densityReceiptNoClayPromotion :
      Density.clayNavierStokesPromoted densityReceipt ≡ false

    status :
      List NSCarrierToAllDataStatus

    statusIsCanonical :
      status ≡ canonicalNSCarrierToAllDataStatus

    steps :
      List NSCarrierToAllDataStep

    stepsAreCanonical :
      steps ≡ canonicalNSCarrierToAllDataSteps

    arbitraryH118DataScope :
      Bool

    arbitraryH118DataScopeIsTrue :
      arbitraryH118DataScope ≡ true

    h118SobolevNumerator :
      Nat

    h118SobolevNumeratorIs11 :
      h118SobolevNumerator ≡ 11

    h118SobolevDenominator :
      Nat

    h118SobolevDenominatorIs8 :
      h118SobolevDenominator ≡ 8

    densePrimeLPProjectionsToCarrierData :
      Bool

    densePrimeLPProjectionsToCarrierDataIsTrue :
      densePrimeLPProjectionsToCarrierData ≡ true

    projectionDepthParameterRecorded :
      Bool

    projectionDepthParameterRecordedIsTrue :
      projectionDepthParameterRecorded ≡ true

    carrierStructuredSolutionsAtEachDepthRecorded :
      Bool

    carrierStructuredSolutionsAtEachDepthRecordedIsTrue :
      carrierStructuredSolutionsAtEachDepthRecorded ≡ true

    uniformH118BoundsIndependentOfDepth :
      NSAllH118ClaimStatus

    uniformH118BoundsIndependentOfDepthIsCandidate :
      uniformH118BoundsIndependentOfDepth ≡ candidate

    uniformH118BoundsAssumedForExtension :
      Bool

    uniformH118BoundsAssumedForExtensionIsTrue :
      uniformH118BoundsAssumedForExtension ≡ true

    aubinLionsSubsequence :
      NSAllH118ClaimStatus

    aubinLionsSubsequenceIsCandidate :
      aubinLionsSubsequence ≡ candidate

    limitSolutionCandidate :
      NSAllH118ClaimStatus

    limitSolutionCandidateIsCandidate :
      limitSolutionCandidate ≡ candidate

    formalisationGaps :
      List NSCarrierToAllDataFormalisationGap

    formalisationGapsAreCanonical :
      formalisationGaps ≡ canonicalNSCarrierToAllDataFormalisationGaps

    nsGlobalRegularityForAllH118Data :
      String

    nsGlobalRegularityForAllH118DataIsConditionalCandidate :
      nsGlobalRegularityForAllH118Data
      ≡
      canonicalNSGlobalRegularityForAllH118Data

    allH118DataStatus :
      NSAllH118ClaimStatus

    allH118DataStatusIsConditionalCandidate :
      allH118DataStatus ≡ conditionalCandidate

    smoothClassicalSolutionPromoted :
      Bool

    smoothClassicalSolutionPromotedIsFalse :
      smoothClassicalSolutionPromoted ≡ false

    globalTerminalPromotion :
      Bool

    globalTerminalPromotionIsFalse :
      globalTerminalPromotion ≡ false

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
      statement ≡ nsCarrierToAllDataStatement

    promotionFlags :
      List NSCarrierToAllDataPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSCarrierToAllDataReceipt public

canonicalNSCarrierToAllDataReceipt :
  NSCarrierToAllDataReceipt
canonicalNSCarrierToAllDataReceipt =
  record
    { carrierReceipt =
        Carrier.canonicalNSCarrierRegularityThresholdReceipt
    ; carrierReceiptStatusCanonical =
        refl
    ; carrierStructuredCandidateImported =
        refl
    ; carrierReceiptNoClayPromotion =
        refl
    ; densityReceipt =
        Density.canonicalNSDensityApproximationReceipt
    ; densityReceiptComponentsCanonical =
        refl
    ; densePrimeLPProjectionImported =
        refl
    ; carrierProjectionDensityImported =
        refl
    ; densityReceiptNoClayPromotion =
        refl
    ; status =
        canonicalNSCarrierToAllDataStatus
    ; statusIsCanonical =
        refl
    ; steps =
        canonicalNSCarrierToAllDataSteps
    ; stepsAreCanonical =
        refl
    ; arbitraryH118DataScope =
        true
    ; arbitraryH118DataScopeIsTrue =
        refl
    ; h118SobolevNumerator =
        11
    ; h118SobolevNumeratorIs11 =
        refl
    ; h118SobolevDenominator =
        8
    ; h118SobolevDenominatorIs8 =
        refl
    ; densePrimeLPProjectionsToCarrierData =
        true
    ; densePrimeLPProjectionsToCarrierDataIsTrue =
        refl
    ; projectionDepthParameterRecorded =
        true
    ; projectionDepthParameterRecordedIsTrue =
        refl
    ; carrierStructuredSolutionsAtEachDepthRecorded =
        true
    ; carrierStructuredSolutionsAtEachDepthRecordedIsTrue =
        refl
    ; uniformH118BoundsIndependentOfDepth =
        candidate
    ; uniformH118BoundsIndependentOfDepthIsCandidate =
        refl
    ; uniformH118BoundsAssumedForExtension =
        true
    ; uniformH118BoundsAssumedForExtensionIsTrue =
        refl
    ; aubinLionsSubsequence =
        candidate
    ; aubinLionsSubsequenceIsCandidate =
        refl
    ; limitSolutionCandidate =
        candidate
    ; limitSolutionCandidateIsCandidate =
        refl
    ; formalisationGaps =
        canonicalNSCarrierToAllDataFormalisationGaps
    ; formalisationGapsAreCanonical =
        refl
    ; nsGlobalRegularityForAllH118Data =
        canonicalNSGlobalRegularityForAllH118Data
    ; nsGlobalRegularityForAllH118DataIsConditionalCandidate =
        refl
    ; allH118DataStatus =
        conditionalCandidate
    ; allH118DataStatusIsConditionalCandidate =
        refl
    ; smoothClassicalSolutionPromoted =
        false
    ; smoothClassicalSolutionPromotedIsFalse =
        refl
    ; globalTerminalPromotion =
        false
    ; globalTerminalPromotionIsFalse =
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
        nsCarrierToAllDataStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Scope is arbitrary H^{11/8} initial data, reached through dense prime-LP carrier projections"
        ∷ "Carrier-structured finite-depth solutions are imported only as candidate data"
        ∷ "Uniform H^{11/8} bounds independent of projection depth are recorded as the conditional hypothesis"
        ∷ "Aubin-Lions compactness extracts a subsequence and records a limit solution candidate"
        ∷ "nsGlobalRegularityForAllH118Data = conditional candidate"
        ∷ "No smooth classical solution, global terminal result, Clay Navier-Stokes result, or terminal Clay claim is promoted"
        ∷ []
    }
