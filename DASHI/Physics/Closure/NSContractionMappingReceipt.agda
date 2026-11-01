module DASHI.Physics.Closure.NSContractionMappingReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.AdjacentOnlyVortexStretchingReceipt as Adjacent

------------------------------------------------------------------------
-- Navier-Stokes contraction-mapping resolution receipt.
--
-- This receipt records the Manager A4 resolution only.  The Picard/Stokes
-- iteration is the selected fixed-point scheme.  Small-data contraction is
-- immediate.  For large data, the only recorded candidate route is
-- adjacent-only high-frequency dominance plus a finite low-frequency ODE.
-- That candidate is recorded for all H118 carrier data, but the key
-- nonlinear high-frequency estimate is still unresolved.  No Clay/global or
-- terminal promotion is introduced.

data NSContractionIteration : Set where
  picardStokesIteration :
    NSContractionIteration

data NSContractionDataRegime : Set where
  smallDataRegime :
    NSContractionDataRegime

  largeDataRegime :
    NSContractionDataRegime

data NSLargeDataContractionIngredient : Set where
  adjacentOnlyHighFrequencyDominance :
    NSLargeDataContractionIngredient

  finiteLowFrequencyODE :
    NSLargeDataContractionIngredient

canonicalNSLargeDataContractionIngredients :
  List NSLargeDataContractionIngredient
canonicalNSLargeDataContractionIngredients =
  adjacentOnlyHighFrequencyDominance
  ∷ finiteLowFrequencyODE
  ∷ []

data NSContractionMappingStatus : Set where
  picardStokesIterationSelected :
    NSContractionMappingStatus

  smallDataContractionImmediateStatus :
    NSContractionMappingStatus

  largeDataAdjacentHighFrequencyFiniteLowODECandidateStatus :
    NSContractionMappingStatus

  candidateForAllH118CarrierDataStatus :
    NSContractionMappingStatus

  keyEstimateUnresolvedStatus :
    NSContractionMappingStatus

  noClayOrTerminalPromotionStatus :
    NSContractionMappingStatus

canonicalNSContractionMappingStatus :
  List NSContractionMappingStatus
canonicalNSContractionMappingStatus =
  picardStokesIterationSelected
  ∷ smallDataContractionImmediateStatus
  ∷ largeDataAdjacentHighFrequencyFiniteLowODECandidateStatus
  ∷ candidateForAllH118CarrierDataStatus
  ∷ keyEstimateUnresolvedStatus
  ∷ noClayOrTerminalPromotionStatus
  ∷ []

data H118CarrierDataScope : Set where
  allH118CarrierData :
    H118CarrierDataScope

data NSContractionPromotion : Set where

nsContractionPromotionImpossibleHere :
  NSContractionPromotion →
  ⊥
nsContractionPromotionImpossibleHere ()

nsContractionMappingStatement : String
nsContractionMappingStatement =
  "NS contraction mapping resolution: use Picard/Stokes iteration; small-data contraction is immediate; large-data contraction is only a candidate from adjacent-only high-frequency dominance plus finite low-frequency ODE, recorded for all H118 carrier data; the key nonlinear high-frequency estimate remains unresolved."

keyUnresolvedEstimateStatement : String
keyUnresolvedEstimateStatement =
  "Unresolved estimate: prove adjacent-only high-frequency dominance strong enough to make the Picard/Stokes nonlinear map a strict contraction after coupling to the finite low-frequency ODE, uniformly for H118 carrier data."

record NSContractionMappingReceipt : Setω where
  field
    adjacentOnlyReceipt :
      Adjacent.AdjacentOnlyVortexStretchingReceipt

    adjacentOnlyStatusCanonical :
      Adjacent.status adjacentOnlyReceipt
      ≡
      Adjacent.canonicalAdjacentOnlyVortexStretchingStatus

    adjacentOnlyHighFrequencyDiagnosticRecorded :
      Adjacent.highFrequencyCrossBaseResonancesSparseOrAbsent
        adjacentOnlyReceipt
      ≡
      true

    adjacentOnlySameBaseBandDiagnosticRecorded :
      Adjacent.sameBaseResonancesAdjacentBandOnly adjacentOnlyReceipt
      ≡
      true

    adjacentOnlyDoesNotPromoteClay :
      Adjacent.clayNavierStokesPromoted adjacentOnlyReceipt
      ≡
      false

    iteration :
      NSContractionIteration

    iterationIsPicardStokes :
      iteration ≡ picardStokesIteration

    regimes :
      List NSContractionDataRegime

    regimesAreCanonical :
      regimes ≡ smallDataRegime ∷ largeDataRegime ∷ []

    smallDataContractionImmediate :
      Bool

    smallDataContractionImmediateIsTrue :
      smallDataContractionImmediate ≡ true

    largeDataIngredients :
      List NSLargeDataContractionIngredient

    largeDataIngredientsAreCanonical :
      largeDataIngredients ≡ canonicalNSLargeDataContractionIngredients

    largeDataContractionCandidateRecorded :
      Bool

    largeDataContractionCandidateRecordedIsTrue :
      largeDataContractionCandidateRecorded ≡ true

    largeDataContractionProved :
      Bool

    largeDataContractionProvedIsFalse :
      largeDataContractionProved ≡ false

    h118CarrierDataScope :
      H118CarrierDataScope

    h118CarrierDataScopeIsAll :
      h118CarrierDataScope ≡ allH118CarrierData

    candidateForAllH118CarrierData :
      Bool

    candidateForAllH118CarrierDataIsTrue :
      candidateForAllH118CarrierData ≡ true

    finiteLowFrequencyODECandidateRecorded :
      Bool

    finiteLowFrequencyODECandidateRecordedIsTrue :
      finiteLowFrequencyODECandidateRecorded ≡ true

    adjacentOnlyHighFrequencyDominanceCandidateRecorded :
      Bool

    adjacentOnlyHighFrequencyDominanceCandidateRecordedIsTrue :
      adjacentOnlyHighFrequencyDominanceCandidateRecorded ≡ true

    keyNonlinearHighFrequencyEstimateResolved :
      Bool

    keyNonlinearHighFrequencyEstimateResolvedIsFalse :
      keyNonlinearHighFrequencyEstimateResolved ≡ false

    contractionMappingTheoremClosed :
      Bool

    contractionMappingTheoremClosedIsFalse :
      contractionMappingTheoremClosed ≡ false

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalPromotionClaimed :
      Bool

    terminalPromotionClaimedIsFalse :
      terminalPromotionClaimed ≡ false

    status :
      List NSContractionMappingStatus

    statusIsCanonical :
      status ≡ canonicalNSContractionMappingStatus

    statement :
      String

    statementIsCanonical :
      statement ≡ nsContractionMappingStatement

    keyUnresolvedEstimate :
      String

    keyUnresolvedEstimateIsCanonical :
      keyUnresolvedEstimate ≡ keyUnresolvedEstimateStatement

    promotionFlags :
      List NSContractionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSContractionMappingReceipt public

canonicalNSContractionMappingReceipt :
  NSContractionMappingReceipt
canonicalNSContractionMappingReceipt =
  record
    { adjacentOnlyReceipt =
        Adjacent.canonicalAdjacentOnlyVortexStretchingReceipt
    ; adjacentOnlyStatusCanonical =
        refl
    ; adjacentOnlyHighFrequencyDiagnosticRecorded =
        refl
    ; adjacentOnlySameBaseBandDiagnosticRecorded =
        refl
    ; adjacentOnlyDoesNotPromoteClay =
        refl
    ; iteration =
        picardStokesIteration
    ; iterationIsPicardStokes =
        refl
    ; regimes =
        smallDataRegime
        ∷ largeDataRegime
        ∷ []
    ; regimesAreCanonical =
        refl
    ; smallDataContractionImmediate =
        true
    ; smallDataContractionImmediateIsTrue =
        refl
    ; largeDataIngredients =
        canonicalNSLargeDataContractionIngredients
    ; largeDataIngredientsAreCanonical =
        refl
    ; largeDataContractionCandidateRecorded =
        true
    ; largeDataContractionCandidateRecordedIsTrue =
        refl
    ; largeDataContractionProved =
        false
    ; largeDataContractionProvedIsFalse =
        refl
    ; h118CarrierDataScope =
        allH118CarrierData
    ; h118CarrierDataScopeIsAll =
        refl
    ; candidateForAllH118CarrierData =
        true
    ; candidateForAllH118CarrierDataIsTrue =
        refl
    ; finiteLowFrequencyODECandidateRecorded =
        true
    ; finiteLowFrequencyODECandidateRecordedIsTrue =
        refl
    ; adjacentOnlyHighFrequencyDominanceCandidateRecorded =
        true
    ; adjacentOnlyHighFrequencyDominanceCandidateRecordedIsTrue =
        refl
    ; keyNonlinearHighFrequencyEstimateResolved =
        false
    ; keyNonlinearHighFrequencyEstimateResolvedIsFalse =
        refl
    ; contractionMappingTheoremClosed =
        false
    ; contractionMappingTheoremClosedIsFalse =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalPromotionClaimed =
        false
    ; terminalPromotionClaimedIsFalse =
        refl
    ; status =
        canonicalNSContractionMappingStatus
    ; statusIsCanonical =
        refl
    ; statement =
        nsContractionMappingStatement
    ; statementIsCanonical =
        refl
    ; keyUnresolvedEstimate =
        keyUnresolvedEstimateStatement
    ; keyUnresolvedEstimateIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Picard/Stokes iteration is selected as the contraction-mapping resolution scheme"
        ∷ "Small-data contraction is recorded as immediate"
        ∷ "Large-data contraction is only a candidate: adjacent-only high-frequency dominance plus finite low-frequency ODE"
        ∷ "The candidate is recorded for all H118 carrier data"
        ∷ "The key nonlinear high-frequency dominance estimate is unresolved"
        ∷ "No Clay Navier-Stokes, global regularity, or terminal promotion is claimed"
        ∷ []
    }

nsContractionSmallDataImmediate :
  smallDataContractionImmediate canonicalNSContractionMappingReceipt ≡ true
nsContractionSmallDataImmediate =
  refl

nsContractionLargeDataCandidateOnly :
  largeDataContractionProved canonicalNSContractionMappingReceipt ≡ false
nsContractionLargeDataCandidateOnly =
  refl

nsContractionCandidateForAllH118CarrierData :
  candidateForAllH118CarrierData canonicalNSContractionMappingReceipt ≡ true
nsContractionCandidateForAllH118CarrierData =
  refl

nsContractionKeyEstimateUnresolved :
  keyNonlinearHighFrequencyEstimateResolved canonicalNSContractionMappingReceipt
  ≡
  false
nsContractionKeyEstimateUnresolved =
  refl

nsContractionNoClayPromotion :
  clayNavierStokesPromoted canonicalNSContractionMappingReceipt ≡ false
nsContractionNoClayPromotion =
  refl

nsContractionNoTerminalPromotion :
  terminalPromotionClaimed canonicalNSContractionMappingReceipt ≡ false
nsContractionNoTerminalPromotion =
  refl

nsContractionNoPromotion :
  NSContractionPromotion →
  ⊥
nsContractionNoPromotion =
  nsContractionPromotionImpossibleHere
