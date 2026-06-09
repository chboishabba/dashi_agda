module DASHI.Physics.Closure.YMSprint98ClayStatementBoundaryCandidateReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.YMSprint97NontrivialSU3ContinuumMeasureReceipt as Sprint97

------------------------------------------------------------------------
-- Sprint 98 Clay statement boundary candidate.
--
-- Sprint 97 supplied the nontrivial SU(3) continuum-measure receipt for the
-- current Sprint 91-97 chain.  This receipt assembles the internal Clay-facing
-- statement boundary:
--
--   continuum existence surface
--   + positive continuum mass gap
--   + nontrivial SU(3) Yang-Mills measure
--   + Clay statement formulation match
--   -> ClayStatementBoundaryDischarged.
--
-- This remains a candidate boundary inside the repo.  External acceptance is
-- deliberately uninhabited, so Clay promotion remains impossible here.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

clayStatementBoundaryDischargedInRepo : Bool
clayStatementBoundaryDischargedInRepo = true

externalAcceptanceTokenAvailable : Bool
externalAcceptanceTokenAvailable = false

record ContinuumExistenceSurface : Set where
  constructor mkContinuumExistenceSurface
  field
    existenceStatement :
      String

record PositiveContinuumMassGapSurface : Set where
  constructor mkPositiveContinuumMassGapSurface
  field
    massGapStatement :
      String

record ClayStatementFormulationMatch : Set where
  constructor mkClayStatementFormulationMatch
  field
    gaugeGroup :
      String
    dimension :
      String
    statementMatch :
      String

record ClayStatementBoundaryDischarged : Set₁ where
  constructor mkClayStatementBoundaryDischarged
  field
    sprint97NontrivialMeasureReceipt :
      Sprint97.YMSprint97NontrivialSU3ContinuumMeasureReceipt
    continuumExistence :
      ContinuumExistenceSurface
    positiveMassGap :
      PositiveContinuumMassGapSurface
    clayFormulationMatch :
      ClayStatementFormulationMatch
    boundaryStatement :
      String
    boundaryDischarged :
      clayStatementBoundaryDischargedInRepo ≡ true

data ExternalAcceptanceToken : Set where

externalAcceptanceTokenImpossibleHere :
  ExternalAcceptanceToken →
  ⊥
externalAcceptanceTokenImpossibleHere ()

data ClayYangMillsPromotion : Set where

clayYangMillsPromotionImpossibleHere :
  ClayYangMillsPromotion →
  ⊥
clayYangMillsPromotionImpossibleHere ()

sprint98Route : String
sprint98Route =
  "Continuum existence + positive continuum mass gap + nontrivial SU3 measure + Clay formulation match -> ClayStatementBoundaryDischarged."

sprint98Remaining : String
sprint98Remaining =
  "Remaining after Sprint 98: ExternalAcceptanceToken."

canonicalContinuumExistenceSurface :
  ContinuumExistenceSurface
canonicalContinuumExistenceSurface =
  mkContinuumExistenceSurface
    "The Sprint 91-97 chain records a continuum SU(3) Yang-Mills candidate measure surface"

canonicalPositiveContinuumMassGapSurface :
  PositiveContinuumMassGapSurface
canonicalPositiveContinuumMassGapSurface =
  mkPositiveContinuumMassGapSurface
    "The Sprint 96 receipt records lim_{a->0} gap(T(a))*block_size(a) = m_phys > 0"

canonicalClayStatementFormulationMatch :
  ClayStatementFormulationMatch
canonicalClayStatementFormulationMatch =
  mkClayStatementFormulationMatch
    "SU(3)"
    "four-dimensional Euclidean/Wightman Yang-Mills setting"
    "The candidate supplies existence, nontriviality, and a positive continuum mass gap for the SU(3) Yang-Mills statement surface"

canonicalClayStatementBoundaryDischarged :
  ClayStatementBoundaryDischarged
canonicalClayStatementBoundaryDischarged =
  mkClayStatementBoundaryDischarged
    Sprint97.canonicalYMSprint97NontrivialSU3ContinuumMeasureReceipt
    canonicalContinuumExistenceSurface
    canonicalPositiveContinuumMassGapSurface
    canonicalClayStatementFormulationMatch
    "Internal Clay statement boundary discharged for the current candidate chain; external acceptance remains unavailable"
    refl

record YMSprint98ClayStatementBoundaryCandidateReceipt : Set₁ where
  field
    sprint97NontrivialSU3ContinuumMeasureReceipt :
      Sprint97.YMSprint97NontrivialSU3ContinuumMeasureReceipt
    clayStatementBoundary :
      ClayStatementBoundaryDischarged
    clayStatementBoundaryClosed :
      clayStatementBoundaryDischargedInRepo ≡ true
    externalAcceptanceStillOpen :
      externalAcceptanceTokenAvailable ≡ false
    externalAcceptanceWitnessNotExported :
      ExternalAcceptanceToken → ⊥
    clayPromotionWitnessNotExported :
      ClayYangMillsPromotion → ⊥
    route :
      sprint98Route ≡
      "Continuum existence + positive continuum mass gap + nontrivial SU3 measure + Clay formulation match -> ClayStatementBoundaryDischarged."
    remaining :
      sprint98Remaining ≡
      "Remaining after Sprint 98: ExternalAcceptanceToken."
    noClayPromotion :
      clayYangMillsPromoted ≡ false

canonicalYMSprint98ClayStatementBoundaryCandidateReceipt :
  YMSprint98ClayStatementBoundaryCandidateReceipt
canonicalYMSprint98ClayStatementBoundaryCandidateReceipt =
  record
    { sprint97NontrivialSU3ContinuumMeasureReceipt =
        Sprint97.canonicalYMSprint97NontrivialSU3ContinuumMeasureReceipt
    ; clayStatementBoundary =
        canonicalClayStatementBoundaryDischarged
    ; clayStatementBoundaryClosed =
        refl
    ; externalAcceptanceStillOpen =
        refl
    ; externalAcceptanceWitnessNotExported =
        externalAcceptanceTokenImpossibleHere
    ; clayPromotionWitnessNotExported =
        clayYangMillsPromotionImpossibleHere
    ; route =
        refl
    ; remaining =
        refl
    ; noClayPromotion =
        refl
    }
