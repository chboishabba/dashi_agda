module DASHI.Culture.IntellectualReceptionStratumItineraryAdmissibilityMemoryExact where

------------------------------------------------------------------------
-- INTELLECTUAL RECEPTION / STRATUM ITINERARY / ADMISSIBILITY MEMORY
--
-- A reception path may pass through an intermediate stratum whose effects are
-- not reconstructible from a later coarse surface.  The canonical trajectory-
-- residue owner is used for the persistent-memory theorem; this module supplies
-- a finite reception-specific itinerary and an admissibility consequence.
--
-- The fixture is a DASHI construction.  It is not a historical claim and it is
-- not identified with Base369 geometry, gauge holonomy or Monster structure.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.TrajectoryResidueExact as Residue
import DASHI.Culture.IntellectualReceptionAdmissibilityStratumWhatIfExact as Stratum

------------------------------------------------------------------------
-- 1. Fine itinerary states.
------------------------------------------------------------------------

data ItineraryState : Set where
  sourceOpen
  canonClosureVisited
  archiveRecoveryVisited
  reconvergedAfterClosure
  reconvergedAfterArchive
  pluralContinuationAfterArchive
  : ItineraryState

-- The two reconverged states intentionally expose the same present/future
-- observer despite having traversed different intermediate strata.

presentSurface : ItineraryState → Stratum.CoarseReceptionPosition
presentSurface _ = Stratum.samePresentVocabulary

futureSurface : ItineraryState → Stratum.FutureConeCode
futureSurface sourceOpen = Stratum.canonDominantCone
futureSurface canonClosureVisited = Stratum.canonDominantCone
futureSurface archiveRecoveryVisited = Stratum.archivalReconstructionCone
futureSurface reconvergedAfterClosure = Stratum.pluralContestableCone
futureSurface reconvergedAfterArchive = Stratum.pluralContestableCone
futureSurface pluralContinuationAfterArchive = Stratum.pluralContestableCone

reconvergedFutureSurfaceSame :
  futureSurface reconvergedAfterClosure ≡ futureSurface reconvergedAfterArchive
reconvergedFutureSurfaceSame = refl

------------------------------------------------------------------------
-- 2. Explicit stratum itinerary relation.
------------------------------------------------------------------------

data ItineraryStep : ItineraryState → ItineraryState → Set where
  visitCanonClosure : ItineraryStep sourceOpen canonClosureVisited
  leaveCanonClosure : ItineraryStep canonClosureVisited reconvergedAfterClosure
  visitArchiveRecovery : ItineraryStep sourceOpen archiveRecoveryVisited
  leaveArchiveRecovery : ItineraryStep archiveRecoveryVisited reconvergedAfterArchive
  continuePluralAfterArchive :
    ItineraryStep reconvergedAfterArchive pluralContinuationAfterArchive

closureItinerary : Residue.Trace ItineraryStep sourceOpen reconvergedAfterClosure
closureItinerary =
  Residue.traceStep visitCanonClosure
    (Residue.traceStep leaveCanonClosure Residue.traceRefl)

archiveItinerary : Residue.Trace ItineraryStep sourceOpen reconvergedAfterArchive
archiveItinerary =
  Residue.traceStep visitArchiveRecovery
    (Residue.traceStep leaveArchiveRecovery Residue.traceRefl)

------------------------------------------------------------------------
-- 3. Itinerary codes remain finer than the reconverged observer.
------------------------------------------------------------------------

data ReconvergedCase : Set where
  viaClosure viaArchive : ReconvergedCase

data ItineraryCode : Set where
  sourceCanonClosureReconverge
  sourceArchiveRecoveryReconverge
  : ItineraryCode

data ReconvergedSurface : Set where
  sameReconvergedSurface : ReconvergedSurface

reconvergedSurface : ReconvergedCase → ReconvergedSurface
reconvergedSurface _ = sameReconvergedSurface

itineraryCode : ReconvergedCase → ItineraryCode
itineraryCode viaClosure = sourceCanonClosureReconverge
itineraryCode viaArchive = sourceArchiveRecoveryReconverge

itineraryCodesDiffer :
  itineraryCode viaClosure ≡ itineraryCode viaArchive → ⊥
itineraryCodesDiffer ()

sameReconvergedSurfaceCannotRecoverItinerary :
  INF.FactorsThrough reconvergedSurface itineraryCode → ⊥
sameReconvergedSurfaceCannotRecoverItinerary =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness viaClosure viaArchive refl itineraryCodesDiffer)

------------------------------------------------------------------------
-- 4. Canonical trajectory residue: closure visitation deposits memory.
------------------------------------------------------------------------

closureResidue : ItineraryState → Residue.ResidueFlag
closureResidue sourceOpen = Residue.residueAbsent
closureResidue canonClosureVisited = Residue.residuePresent
closureResidue archiveRecoveryVisited = Residue.residueAbsent
closureResidue reconvergedAfterClosure = Residue.residuePresent
closureResidue reconvergedAfterArchive = Residue.residueAbsent
closureResidue pluralContinuationAfterArchive = Residue.residueAbsent

noClosureResidueErasure : Residue.NoResidueErasure ItineraryStep closureResidue
noClosureResidueErasure visitCanonClosure present = refl
noClosureResidueErasure leaveCanonClosure present = refl
noClosureResidueErasure visitArchiveRecovery ()
noClosureResidueErasure leaveArchiveRecovery ()
noClosureResidueErasure continuePluralAfterArchive ()

closureResidueDeposition :
  Residue.ResidueDeposition ItineraryStep closureResidue
closureResidueDeposition =
  Residue.residueDeposition
    sourceOpen
    reconvergedAfterClosure
    closureItinerary
    refl
    refl

closureResiduePersistsAcrossFurtherTrace :
  ∀ {finish} →
  Residue.Trace ItineraryStep reconvergedAfterClosure finish →
  closureResidue finish ≡ Residue.residuePresent
closureResiduePersistsAcrossFurtherTrace trace =
  Residue.tracePreservesPresentResidue
    noClosureResidueErasure
    trace
    refl

------------------------------------------------------------------------
-- 5. Reconvergence does not imply equal later admissibility.
--
-- The archive route retains an admitted plural continuation.  The closure route
-- has no corresponding edge.  This is absence of an admitted edge, not a small
-- probability assigned to the same edge.
------------------------------------------------------------------------

data ContinuationMove : Set where pluraliseAgain : ContinuationMove

data ContinuationAdmission : Set where admitted blocked : ContinuationAdmission

continuationAdmission : ReconvergedCase → ContinuationAdmission
continuationAdmission viaClosure = blocked
continuationAdmission viaArchive = admitted

continuationAdmissionsDiffer :
  continuationAdmission viaClosure ≡ continuationAdmission viaArchive → ⊥
continuationAdmissionsDiffer ()

sameReconvergedSurfaceCannotRecoverLaterAdmissibility :
  INF.FactorsThrough reconvergedSurface continuationAdmission → ⊥
sameReconvergedSurfaceCannotRecoverLaterAdmissibility =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      viaClosure viaArchive refl continuationAdmissionsDiffer)

archiveRouteHasPluralContinuation :
  ItineraryStep reconvergedAfterArchive pluralContinuationAfterArchive
archiveRouteHasPluralContinuation = continuePluralAfterArchive

-- There is deliberately no constructor of
-- ItineraryStep reconvergedAfterClosure pluralContinuationAfterArchive.

data ClosureRoutePluralContinuation : Set where

closureRouteCannotManufacturePluralContinuation :
  ClosureRoutePluralContinuation → ⊥
closureRouteCannotManufacturePluralContinuation ()

------------------------------------------------------------------------
-- 6. Residue is not recoverable from the coarse reconverged surface.
------------------------------------------------------------------------

data ReconvergedFineState : Set where
  closureReconverged archiveReconverged : ReconvergedFineState

coarseReconverged : ReconvergedFineState → ReconvergedSurface
coarseReconverged _ = sameReconvergedSurface

reconvergedResidue : ReconvergedFineState → Residue.ResidueFlag
reconvergedResidue closureReconverged = Residue.residuePresent
reconvergedResidue archiveReconverged = Residue.residueAbsent

coarseReconvergenceCannotRecoverClosureResidue :
  Residue.ResidueDescendsThrough coarseReconverged reconvergedResidue → ⊥
coarseReconvergenceCannotRecoverClosureResidue =
  Residue.coarseCollisionAcrossResidueBlocksDescent
    refl refl refl

------------------------------------------------------------------------
-- 7. No-promotion boundaries.
------------------------------------------------------------------------

data ReconvergencePromotesSameHistory : Set where
data SameFuturePromotesSameAdmissibility : Set where
data ClosureResiduePromotesHistoricalNecessity : Set where
data ItineraryPromotesPhysicalWorldline : Set where
data ItineraryPromotesBase369Identity : Set where

reconvergenceDoesNotPromoteSameHistory : ReconvergencePromotesSameHistory → ⊥
reconvergenceDoesNotPromoteSameHistory ()

sameFutureDoesNotPromoteSameAdmissibility : SameFuturePromotesSameAdmissibility → ⊥
sameFutureDoesNotPromoteSameAdmissibility ()

closureResidueDoesNotPromoteHistoricalNecessity :
  ClosureResiduePromotesHistoricalNecessity → ⊥
closureResidueDoesNotPromoteHistoricalNecessity ()

itineraryDoesNotPromotePhysicalWorldline : ItineraryPromotesPhysicalWorldline → ⊥
itineraryDoesNotPromotePhysicalWorldline ()

itineraryDoesNotPromoteBase369Identity : ItineraryPromotesBase369Identity → ⊥
itineraryDoesNotPromoteBase369Identity ()

------------------------------------------------------------------------
-- 8. Canonical boundary.
------------------------------------------------------------------------

record IntellectualReceptionStratumItineraryMemoryBoundary : Set where
  constructor intellectual-reception-stratum-itinerary-memory-boundary
  field
    sameReconvergedSurfaceDeterminesItinerary : Bool
    sameReconvergedFutureDeterminesLaterAdmissibility : Bool
    pathDepositedResidueCanPersist : Bool
    intermediateStratumCanAlterLaterReachability : Bool
    missingEdgeMeansLowProbabilityEdge : Bool
    itineraryIsActualHistory : Bool
    itineraryIsPhysicalWorldline : Bool
    sourceAttributionBoundarySurvivesItineraryReasoning : Bool

canonicalIntellectualReceptionStratumItineraryMemoryBoundary :
  IntellectualReceptionStratumItineraryMemoryBoundary
canonicalIntellectualReceptionStratumItineraryMemoryBoundary =
  intellectual-reception-stratum-itinerary-memory-boundary
    false false true true false false false true
