module DASHI.Culture.IntellectualReceptionMultiResidueAdmissibilityLedgerExact where

------------------------------------------------------------------------
-- INTELLECTUAL RECEPTION / MULTI-RESIDUE ADMISSIBILITY LEDGER
--
-- A path can deposit several independent historical residues.  Reconverged
-- states may expose the same present and same future-cone code while retaining
-- different residue vectors and therefore different later admissible edge sets.
--
-- The binary irreversible-residue theorem is reused coordinatewise from
-- TrajectoryResidueExact.  This finite ledger and its reception semantics are
-- DASHI constructions, not claims about an actual intellectual history.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.TrajectoryResidueExact as Residue
import DASHI.Culture.IntellectualReceptionAdmissibilityStratumWhatIfExact as Stratum

------------------------------------------------------------------------
-- 1. Typed residue vector.
------------------------------------------------------------------------

record ReceptionResidueLedger : Set where
  constructor reception-residue-ledger
  field
    closureVisited : Residue.ResidueFlag
    archiveRecoveryVisited : Residue.ResidueFlag
    movementUptakeVisited : Residue.ResidueFlag
    pluralSelectionVisited : Residue.ResidueFlag
    institutionalAuthorityAcquired : Residue.ResidueFlag

open ReceptionResidueLedger public

emptyLedger : ReceptionResidueLedger
emptyLedger =
  reception-residue-ledger
    Residue.residueAbsent Residue.residueAbsent Residue.residueAbsent
    Residue.residueAbsent Residue.residueAbsent

closureLedger : ReceptionResidueLedger
closureLedger =
  reception-residue-ledger
    Residue.residuePresent Residue.residueAbsent Residue.residueAbsent
    Residue.residueAbsent Residue.residueAbsent

archivePluralLedger : ReceptionResidueLedger
archivePluralLedger =
  reception-residue-ledger
    Residue.residueAbsent Residue.residuePresent Residue.residueAbsent
    Residue.residuePresent Residue.residueAbsent

movementAuthorityLedger : ReceptionResidueLedger
movementAuthorityLedger =
  reception-residue-ledger
    Residue.residueAbsent Residue.residueAbsent Residue.residuePresent
    Residue.residueAbsent Residue.residuePresent

------------------------------------------------------------------------
-- 2. Finite itinerary carrier and deposition paths.
------------------------------------------------------------------------

data LedgerState : Set where
  sourceLedgerState
  closureVisitedState
  archivePluralVisitedState
  movementAuthorityVisitedState
  reconvergedClosureState
  reconvergedArchivePluralState
  reconvergedMovementAuthorityState
  archivePluralContinuationState
  movementContinuationState
  authorityContinuationState
  : LedgerState

ledger : LedgerState → ReceptionResidueLedger
ledger sourceLedgerState = emptyLedger
ledger closureVisitedState = closureLedger
ledger archivePluralVisitedState = archivePluralLedger
ledger movementAuthorityVisitedState = movementAuthorityLedger
ledger reconvergedClosureState = closureLedger
ledger reconvergedArchivePluralState = archivePluralLedger
ledger reconvergedMovementAuthorityState = movementAuthorityLedger
ledger archivePluralContinuationState = archivePluralLedger
ledger movementContinuationState = movementAuthorityLedger
ledger authorityContinuationState = movementAuthorityLedger

data LedgerStep : LedgerState → LedgerState → Set where
  visitClosure : LedgerStep sourceLedgerState closureVisitedState
  closureReconverges : LedgerStep closureVisitedState reconvergedClosureState
  visitArchivePlural : LedgerStep sourceLedgerState archivePluralVisitedState
  archivePluralReconverges : LedgerStep archivePluralVisitedState reconvergedArchivePluralState
  visitMovementAuthority : LedgerStep sourceLedgerState movementAuthorityVisitedState
  movementAuthorityReconverges :
    LedgerStep movementAuthorityVisitedState reconvergedMovementAuthorityState
  continueArchivePlural :
    LedgerStep reconvergedArchivePluralState archivePluralContinuationState
  continueMovement :
    LedgerStep reconvergedMovementAuthorityState movementContinuationState
  continueAuthority :
    LedgerStep reconvergedMovementAuthorityState authorityContinuationState

closureTrace : Residue.Trace LedgerStep sourceLedgerState reconvergedClosureState
closureTrace =
  Residue.traceStep visitClosure
    (Residue.traceStep closureReconverges Residue.traceRefl)

archivePluralTrace :
  Residue.Trace LedgerStep sourceLedgerState reconvergedArchivePluralState
archivePluralTrace =
  Residue.traceStep visitArchivePlural
    (Residue.traceStep archivePluralReconverges Residue.traceRefl)

movementAuthorityTrace :
  Residue.Trace LedgerStep sourceLedgerState reconvergedMovementAuthorityState
movementAuthorityTrace =
  Residue.traceStep visitMovementAuthority
    (Residue.traceStep movementAuthorityReconverges Residue.traceRefl)

------------------------------------------------------------------------
-- 3. Coordinatewise reuse of the canonical irreversible-residue theorem.
------------------------------------------------------------------------

closureFlag : LedgerState → Residue.ResidueFlag
closureFlag state = closureVisited (ledger state)

archiveFlag : LedgerState → Residue.ResidueFlag
archiveFlag state = archiveRecoveryVisited (ledger state)

movementFlag : LedgerState → Residue.ResidueFlag
movementFlag state = movementUptakeVisited (ledger state)

noClosureErasure : Residue.NoResidueErasure LedgerStep closureFlag
noClosureErasure visitClosure present = refl
noClosureErasure closureReconverges present = refl
noClosureErasure visitArchivePlural ()
noClosureErasure archivePluralReconverges ()
noClosureErasure visitMovementAuthority ()
noClosureErasure movementAuthorityReconverges ()
noClosureErasure continueArchivePlural ()
noClosureErasure continueMovement ()
noClosureErasure continueAuthority ()

noArchiveErasure : Residue.NoResidueErasure LedgerStep archiveFlag
noArchiveErasure visitClosure ()
noArchiveErasure closureReconverges ()
noArchiveErasure visitArchivePlural present = refl
noArchiveErasure archivePluralReconverges present = refl
noArchiveErasure visitMovementAuthority ()
noArchiveErasure movementAuthorityReconverges ()
noArchiveErasure continueArchivePlural present = refl
noArchiveErasure continueMovement ()
noArchiveErasure continueAuthority ()

noMovementErasure : Residue.NoResidueErasure LedgerStep movementFlag
noMovementErasure visitClosure ()
noMovementErasure closureReconverges ()
noMovementErasure visitArchivePlural ()
noMovementErasure archivePluralReconverges ()
noMovementErasure visitMovementAuthority present = refl
noMovementErasure movementAuthorityReconverges present = refl
noMovementErasure continueArchivePlural ()
noMovementErasure continueMovement present = refl
noMovementErasure continueAuthority present = refl

archiveResiduePersistsAfterReconvergence :
  ∀ {finish} →
  Residue.Trace LedgerStep reconvergedArchivePluralState finish →
  archiveFlag finish ≡ Residue.residuePresent
archiveResiduePersistsAfterReconvergence trace =
  Residue.tracePreservesPresentResidue noArchiveErasure trace refl

movementResiduePersistsAfterReconvergence :
  ∀ {finish} →
  Residue.Trace LedgerStep reconvergedMovementAuthorityState finish →
  movementFlag finish ≡ Residue.residuePresent
movementResiduePersistsAfterReconvergence trace =
  Residue.tracePreservesPresentResidue noMovementErasure trace refl

------------------------------------------------------------------------
-- 4. All three histories reconverge in present and future-cone observations.
------------------------------------------------------------------------

data ReconvergedLedgerCase : Set where
  closureCase archivePluralCase movementAuthorityCase : ReconvergedLedgerCase

data SameReconvergedPresent : Set where samePresent : SameReconvergedPresent

presentObserver : ReconvergedLedgerCase → SameReconvergedPresent
presentObserver _ = samePresent

futureObserver : ReconvergedLedgerCase → Stratum.FutureConeCode
futureObserver _ = Stratum.pluralContestableCone

------------------------------------------------------------------------
-- 5. Residue combination determines a different later edge profile.
------------------------------------------------------------------------

data LaterEdgeProfile : Set where
  closureRestrictedEdges
  archivePluralEdges
  movementAuthorityEdges
  : LaterEdgeProfile

edgeProfile : ReconvergedLedgerCase → LaterEdgeProfile
edgeProfile closureCase = closureRestrictedEdges
edgeProfile archivePluralCase = archivePluralEdges
edgeProfile movementAuthorityCase = movementAuthorityEdges

closureAndArchiveProfilesDiffer :
  edgeProfile closureCase ≡ edgeProfile archivePluralCase → ⊥
closureAndArchiveProfilesDiffer ()

archiveAndMovementProfilesDiffer :
  edgeProfile archivePluralCase ≡ edgeProfile movementAuthorityCase → ⊥
archiveAndMovementProfilesDiffer ()

samePresentCannotRecoverEdgeProfile :
  INF.FactorsThrough presentObserver edgeProfile → ⊥
samePresentCannotRecoverEdgeProfile =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      closureCase archivePluralCase refl closureAndArchiveProfilesDiffer)

sameFutureConeCannotRecoverEdgeProfile :
  INF.FactorsThrough futureObserver edgeProfile → ⊥
sameFutureConeCannotRecoverEdgeProfile =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      archivePluralCase movementAuthorityCase refl archiveAndMovementProfilesDiffer)

------------------------------------------------------------------------
-- 6. Edge-set semantics are explicit, not probabilistic weights.
------------------------------------------------------------------------

pluralEdgeEnabled : ReconvergedLedgerCase → Bool
pluralEdgeEnabled closureCase = false
pluralEdgeEnabled archivePluralCase = true
pluralEdgeEnabled movementAuthorityCase = false

movementEdgeEnabled : ReconvergedLedgerCase → Bool
movementEdgeEnabled closureCase = false
movementEdgeEnabled archivePluralCase = false
movementEdgeEnabled movementAuthorityCase = true

authorityEdgeEnabled : ReconvergedLedgerCase → Bool
authorityEdgeEnabled closureCase = false
authorityEdgeEnabled archivePluralCase = false
authorityEdgeEnabled movementAuthorityCase = true

archiveRoutePluralEdgeExists :
  pluralEdgeEnabled archivePluralCase ≡ true
archiveRoutePluralEdgeExists = refl

closureRoutePluralEdgeAbsent :
  pluralEdgeEnabled closureCase ≡ false
closureRoutePluralEdgeAbsent = refl

movementRouteMovementEdgeExists :
  movementEdgeEnabled movementAuthorityCase ≡ true
movementRouteMovementEdgeExists = refl

movementRouteAuthorityEdgeExists :
  authorityEdgeEnabled movementAuthorityCase ≡ true
movementRouteAuthorityEdgeExists = refl

------------------------------------------------------------------------
-- 7. The whole residue ledger is finer than the common reconverged surface.
------------------------------------------------------------------------

data LedgerCode : Set where
  closureOnlyCode archivePlusPluralCode movementPlusAuthorityCode : LedgerCode

ledgerCode : ReconvergedLedgerCase → LedgerCode
ledgerCode closureCase = closureOnlyCode
ledgerCode archivePluralCase = archivePlusPluralCode
ledgerCode movementAuthorityCase = movementPlusAuthorityCode

ledgerCodesDiffer :
  ledgerCode closureCase ≡ ledgerCode archivePluralCase → ⊥
ledgerCodesDiffer ()

sameReconvergedPresentCannotRecoverResidueLedger :
  INF.FactorsThrough presentObserver ledgerCode → ⊥
sameReconvergedPresentCannotRecoverResidueLedger =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      closureCase archivePluralCase refl ledgerCodesDiffer)

------------------------------------------------------------------------
-- 8. No-promotion boundaries.
------------------------------------------------------------------------

data ResidueVectorPromotesActualHistory : Set where
data ResidueVectorPromotesNecessaryDialectic : Set where
data AdmissibilityProfilePromotesProbabilityModel : Set where
data ReceptionLedgerPromotesBase369Stabiliser : Set where

residueVectorDoesNotPromoteActualHistory : ResidueVectorPromotesActualHistory → ⊥
residueVectorDoesNotPromoteActualHistory ()

residueVectorDoesNotPromoteNecessaryDialectic :
  ResidueVectorPromotesNecessaryDialectic → ⊥
residueVectorDoesNotPromoteNecessaryDialectic ()

admissibilityProfileDoesNotPromoteProbabilityModel :
  AdmissibilityProfilePromotesProbabilityModel → ⊥
admissibilityProfileDoesNotPromoteProbabilityModel ()

receptionLedgerDoesNotPromoteBase369Stabiliser :
  ReceptionLedgerPromotesBase369Stabiliser → ⊥
receptionLedgerDoesNotPromoteBase369Stabiliser ()

------------------------------------------------------------------------
-- 9. Canonical boundary.
------------------------------------------------------------------------

record IntellectualReceptionMultiResidueLedgerBoundary : Set where
  constructor intellectual-reception-multi-residue-ledger-boundary
  field
    residueCoordinatesAccumulateIndependently : Bool
    samePresentDeterminesResidueLedger : Bool
    sameFutureConeDeterminesLaterEdgeProfile : Bool
    residueCombinationCanChangeLaterEdgeSet : Bool
    absentEdgeMeansLowProbabilityEdge : Bool
    residueLedgerIsActualHistory : Bool
    residueLedgerIsBase369Stabiliser : Bool
    sourceAttributionBoundarySurvivesLedgerReasoning : Bool

canonicalIntellectualReceptionMultiResidueLedgerBoundary :
  IntellectualReceptionMultiResidueLedgerBoundary
canonicalIntellectualReceptionMultiResidueLedgerBoundary =
  intellectual-reception-multi-residue-ledger-boundary
    true false false true false false false true
