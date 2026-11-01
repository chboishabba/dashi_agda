module DASHI.Physics.Closure.NSSprint91LocalizedFluxIdentityAndCoefficientBudget where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSSprint90LocalEnstrophyDangerShellReductionReceipt
  as Sprint90
import DASHI.Physics.Closure.NSTailFluxLPIdentityFullDerivationReceipt
  as Full
import DASHI.Physics.Closure.NSAdjacentShellLeakageBoundReceipt
  as Leak

------------------------------------------------------------------------
-- Sprint 91 localized fixed-K flux identity receipt.
--
-- Sprint 91 imports the existing fixed-K Littlewood-Paley identity as
-- bookkeeping for the localized flux identity gate selected in Sprint 90.
-- The import is intentionally fixed-K only: it records no moving K*(t)
-- boundary term, no high-high dominance theorem, no pointwise tail extraction,
-- no independent coefficient budget, and no Clay Navier-Stokes promotion.

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

localizedEnstrophyFluxIdentityClosed : Bool
localizedEnstrophyFluxIdentityClosed = true

dangerShellDissipationDominatesInfluxClosed : Bool
dangerShellDissipationDominatesInfluxClosed = false

pointwiseTailFromLocalDissipationClosed : Bool
pointwiseTailFromLocalDissipationClosed = false

independentCoefficientBudgetClosed : Bool
independentCoefficientBudgetClosed = false

data LocalizedFluxIdentityImportedFromFixedKLP : Set where
  importedFromFullFixedKLittlewoodPaleyIdentity :
    LocalizedFluxIdentityImportedFromFixedKLP

canonicalLocalizedFluxIdentityImportedFromFixedKLP :
  LocalizedFluxIdentityImportedFromFixedKLP
canonicalLocalizedFluxIdentityImportedFromFixedKLP =
  importedFromFullFixedKLittlewoodPaleyIdentity

data MovingKStarLocalizationBoundary : Set where
  movingKStarBoundaryNotClosedByFixedKImport :
    MovingKStarLocalizationBoundary

canonicalMovingKStarLocalizationBoundary :
  MovingKStarLocalizationBoundary
canonicalMovingKStarLocalizationBoundary =
  movingKStarBoundaryNotClosedByFixedKImport

data AdjacentLeakageBudgetAvailable : Set where
  adjacentLeakageBudgetRecordedButNotDominating :
    AdjacentLeakageBudgetAvailable

canonicalAdjacentLeakageBudgetAvailable :
  AdjacentLeakageBudgetAvailable
canonicalAdjacentLeakageBudgetAvailable =
  adjacentLeakageBudgetRecordedButNotDominating

data HighHighDominanceStillOpen : Set where
  highHighDominanceNotSuppliedByAdjacentLeakage :
    HighHighDominanceStillOpen

canonicalHighHighDominanceStillOpen :
  HighHighDominanceStillOpen
canonicalHighHighDominanceStillOpen =
  highHighDominanceNotSuppliedByAdjacentLeakage

data IndependentCoefficientStillOpen : Set where
  independentCoefficientNotProducedByIdentityImport :
    IndependentCoefficientStillOpen

canonicalIndependentCoefficientStillOpen :
  IndependentCoefficientStillOpen
canonicalIndependentCoefficientStillOpen =
  independentCoefficientNotProducedByIdentityImport

data Sprint91ClosedBookkeeping : Set where
  sprint90ReductionInherited :
    Sprint91ClosedBookkeeping
  fullFixedKLPIdentityImported :
    Sprint91ClosedBookkeeping
  localizedFluxIdentityBookedAtFixedK :
    Sprint91ClosedBookkeeping
  adjacentLeakageBudgetRecorded :
    Sprint91ClosedBookkeeping

canonicalSprint91ClosedBookkeeping : List Sprint91ClosedBookkeeping
canonicalSprint91ClosedBookkeeping =
  sprint90ReductionInherited
  ∷ fullFixedKLPIdentityImported
  ∷ localizedFluxIdentityBookedAtFixedK
  ∷ adjacentLeakageBudgetRecorded
  ∷ []

data Sprint91OpenBoundary : Set where
  movingKStarLocalizationBoundaryOpen :
    Sprint91OpenBoundary
  dangerShellDissipationDominanceOpen :
    Sprint91OpenBoundary
  pointwiseTailExtractionOpen :
    Sprint91OpenBoundary
  highHighDominanceOpen :
    Sprint91OpenBoundary
  independentCoefficientBudgetOpen :
    Sprint91OpenBoundary
  clayNavierStokesPromotionOpen :
    Sprint91OpenBoundary

canonicalSprint91OpenBoundaries : List Sprint91OpenBoundary
canonicalSprint91OpenBoundaries =
  movingKStarLocalizationBoundaryOpen
  ∷ dangerShellDissipationDominanceOpen
  ∷ pointwiseTailExtractionOpen
  ∷ highHighDominanceOpen
  ∷ independentCoefficientBudgetOpen
  ∷ clayNavierStokesPromotionOpen
  ∷ []

sprint91IdentityImportStatement : String
sprint91IdentityImportStatement =
  "Sprint 91 closes only localizedEnstrophyFluxIdentityClosed by importing the existing full fixed-K Littlewood-Paley identity derivation as bookkeeping at K=0."

sprint91BoundaryStatement : String
sprint91BoundaryStatement =
  "The fixed-K import does not close moving K*(t) localization, danger-shell dissipation domination, pointwise tail extraction, high-high dominance, independent coefficient budgeting, or Clay Navier-Stokes."

record Sprint91CoefficientBudgetLedger : Set where
  constructor coefficientBudgetLedger
  field
    importedIdentity :
      LocalizedFluxIdentityImportedFromFixedKLP
    movingBoundary :
      MovingKStarLocalizationBoundary
    adjacentLeakage :
      AdjacentLeakageBudgetAvailable
    highHighDominance :
      HighHighDominanceStillOpen
    independentCoefficient :
      IndependentCoefficientStillOpen
    localizedFluxIdentityClosedHere :
      Bool
    localizedFluxIdentityClosedHereIsTrue :
      localizedFluxIdentityClosedHere ≡ true
    dangerDominanceClosedHere :
      Bool
    dangerDominanceClosedHereIsFalse :
      dangerDominanceClosedHere ≡ false
    pointwiseTailClosedHere :
      Bool
    pointwiseTailClosedHereIsFalse :
      pointwiseTailClosedHere ≡ false
    independentCoefficientClosedHere :
      Bool
    independentCoefficientClosedHereIsFalse :
      independentCoefficientClosedHere ≡ false

open Sprint91CoefficientBudgetLedger public

canonicalSprint91CoefficientBudgetLedger :
  Sprint91CoefficientBudgetLedger
canonicalSprint91CoefficientBudgetLedger =
  coefficientBudgetLedger
    canonicalLocalizedFluxIdentityImportedFromFixedKLP
    canonicalMovingKStarLocalizationBoundary
    canonicalAdjacentLeakageBudgetAvailable
    canonicalHighHighDominanceStillOpen
    canonicalIndependentCoefficientStillOpen
    true
    refl
    false
    refl
    false
    refl
    false
    refl

record NSSprint91LocalizedFluxIdentityAndCoefficientBudget : Setω where
  field
    sprint90Receipt :
      Sprint90.NSSprint90LocalEnstrophyDangerShellReductionReceipt
    sprint90ReductionBookkeepingClosed :
      Sprint90.localEnstrophyDangerShellReductionBookkeepingClosed ≡ true
    sprint90LocalizedFluxIdentityWasOpen :
      Sprint90.localizedEnstrophyFluxIdentityClosed ≡ false
    sprint90DangerDominanceStillOpen :
      Sprint90.dangerShellDissipationDominatesInfluxClosed ≡ false
    sprint90PointwiseTailStillOpen :
      Sprint90.pointwiseTailFromLocalDissipationClosed ≡ false
    sprint90IndependentCoefficientStillOpen :
      Sprint90.independentCoefficientBudgetClosed ≡ false
    sprint90NoClay :
      Sprint90.clayNavierStokesPromoted ≡ false

    fullIdentityReceipt :
      Full.NSTailFluxLPIdentityFullDerivationReceipt zero
    fullIdentityDerived :
      Full.lpIdentityDerivedHere fullIdentityReceipt ≡ true
    fullIdentityFixedK :
      Full.fixedKSelectedBeforeDifferentiation fullIdentityReceipt ≡ true
    fullIdentityMovingCutoffAbsent :
      Full.movingCutoffTermAbsent fullIdentityReceipt ≡ true
    fullIdentityNoClay :
      Full.clayNavierStokesPromoted fullIdentityReceipt ≡ false

    adjacentLeakageReceipt :
      Leak.NSAdjacentShellLeakageBoundReceipt zero
    adjacentLeakageBudgetConditionallyAvailable :
      Leak.edgeInfluxBoundConditionallyStated adjacentLeakageReceipt ≡ true
    adjacentLeakageNotUnconditional :
      Leak.leakageBoundUnconditionallyProved adjacentLeakageReceipt ≡ false
    adjacentLeakageHighHighBarrierRecorded :
      Leak.highHighThetaBarrierCrossedInDiagnostics adjacentLeakageReceipt
      ≡ true
    adjacentLeakageNoClay :
      Leak.clayNavierStokesPromoted adjacentLeakageReceipt ≡ false

    localizedFluxIdentityImport :
      LocalizedFluxIdentityImportedFromFixedKLP
    localizedFluxIdentityImportIsCanonical :
      localizedFluxIdentityImport
      ≡ canonicalLocalizedFluxIdentityImportedFromFixedKLP
    movingKStarBoundary :
      MovingKStarLocalizationBoundary
    movingKStarBoundaryIsCanonical :
      movingKStarBoundary ≡ canonicalMovingKStarLocalizationBoundary
    adjacentLeakageBudget :
      AdjacentLeakageBudgetAvailable
    adjacentLeakageBudgetIsCanonical :
      adjacentLeakageBudget ≡ canonicalAdjacentLeakageBudgetAvailable
    highHighDominance :
      HighHighDominanceStillOpen
    highHighDominanceIsCanonical :
      highHighDominance ≡ canonicalHighHighDominanceStillOpen
    independentCoefficient :
      IndependentCoefficientStillOpen
    independentCoefficientIsCanonical :
      independentCoefficient ≡ canonicalIndependentCoefficientStillOpen

    coefficientLedger :
      Sprint91CoefficientBudgetLedger
    coefficientLedgerIsCanonical :
      coefficientLedger ≡ canonicalSprint91CoefficientBudgetLedger
    closedBookkeeping :
      List Sprint91ClosedBookkeeping
    closedBookkeepingIsCanonical :
      closedBookkeeping ≡ canonicalSprint91ClosedBookkeeping
    openBoundaries :
      List Sprint91OpenBoundary
    openBoundariesAreCanonical :
      openBoundaries ≡ canonicalSprint91OpenBoundaries

    localizedEnstrophyFluxIdentityClosedIsTrue :
      localizedEnstrophyFluxIdentityClosed ≡ true
    dangerShellDissipationDominatesInfluxClosedIsFalse :
      dangerShellDissipationDominatesInfluxClosed ≡ false
    pointwiseTailFromLocalDissipationClosedIsFalse :
      pointwiseTailFromLocalDissipationClosed ≡ false
    independentCoefficientBudgetClosedIsFalse :
      independentCoefficientBudgetClosed ≡ false
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    identityImportStatement :
      String
    identityImportStatementIsCanonical :
      identityImportStatement ≡ sprint91IdentityImportStatement
    boundaryStatement :
      String
    boundaryStatementIsCanonical :
      boundaryStatement ≡ sprint91BoundaryStatement

open NSSprint91LocalizedFluxIdentityAndCoefficientBudget public

canonicalNSSprint91LocalizedFluxIdentityAndCoefficientBudget :
  NSSprint91LocalizedFluxIdentityAndCoefficientBudget
canonicalNSSprint91LocalizedFluxIdentityAndCoefficientBudget =
  record
    { sprint90Receipt =
        Sprint90.canonicalNSSprint90LocalEnstrophyDangerShellReductionReceipt
    ; sprint90ReductionBookkeepingClosed =
        refl
    ; sprint90LocalizedFluxIdentityWasOpen =
        refl
    ; sprint90DangerDominanceStillOpen =
        refl
    ; sprint90PointwiseTailStillOpen =
        refl
    ; sprint90IndependentCoefficientStillOpen =
        refl
    ; sprint90NoClay =
        refl
    ; fullIdentityReceipt =
        Full.canonicalNSTailFluxLPIdentityFullDerivationReceipt
    ; fullIdentityDerived =
        refl
    ; fullIdentityFixedK =
        refl
    ; fullIdentityMovingCutoffAbsent =
        refl
    ; fullIdentityNoClay =
        refl
    ; adjacentLeakageReceipt =
        Leak.canonicalNSAdjacentShellLeakageBoundReceipt
    ; adjacentLeakageBudgetConditionallyAvailable =
        refl
    ; adjacentLeakageNotUnconditional =
        refl
    ; adjacentLeakageHighHighBarrierRecorded =
        refl
    ; adjacentLeakageNoClay =
        refl
    ; localizedFluxIdentityImport =
        canonicalLocalizedFluxIdentityImportedFromFixedKLP
    ; localizedFluxIdentityImportIsCanonical =
        refl
    ; movingKStarBoundary =
        canonicalMovingKStarLocalizationBoundary
    ; movingKStarBoundaryIsCanonical =
        refl
    ; adjacentLeakageBudget =
        canonicalAdjacentLeakageBudgetAvailable
    ; adjacentLeakageBudgetIsCanonical =
        refl
    ; highHighDominance =
        canonicalHighHighDominanceStillOpen
    ; highHighDominanceIsCanonical =
        refl
    ; independentCoefficient =
        canonicalIndependentCoefficientStillOpen
    ; independentCoefficientIsCanonical =
        refl
    ; coefficientLedger =
        canonicalSprint91CoefficientBudgetLedger
    ; coefficientLedgerIsCanonical =
        refl
    ; closedBookkeeping =
        canonicalSprint91ClosedBookkeeping
    ; closedBookkeepingIsCanonical =
        refl
    ; openBoundaries =
        canonicalSprint91OpenBoundaries
    ; openBoundariesAreCanonical =
        refl
    ; localizedEnstrophyFluxIdentityClosedIsTrue =
        refl
    ; dangerShellDissipationDominatesInfluxClosedIsFalse =
        refl
    ; pointwiseTailFromLocalDissipationClosedIsFalse =
        refl
    ; independentCoefficientBudgetClosedIsFalse =
        refl
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; identityImportStatement =
        sprint91IdentityImportStatement
    ; identityImportStatementIsCanonical =
        refl
    ; boundaryStatement =
        sprint91BoundaryStatement
    ; boundaryStatementIsCanonical =
        refl
    }

canonicalSprint91Flags :
  (localizedEnstrophyFluxIdentityClosed ≡ true)
  × (dangerShellDissipationDominatesInfluxClosed ≡ false)
  × (pointwiseTailFromLocalDissipationClosed ≡ false)
  × (independentCoefficientBudgetClosed ≡ false)
  × (clayNavierStokesPromoted ≡ false)
canonicalSprint91Flags =
  refl , refl , refl , refl , refl
