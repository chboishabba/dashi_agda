module DASHI.Physics.Closure.NSSprint92MovingKStarLocalizationBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSSprint91LocalizedFluxIdentityAndCoefficientBudget
  as Sprint91
import DASHI.Physics.Closure.NSTailFluxLPIdentityFullDerivationReceipt
  as Full

------------------------------------------------------------------------
-- Sprint 92 moving K*(t) localization boundary receipt.
--
-- Sprint 91 closes only the localized fixed-K flux identity bookkeeping.
-- Sprint 92 records the next boundary honestly: at a fixed danger time one
-- may freeze K*(t) and reuse the Sprint 91 fixed-K identity ledger, but this
-- does not differentiate a moving cutoff and therefore does not close the
-- moving-in-time boundary term, danger-shell dominance, pointwise tail
-- extraction, high-high dominance, independent coefficient budgeting, or
-- Clay Navier-Stokes promotion.

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

fixedDangerTimeFrozenKBookkeepingClosed : Bool
fixedDangerTimeFrozenKBookkeepingClosed = true

movingInTimeKStarLocalizationBoundaryClosed : Bool
movingInTimeKStarLocalizationBoundaryClosed = false

dangerShellDissipationDominatesInfluxClosed : Bool
dangerShellDissipationDominatesInfluxClosed = false

pointwiseTailFromLocalDissipationClosed : Bool
pointwiseTailFromLocalDissipationClosed = false

highHighDominanceClosed : Bool
highHighDominanceClosed = false

independentCoefficientBudgetClosed : Bool
independentCoefficientBudgetClosed = false

data Sprint92FrozenKJustification : Set where
  fixedDangerTimeUsesSprint91FixedKIdentity :
    Sprint92FrozenKJustification

canonicalSprint92FrozenKJustification :
  Sprint92FrozenKJustification
canonicalSprint92FrozenKJustification =
  fixedDangerTimeUsesSprint91FixedKIdentity

data Sprint92MovingBoundary : Set where
  movingKStarTimeDerivativeNotProducedByFrozenKIdentity :
    Sprint92MovingBoundary

canonicalSprint92MovingBoundary :
  Sprint92MovingBoundary
canonicalSprint92MovingBoundary =
  movingKStarTimeDerivativeNotProducedByFrozenKIdentity

data Sprint92OpenGate : Set where
  movingInTimeBoundaryOpen :
    Sprint92OpenGate
  dangerShellDominanceOpen :
    Sprint92OpenGate
  pointwiseTailExtractionOpen :
    Sprint92OpenGate
  highHighDominanceOpen :
    Sprint92OpenGate
  independentCoefficientOpen :
    Sprint92OpenGate
  clayPromotionOpen :
    Sprint92OpenGate

canonicalSprint92OpenGates : List Sprint92OpenGate
canonicalSprint92OpenGates =
  movingInTimeBoundaryOpen
  ∷ dangerShellDominanceOpen
  ∷ pointwiseTailExtractionOpen
  ∷ highHighDominanceOpen
  ∷ independentCoefficientOpen
  ∷ clayPromotionOpen
  ∷ []

data Sprint92ClosedBookkeeping : Set where
  sprint91ReceiptInherited :
    Sprint92ClosedBookkeeping
  localizedFixedKFluxIdentityInherited :
    Sprint92ClosedBookkeeping
  fixedDangerTimeKStarFrozenForBookkeeping :
    Sprint92ClosedBookkeeping
  movingCutoffAbsencePreservedAsBoundary :
    Sprint92ClosedBookkeeping

canonicalSprint92ClosedBookkeeping :
  List Sprint92ClosedBookkeeping
canonicalSprint92ClosedBookkeeping =
  sprint91ReceiptInherited
  ∷ localizedFixedKFluxIdentityInherited
  ∷ fixedDangerTimeKStarFrozenForBookkeeping
  ∷ movingCutoffAbsencePreservedAsBoundary
  ∷ []

sprint92FrozenKStatement : String
sprint92FrozenKStatement =
  "Sprint 92 closes only fixed-danger-time/frozen-K bookkeeping by reusing Sprint 91's fixed-K localized flux identity ledger."

sprint92BoundaryStatement : String
sprint92BoundaryStatement =
  "The moving K*(t) localization boundary remains open: Sprint 91's fixed-K identity has movingCutoffTermAbsent=true and supplies no time-differentiated K*(t) boundary, danger-shell dominance, pointwise tail, high-high dominance, independent coefficient, or Clay promotion."

record Sprint92MovingKStarBoundaryLedger : Set where
  constructor movingKStarBoundaryLedger
  field
    frozenKJustification :
      Sprint92FrozenKJustification
    movingBoundary :
      Sprint92MovingBoundary
    closedBookkeeping :
      List Sprint92ClosedBookkeeping
    openGates :
      List Sprint92OpenGate
    fixedDangerTimeFrozenKBookkeepingClosedHere :
      Bool
    fixedDangerTimeFrozenKBookkeepingClosedHereIsTrue :
      fixedDangerTimeFrozenKBookkeepingClosedHere ≡ true
    movingInTimeBoundaryClosedHere :
      Bool
    movingInTimeBoundaryClosedHereIsFalse :
      movingInTimeBoundaryClosedHere ≡ false
    dangerShellDominanceClosedHere :
      Bool
    dangerShellDominanceClosedHereIsFalse :
      dangerShellDominanceClosedHere ≡ false
    pointwiseTailClosedHere :
      Bool
    pointwiseTailClosedHereIsFalse :
      pointwiseTailClosedHere ≡ false
    highHighDominanceClosedHere :
      Bool
    highHighDominanceClosedHereIsFalse :
      highHighDominanceClosedHere ≡ false
    independentCoefficientClosedHere :
      Bool
    independentCoefficientClosedHereIsFalse :
      independentCoefficientClosedHere ≡ false
    clayPromotionClosedHere :
      Bool
    clayPromotionClosedHereIsFalse :
      clayPromotionClosedHere ≡ false

open Sprint92MovingKStarBoundaryLedger public

canonicalSprint92MovingKStarBoundaryLedger :
  Sprint92MovingKStarBoundaryLedger
canonicalSprint92MovingKStarBoundaryLedger =
  movingKStarBoundaryLedger
    canonicalSprint92FrozenKJustification
    canonicalSprint92MovingBoundary
    canonicalSprint92ClosedBookkeeping
    canonicalSprint92OpenGates
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl

record NSSprint92MovingKStarLocalizationBoundary : Setω where
  field
    sprint91Receipt :
      Sprint91.NSSprint91LocalizedFluxIdentityAndCoefficientBudget
    sprint91LocalizedFluxIdentityClosed :
      Sprint91.localizedEnstrophyFluxIdentityClosed ≡ true
    sprint91FixedKIdentityImported :
      Sprint91.localizedFluxIdentityImport sprint91Receipt
      ≡ Sprint91.canonicalLocalizedFluxIdentityImportedFromFixedKLP
    sprint91MovingBoundaryStillCanonicalOpen :
      Sprint91.movingKStarBoundary sprint91Receipt
      ≡ Sprint91.canonicalMovingKStarLocalizationBoundary
    sprint91FullIdentityMovingCutoffAbsent :
      Full.movingCutoffTermAbsent (Sprint91.fullIdentityReceipt sprint91Receipt)
      ≡ true
    sprint91DangerDominanceStillOpen :
      Sprint91.dangerShellDissipationDominatesInfluxClosed ≡ false
    sprint91PointwiseTailStillOpen :
      Sprint91.pointwiseTailFromLocalDissipationClosed ≡ false
    sprint91IndependentCoefficientStillOpen :
      Sprint91.independentCoefficientBudgetClosed ≡ false
    sprint91NoClay :
      Sprint91.clayNavierStokesPromoted ≡ false

    frozenKJustification :
      Sprint92FrozenKJustification
    frozenKJustificationIsCanonical :
      frozenKJustification ≡ canonicalSprint92FrozenKJustification
    movingBoundary :
      Sprint92MovingBoundary
    movingBoundaryIsCanonical :
      movingBoundary ≡ canonicalSprint92MovingBoundary
    boundaryLedger :
      Sprint92MovingKStarBoundaryLedger
    boundaryLedgerIsCanonical :
      boundaryLedger ≡ canonicalSprint92MovingKStarBoundaryLedger
    closedBookkeeping :
      List Sprint92ClosedBookkeeping
    closedBookkeepingIsCanonical :
      closedBookkeeping ≡ canonicalSprint92ClosedBookkeeping
    openGates :
      List Sprint92OpenGate
    openGatesAreCanonical :
      openGates ≡ canonicalSprint92OpenGates

    fixedDangerTimeFrozenKBookkeepingClosedIsTrue :
      fixedDangerTimeFrozenKBookkeepingClosed ≡ true
    movingInTimeKStarLocalizationBoundaryClosedIsFalse :
      movingInTimeKStarLocalizationBoundaryClosed ≡ false
    dangerShellDissipationDominatesInfluxClosedIsFalse :
      dangerShellDissipationDominatesInfluxClosed ≡ false
    pointwiseTailFromLocalDissipationClosedIsFalse :
      pointwiseTailFromLocalDissipationClosed ≡ false
    highHighDominanceClosedIsFalse :
      highHighDominanceClosed ≡ false
    independentCoefficientBudgetClosedIsFalse :
      independentCoefficientBudgetClosed ≡ false
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    frozenKStatement :
      String
    frozenKStatementIsCanonical :
      frozenKStatement ≡ sprint92FrozenKStatement
    boundaryStatement :
      String
    boundaryStatementIsCanonical :
      boundaryStatement ≡ sprint92BoundaryStatement

open NSSprint92MovingKStarLocalizationBoundary public

canonicalNSSprint92MovingKStarLocalizationBoundary :
  NSSprint92MovingKStarLocalizationBoundary
canonicalNSSprint92MovingKStarLocalizationBoundary =
  record
    { sprint91Receipt =
        Sprint91.canonicalNSSprint91LocalizedFluxIdentityAndCoefficientBudget
    ; sprint91LocalizedFluxIdentityClosed =
        refl
    ; sprint91FixedKIdentityImported =
        refl
    ; sprint91MovingBoundaryStillCanonicalOpen =
        refl
    ; sprint91FullIdentityMovingCutoffAbsent =
        refl
    ; sprint91DangerDominanceStillOpen =
        refl
    ; sprint91PointwiseTailStillOpen =
        refl
    ; sprint91IndependentCoefficientStillOpen =
        refl
    ; sprint91NoClay =
        refl
    ; frozenKJustification =
        canonicalSprint92FrozenKJustification
    ; frozenKJustificationIsCanonical =
        refl
    ; movingBoundary =
        canonicalSprint92MovingBoundary
    ; movingBoundaryIsCanonical =
        refl
    ; boundaryLedger =
        canonicalSprint92MovingKStarBoundaryLedger
    ; boundaryLedgerIsCanonical =
        refl
    ; closedBookkeeping =
        canonicalSprint92ClosedBookkeeping
    ; closedBookkeepingIsCanonical =
        refl
    ; openGates =
        canonicalSprint92OpenGates
    ; openGatesAreCanonical =
        refl
    ; fixedDangerTimeFrozenKBookkeepingClosedIsTrue =
        refl
    ; movingInTimeKStarLocalizationBoundaryClosedIsFalse =
        refl
    ; dangerShellDissipationDominatesInfluxClosedIsFalse =
        refl
    ; pointwiseTailFromLocalDissipationClosedIsFalse =
        refl
    ; highHighDominanceClosedIsFalse =
        refl
    ; independentCoefficientBudgetClosedIsFalse =
        refl
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; frozenKStatement =
        sprint92FrozenKStatement
    ; frozenKStatementIsCanonical =
        refl
    ; boundaryStatement =
        sprint92BoundaryStatement
    ; boundaryStatementIsCanonical =
        refl
    }

canonicalSprint92Flags :
  (fixedDangerTimeFrozenKBookkeepingClosed ≡ true)
  × (movingInTimeKStarLocalizationBoundaryClosed ≡ false)
  × (dangerShellDissipationDominatesInfluxClosed ≡ false)
  × (pointwiseTailFromLocalDissipationClosed ≡ false)
  × (highHighDominanceClosed ≡ false)
  × (independentCoefficientBudgetClosed ≡ false)
  × (clayNavierStokesPromoted ≡ false)
canonicalSprint92Flags =
  refl , refl , refl , refl , refl , refl , refl
