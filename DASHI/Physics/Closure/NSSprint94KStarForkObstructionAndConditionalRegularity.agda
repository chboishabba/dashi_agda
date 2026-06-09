module DASHI.Physics.Closure.NSSprint94KStarForkObstructionAndConditionalRegularity where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSSprint93DominancePointwiseCoefficientLedger
  as Sprint93

------------------------------------------------------------------------
-- Sprint 94 K* fork obstruction and conditional regularity receipt.
--
-- Sprint 93 leaves the dominance / pointwise / independent-coefficient
-- residual gate open.  Sprint 94 records the fork outcome:
--
--   * the general-data gate is obstructed by the K* lower-bound /
--     small-data calculation;
--   * Option C is closed only as a conditional regularity criterion under
--     KStarLowerBoundHypothesis;
--   * Option A general-data Clay regularity and Option B blowup
--     construction remain open;
--   * Clay Navier-Stokes promotion remains false.

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

generalDataGateClosed : Bool
generalDataGateClosed = false

generalDataGateObstructedByKStarLowerBound : Bool
generalDataGateObstructedByKStarLowerBound = true

optionCConditionalRegularityCriterionClosed : Bool
optionCConditionalRegularityCriterionClosed = true

optionCConditionalCriterionClosed : Bool
optionCConditionalCriterionClosed = true

optionAGeneralDataClayRegularityClosed : Bool
optionAGeneralDataClayRegularityClosed = false

optionBBlowupConstructionClosed : Bool
optionBBlowupConstructionClosed = false

kStarForkObstructionClosed : Bool
kStarForkObstructionClosed = true

globalRegularityUnderKStarLowerBoundClosed : Bool
globalRegularityUnderKStarLowerBoundClosed = true

generalDataKStarLowerBoundClosed : Bool
generalDataKStarLowerBoundClosed = false

generalDataClayRegularityClosed : Bool
generalDataClayRegularityClosed = false

blowupConstructionClosed : Bool
blowupConstructionClosed = false

data Sprint94ForkOption : Set where
  optionAGeneralDataClayRegularity :
    Sprint94ForkOption
  optionBBlowupConstruction :
    Sprint94ForkOption
  optionCConditionalRegularityUnderKStarLowerBound :
    Sprint94ForkOption

OptionABlocked : Sprint94ForkOption
OptionABlocked =
  optionAGeneralDataClayRegularity

OptionABlockedGeneralDataRegularity : Sprint94ForkOption
OptionABlockedGeneralDataRegularity =
  optionAGeneralDataClayRegularity

OptionBOpen : Sprint94ForkOption
OptionBOpen =
  optionBBlowupConstruction

OptionBOpenBlowupConstruction : Sprint94ForkOption
OptionBOpenBlowupConstruction =
  optionBBlowupConstruction

OptionCConditional : Sprint94ForkOption
OptionCConditional =
  optionCConditionalRegularityUnderKStarLowerBound

OptionCConditionalRegularity : Sprint94ForkOption
OptionCConditionalRegularity =
  optionCConditionalRegularityUnderKStarLowerBound

canonicalSprint94ForkOptions : List Sprint94ForkOption
canonicalSprint94ForkOptions =
  optionAGeneralDataClayRegularity
  ∷ optionBBlowupConstruction
  ∷ optionCConditionalRegularityUnderKStarLowerBound
  ∷ []

data Sprint94ForkStatus : Set where
  remainsOpen :
    Sprint94ForkStatus
  closedAsConditionalCriterion :
    Sprint94ForkStatus

record Sprint94ForkLedgerEntry : Set where
  constructor forkLedgerEntry
  field
    option :
      Sprint94ForkOption
    status :
      Sprint94ForkStatus
    closed :
      Bool
    closedProof :
      closed ≡ closed
    note :
      String

open Sprint94ForkLedgerEntry public

optionAForkLedgerEntry : Sprint94ForkLedgerEntry
optionAForkLedgerEntry =
  forkLedgerEntry
    optionAGeneralDataClayRegularity
    remainsOpen
    false
    refl
    "Option A remains open: the K* lower-bound/small-data calculation obstructs general-data Clay regularity promotion."

optionBForkLedgerEntry : Sprint94ForkLedgerEntry
optionBForkLedgerEntry =
  forkLedgerEntry
    optionBBlowupConstruction
    remainsOpen
    false
    refl
    "Option B remains open: Sprint 94 records no blowup construction."

optionCForkLedgerEntry : Sprint94ForkLedgerEntry
optionCForkLedgerEntry =
  forkLedgerEntry
    optionCConditionalRegularityUnderKStarLowerBound
    closedAsConditionalCriterion
    true
    refl
    "Option C is closed only as a conditional regularity criterion under KStarLowerBoundHypothesis."

canonicalSprint94ForkLedger :
  List Sprint94ForkLedgerEntry
canonicalSprint94ForkLedger =
  optionAForkLedgerEntry
  ∷ optionBForkLedgerEntry
  ∷ optionCForkLedgerEntry
  ∷ []

record KStarLowerBoundHypothesis : Set where
  constructor kStarLowerBoundHypothesis
  field
    lowerBoundAvailable :
      Bool
    lowerBoundAvailableIsTrue :
      lowerBoundAvailable ≡ true
    smallDataCalculationRestrictsGeneralData :
      Bool
    smallDataCalculationRestrictsGeneralDataIsTrue :
      smallDataCalculationRestrictsGeneralData ≡ true
    sprint93ResidualGateStillOpen :
      Sprint93.dominanceWithPointwiseTailAndIndependentCoefficientClosed
      ≡ false
    sprint93NoClay :
      Sprint93.clayNavierStokesPromoted ≡ false

open KStarLowerBoundHypothesis public

canonicalKStarLowerBoundHypothesis :
  KStarLowerBoundHypothesis
canonicalKStarLowerBoundHypothesis =
  kStarLowerBoundHypothesis true refl true refl refl refl

data GeneralDataKStarLowerBoundObstruction : Set where
  generalDataKStarLowerBoundObstruction :
    GeneralDataKStarLowerBoundObstruction

canonicalGeneralDataKStarLowerBoundObstruction :
  GeneralDataKStarLowerBoundObstruction
canonicalGeneralDataKStarLowerBoundObstruction =
  generalDataKStarLowerBoundObstruction

record OptionCConditionalRegularityCriterion : Set where
  constructor optionCConditionalRegularityCriterion
  field
    hypothesis :
      KStarLowerBoundHypothesis
    criterionClosed :
      Bool
    criterionClosedIsTrue :
      criterionClosed ≡ true
    generalDataPromotion :
      Bool
    generalDataPromotionIsFalse :
      generalDataPromotion ≡ false
    clayPromotion :
      Bool
    clayPromotionIsFalse :
      clayPromotion ≡ false
    criterionStatement :
      String

open OptionCConditionalRegularityCriterion public

optionCConditionalRegularity :
  KStarLowerBoundHypothesis →
  OptionCConditionalRegularityCriterion
optionCConditionalRegularity hypothesis =
  optionCConditionalRegularityCriterion
    hypothesis
    true
    refl
    false
    refl
    false
    refl
    "Under KStarLowerBoundHypothesis, Option C is a closed conditional regularity criterion only; it does not promote general-data Clay regularity."

canonicalOptionCConditionalRegularityCriterion :
  OptionCConditionalRegularityCriterion
canonicalOptionCConditionalRegularityCriterion =
  optionCConditionalRegularity canonicalKStarLowerBoundHypothesis

GlobalRegularityUnderKStarLowerBound : Set
GlobalRegularityUnderKStarLowerBound =
  OptionCConditionalRegularityCriterion

data Sprint94ClosedBookkeeping : Set where
  sprint93DominancePointwiseCoefficientLedgerInherited :
    Sprint94ClosedBookkeeping
  kStarLowerBoundSmallDataObstructionRecorded :
    Sprint94ClosedBookkeeping
  optionCConditionalCriterionRecordedClosed :
    Sprint94ClosedBookkeeping
  clayPromotionRecordedFalse :
    Sprint94ClosedBookkeeping

canonicalSprint94ClosedBookkeeping :
  List Sprint94ClosedBookkeeping
canonicalSprint94ClosedBookkeeping =
  sprint93DominancePointwiseCoefficientLedgerInherited
  ∷ kStarLowerBoundSmallDataObstructionRecorded
  ∷ optionCConditionalCriterionRecordedClosed
  ∷ clayPromotionRecordedFalse
  ∷ []

data Sprint94OpenBoundary : Set where
  optionAGeneralDataClayRegularityOpen :
    Sprint94OpenBoundary
  optionBBlowupConstructionOpen :
    Sprint94OpenBoundary
  unconditionalGeneralDataRegularityOpen :
    Sprint94OpenBoundary
  clayPromotionOpen :
    Sprint94OpenBoundary

canonicalSprint94OpenBoundaries :
  List Sprint94OpenBoundary
canonicalSprint94OpenBoundaries =
  optionAGeneralDataClayRegularityOpen
  ∷ optionBBlowupConstructionOpen
  ∷ unconditionalGeneralDataRegularityOpen
  ∷ clayPromotionOpen
  ∷ []

sprint94ObstructionStatement : String
sprint94ObstructionStatement =
  "Sprint 94 records the general-data gate as obstructed by the K* lower-bound/small-data calculation."

sprint94ConditionalRegularityStatement : String
sprint94ConditionalRegularityStatement =
  "Option C is closed as a conditional regularity criterion under KStarLowerBoundHypothesis; Option A general-data Clay regularity and Option B blowup construction remain open."

record Sprint94KStarForkLedger : Set where
  constructor kStarForkLedger
  field
    forkOptions :
      List Sprint94ForkOption
    forkOptionsAreCanonical :
      forkOptions ≡ canonicalSprint94ForkOptions
    forkLedger :
      List Sprint94ForkLedgerEntry
    forkLedgerIsCanonical :
      forkLedger ≡ canonicalSprint94ForkLedger
    closedBookkeeping :
      List Sprint94ClosedBookkeeping
    closedBookkeepingIsCanonical :
      closedBookkeeping ≡ canonicalSprint94ClosedBookkeeping
    openBoundaries :
      List Sprint94OpenBoundary
    openBoundariesAreCanonical :
      openBoundaries ≡ canonicalSprint94OpenBoundaries
    optionCCriterion :
      OptionCConditionalRegularityCriterion
    optionCCriterionIsCanonical :
      optionCCriterion ≡ canonicalOptionCConditionalRegularityCriterion
    generalDataObstructed :
      Bool
    generalDataObstructedIsTrue :
      generalDataObstructed ≡ true
    generalDataGateClosedHere :
      Bool
    generalDataGateClosedHereIsFalse :
      generalDataGateClosedHere ≡ false
    optionCClosedHere :
      Bool
    optionCClosedHereIsTrue :
      optionCClosedHere ≡ true
    optionAClosedHere :
      Bool
    optionAClosedHereIsFalse :
      optionAClosedHere ≡ false
    optionBClosedHere :
      Bool
    optionBClosedHereIsFalse :
      optionBClosedHere ≡ false
    clayPromotionClosedHere :
      Bool
    clayPromotionClosedHereIsFalse :
      clayPromotionClosedHere ≡ false

open Sprint94KStarForkLedger public

canonicalSprint94KStarForkLedger :
  Sprint94KStarForkLedger
canonicalSprint94KStarForkLedger =
  kStarForkLedger
    canonicalSprint94ForkOptions
    refl
    canonicalSprint94ForkLedger
    refl
    canonicalSprint94ClosedBookkeeping
    refl
    canonicalSprint94OpenBoundaries
    refl
    canonicalOptionCConditionalRegularityCriterion
    refl
    true
    refl
    false
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl

record NSSprint94KStarForkObstructionAndConditionalRegularity : Setω where
  field
    sprint93Receipt :
      Sprint93.NSSprint93DominancePointwiseCoefficientLedger
    sprint93BookkeepingInherited :
      Sprint93.sprint92BookkeepingInheritedClosed ≡ true
    sprint93ResidualGateStillOpen :
      Sprint93.dominanceWithPointwiseTailAndIndependentCoefficientClosed
      ≡ false
    sprint93DangerDominanceStillOpen :
      Sprint93.dangerShellDissipationDominatesInfluxClosed ≡ false
    sprint93PointwiseTailStillOpen :
      Sprint93.pointwiseTailFromLocalDissipationClosed ≡ false
    sprint93IndependentCoefficientStillOpen :
      Sprint93.independentCoefficientBudgetClosed ≡ false
    sprint93NoClay :
      Sprint93.clayNavierStokesPromoted ≡ false

    kStarHypothesis :
      KStarLowerBoundHypothesis
    kStarHypothesisIsCanonical :
      kStarHypothesis ≡ canonicalKStarLowerBoundHypothesis
    optionCCriterion :
      OptionCConditionalRegularityCriterion
    optionCCriterionIsCanonical :
      optionCCriterion ≡ canonicalOptionCConditionalRegularityCriterion
    sprint94ForkLedger :
      Sprint94KStarForkLedger
    sprint94ForkLedgerIsCanonical :
      sprint94ForkLedger ≡ canonicalSprint94KStarForkLedger
    closedBookkeeping :
      List Sprint94ClosedBookkeeping
    closedBookkeepingIsCanonical :
      closedBookkeeping ≡ canonicalSprint94ClosedBookkeeping
    openBoundaries :
      List Sprint94OpenBoundary
    openBoundariesAreCanonical :
      openBoundaries ≡ canonicalSprint94OpenBoundaries

    generalDataGateClosedIsFalse :
      generalDataGateClosed ≡ false
    generalDataGateObstructedByKStarLowerBoundIsTrue :
      generalDataGateObstructedByKStarLowerBound ≡ true
    optionCConditionalRegularityCriterionClosedIsTrue :
      optionCConditionalRegularityCriterionClosed ≡ true
    optionAGeneralDataClayRegularityClosedIsFalse :
      optionAGeneralDataClayRegularityClosed ≡ false
    optionBBlowupConstructionClosedIsFalse :
      optionBBlowupConstructionClosed ≡ false
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    obstructionStatement :
      String
    obstructionStatementIsCanonical :
      obstructionStatement ≡ sprint94ObstructionStatement
    conditionalRegularityStatement :
      String
    conditionalRegularityStatementIsCanonical :
      conditionalRegularityStatement
      ≡ sprint94ConditionalRegularityStatement

open NSSprint94KStarForkObstructionAndConditionalRegularity public

canonicalNSSprint94KStarForkObstructionAndConditionalRegularity :
  NSSprint94KStarForkObstructionAndConditionalRegularity
canonicalNSSprint94KStarForkObstructionAndConditionalRegularity =
  record
    { sprint93Receipt =
        Sprint93.canonicalNSSprint93DominancePointwiseCoefficientLedger
    ; sprint93BookkeepingInherited =
        refl
    ; sprint93ResidualGateStillOpen =
        refl
    ; sprint93DangerDominanceStillOpen =
        refl
    ; sprint93PointwiseTailStillOpen =
        refl
    ; sprint93IndependentCoefficientStillOpen =
        refl
    ; sprint93NoClay =
        refl
    ; kStarHypothesis =
        canonicalKStarLowerBoundHypothesis
    ; kStarHypothesisIsCanonical =
        refl
    ; optionCCriterion =
        canonicalOptionCConditionalRegularityCriterion
    ; optionCCriterionIsCanonical =
        refl
    ; sprint94ForkLedger =
        canonicalSprint94KStarForkLedger
    ; sprint94ForkLedgerIsCanonical =
        refl
    ; closedBookkeeping =
        canonicalSprint94ClosedBookkeeping
    ; closedBookkeepingIsCanonical =
        refl
    ; openBoundaries =
        canonicalSprint94OpenBoundaries
    ; openBoundariesAreCanonical =
        refl
    ; generalDataGateClosedIsFalse =
        refl
    ; generalDataGateObstructedByKStarLowerBoundIsTrue =
        refl
    ; optionCConditionalRegularityCriterionClosedIsTrue =
        refl
    ; optionAGeneralDataClayRegularityClosedIsFalse =
        refl
    ; optionBBlowupConstructionClosedIsFalse =
        refl
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; obstructionStatement =
        sprint94ObstructionStatement
    ; obstructionStatementIsCanonical =
        refl
    ; conditionalRegularityStatement =
        sprint94ConditionalRegularityStatement
    ; conditionalRegularityStatementIsCanonical =
        refl
    }

canonicalNSSprint94KStarForkObstructionReceipt :
  NSSprint94KStarForkObstructionAndConditionalRegularity
canonicalNSSprint94KStarForkObstructionReceipt =
  canonicalNSSprint94KStarForkObstructionAndConditionalRegularity

canonicalSprint94Flags :
  (generalDataGateClosed ≡ false)
  × (generalDataGateObstructedByKStarLowerBound ≡ true)
  × (optionCConditionalRegularityCriterionClosed ≡ true)
  × (optionAGeneralDataClayRegularityClosed ≡ false)
  × (optionBBlowupConstructionClosed ≡ false)
  × (clayNavierStokesPromoted ≡ false)
canonicalSprint94Flags =
  refl , refl , refl , refl , refl , refl
