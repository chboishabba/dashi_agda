module DASHI.Computation.HistoricalJacquardMechanicalInterpreterExact where

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)
open import Data.List using (reverse)

import DASHI.Computation.JacquardOperationalSemanticsExact as Jacquard

------------------------------------------------------------------------
-- HISTORICAL SINGLE-LIFT JACQUARD MECHANICAL INTERPRETER
--
-- This models the actual control transduction of a punched-card Jacquard head:
--
-- card hole/blank
--   -> needle passes/is pressed
--   -> hook remains aligned/is displaced
--   -> griffe catches/misses hook
--   -> harness/heddle raises/stays down
--   -> shed
--   -> weft insertion
--   -> beat-up
--   -> card advance.
--
-- It deliberately does not claim a calibrated dynamics model of yarn tension,
-- inertia, shuttle velocity, loom geometry, wear or breakage.
------------------------------------------------------------------------

record PunchedCard (n : Nat) : Set where
  constructor punched-card
  field
    holeAt : Fin n → Bool

open PunchedCard public

CardChain : Nat → Set
CardChain n = List (PunchedCard n)

data NeedleState : Set where
  needlePasses : NeedleState
  needlePressed : NeedleState

data HookState : Set where
  hookAligned : HookState
  hookDisplaced : HookState

data GriffeContact : Set where
  griffeCatches : GriffeContact
  griffeMisses : GriffeContact

data HarnessState : Set where
  warpRaised : HarnessState
  warpDown : HarnessState

NeedleField : Nat → Set
NeedleField n = Fin n → NeedleState

HookField : Nat → Set
HookField n = Fin n → HookState

GriffeField : Nat → Set
GriffeField n = Fin n → GriffeContact

HarnessField : Nat → Set
HarnessField n = Fin n → HarnessState

readNeedle : Bool → NeedleState
readNeedle true = needlePasses
readNeedle false = needlePressed

selectHook : NeedleState → HookState
selectHook needlePasses = hookAligned
selectHook needlePressed = hookDisplaced

engageGriffe : HookState → GriffeContact
engageGriffe hookAligned = griffeCatches
engageGriffe hookDisplaced = griffeMisses

liftHarness : GriffeContact → HarnessState
liftHarness griffeCatches = warpRaised
liftHarness griffeMisses = warpDown

readCard : {n : Nat} → PunchedCard n → NeedleField n
readCard card warp = readNeedle (holeAt card warp)

hooksFromNeedles : {n : Nat} → NeedleField n → HookField n
hooksFromNeedles needles warp = selectHook (needles warp)

griffeFromHooks : {n : Nat} → HookField n → GriffeField n
griffeFromHooks hooks warp = engageGriffe (hooks warp)

harnessFromGriffe : {n : Nat} → GriffeField n → HarnessField n
harnessFromGriffe contacts warp = liftHarness (contacts warp)

harnessFromCard : {n : Nat} → PunchedCard n → HarnessField n
harnessFromCard card =
  harnessFromGriffe (griffeFromHooks (hooksFromNeedles (readCard card)))

lifted : HarnessState → Bool
lifted warpRaised = true
lifted warpDown = false

liftMaskFromCard : {n : Nat} → PunchedCard n → Jacquard.LiftMask n
liftMaskFromCard card warp = lifted (harnessFromCard card warp)

cardHoleControlsLift :
  {n : Nat} →
  (card : PunchedCard n) →
  (warp : Fin n) →
  liftMaskFromCard card warp ≡ holeAt card warp
cardHoleControlsLift card warp with holeAt card warp
... | true = refl
... | false = refl

crossingRowFromCard :
  {n : Nat} → PunchedCard n → Jacquard.CrossingRow n
crossingRowFromCard card = Jacquard.weaveRow (liftMaskFromCard card)

------------------------------------------------------------------------
-- One complete mechanical pick cycle.
------------------------------------------------------------------------

data PickPhase : Set where
  cardPresented : PickPhase
  needlesRead : PickPhase
  hooksSelected : PickPhase
  griffeRaised : PickPhase
  shedFormed : PickPhase
  weftInserted : PickPhase
  beatenUp : PickPhase
  cardAdvanced : PickPhase

record PickCycle (n : Nat) : Set where
  constructor pick-cycle
  field
    card : PunchedCard n
    needles : NeedleField n
    hooks : HookField n
    griffe : GriffeField n
    harness : HarnessField n
    shedMask : Jacquard.LiftMask n
    wovenRow : Jacquard.CrossingRow n

    needlesAreCardReading : needles ≡ readCard card
    hooksAreNeedleSelection : hooks ≡ hooksFromNeedles needles
    griffeIsHookSelection : griffe ≡ griffeFromHooks hooks
    harnessIsGriffeLift : harness ≡ harnessFromGriffe griffe
    shedIsHarnessProjection :
      (warp : Fin n) → shedMask warp ≡ lifted (harness warp)
    rowIsShedExecution : wovenRow ≡ Jacquard.weaveRow shedMask

open PickCycle public

executePick : {n : Nat} → PunchedCard n → PickCycle n
executePick card =
  pick-cycle
    card
    (readCard card)
    (hooksFromNeedles (readCard card))
    (griffeFromHooks (hooksFromNeedles (readCard card)))
    (harnessFromGriffe
      (griffeFromHooks (hooksFromNeedles (readCard card))))
    (liftMaskFromCard card)
    (crossingRowFromCard card)
    refl refl refl refl
    (λ warp → refl)
    refl

------------------------------------------------------------------------
-- Card-chain interpreter.
------------------------------------------------------------------------

record MechanicalLoomState (n : Nat) : Set where
  constructor mechanical-loom-state
  field
    pickTime : Nat
    unreadCards : CardChain n
    consumedCardsReverse : CardChain n
    completedCyclesReverse : List (PickCycle n)
    wovenRowsReverse : Jacquard.WovenRows n

open MechanicalLoomState public

initialMechanicalState :
  {n : Nat} → CardChain n → MechanicalLoomState n
initialMechanicalState cards =
  mechanical-loom-state 0 cards [] [] []

runMechanicalFrom :
  {n : Nat} →
  Nat →
  CardChain n →
  CardChain n →
  List (PickCycle n) →
  Jacquard.WovenRows n →
  MechanicalLoomState n
runMechanicalFrom time [] consumed cycles rows =
  mechanical-loom-state time [] consumed cycles rows
runMechanicalFrom time (card ∷ cards) consumed cycles rows =
  runMechanicalFrom
    (suc time)
    cards
    (card ∷ consumed)
    (executePick card ∷ cycles)
    (wovenRow (executePick card) ∷ rows)

runMechanical :
  {n : Nat} → CardChain n → MechanicalLoomState n
runMechanical cards = runMechanicalFrom 0 cards [] [] []

producedRows :
  {n : Nat} → MechanicalLoomState n → Jacquard.WovenRows n
producedRows state = reverse (wovenRowsReverse state)

consumedCards :
  {n : Nat} → MechanicalLoomState n → CardChain n
consumedCards state = reverse (consumedCardsReverse state)

completedCycles :
  {n : Nat} → MechanicalLoomState n → List (PickCycle n)
completedCycles state = reverse (completedCyclesReverse state)

interpretCards : {n : Nat} → CardChain n → Jacquard.WovenRows n
interpretCards [] = []
interpretCards (card ∷ cards) =
  crossingRowFromCard card ∷ interpretCards cards

------------------------------------------------------------------------
-- Adapter to the existing Jacquard program representation.
------------------------------------------------------------------------

cardFromInstruction :
  {n : Nat} → Jacquard.JacquardInstruction n → PunchedCard n
cardFromInstruction (Jacquard.liftMask mask) = punched-card mask

programToCards :
  {n : Nat} → Jacquard.JacquardProgram n → CardChain n
programToCards [] = []
programToCards (instruction ∷ program) =
  cardFromInstruction instruction ∷ programToCards program

programCardsExecuteCanonically :
  {n : Nat} →
  (program : Jacquard.JacquardProgram n) →
  interpretCards (programToCards program)
  ≡ Jacquard.executeProgram program
programCardsExecuteCanonically [] = refl
programCardsExecuteCanonically (Jacquard.liftMask mask ∷ program)
  rewrite programCardsExecuteCanonically program = refl

------------------------------------------------------------------------
-- Hard abstraction boundaries.
------------------------------------------------------------------------

data CardHoleDirectlyIsWarpMotion : Set where
data MechanicalInterpreterIncludesMaterialDynamics : Set where
data ShedFormationAloneCompletesFabric : Set where

cardHoleIsNotDirectWarpMotion : CardHoleDirectlyIsWarpMotion → ⊥
cardHoleIsNotDirectWarpMotion ()

mechanismIsNotCalibratedMaterialDynamics :
  MechanicalInterpreterIncludesMaterialDynamics → ⊥
mechanismIsNotCalibratedMaterialDynamics ()

shedFormationAloneDoesNotCompleteFabric :
  ShedFormationAloneCompletesFabric → ⊥
shedFormationAloneDoesNotCompleteFabric ()

record HistoricalJacquardMechanicalBoundary : Set where
  constructor historical-jacquard-mechanical-boundary
  field
    cardHolesAreReadByNeedles : Bool
    needlesSelectHooks : Bool
    hooksControlGriffeEngagement : Bool
    griffeControlsHarnessLift : Bool
    harnessLiftFormsShed : Bool
    oneCardRunsOnePickCycle : Bool
    pickCycleIncludesWeftInsertionAndBeatUpStages : Bool
    cardChainAdvancesAcrossPicks : Bool
    executionAgreesWithCanonicalJacquardRows : Bool
    calibratedYarnMechanicsIncluded : Bool

canonicalHistoricalJacquardMechanicalBoundary :
  HistoricalJacquardMechanicalBoundary
canonicalHistoricalJacquardMechanicalBoundary =
  historical-jacquard-mechanical-boundary
    true true true true true true true true true false
