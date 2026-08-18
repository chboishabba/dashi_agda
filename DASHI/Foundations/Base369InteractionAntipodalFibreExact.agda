module DASHI.Foundations.Base369InteractionAntipodalFibreExact where

------------------------------------------------------------------------
-- REPO-NATIVE CROSS-POLLINATION
--
-- Base369InteractionAppraisalCubeExact already owns the one-round carrier:
--
--   base interaction cube (27)
--   x participant-A appraisal cube (27)
--   x participant-B appraisal cube (27)
--   = 27^3 = 3^9 = 19683.
--
-- This module does not create another Ege/constraint carrier.  It equips those
-- three existing 27-state blocks with the strict antipodal action from
-- BalancedTernaryAntipodalOrbitExact and exposes the exact orientation-forgotten
-- fibres.  Blockwise orientation loss is distinct from global inversion and
-- from scalar aggregation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ; +_; -[1+_]) renaming (_+_ to _+ℤ_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hyper
import DASHI.Foundations.Base369AddressSymmetryAndBranchGeometryExact as Branch
import DASHI.Foundations.Base369InteractionAppraisalCubeExact as Cube
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit
import DASHI.Foundations.SSPTritCarrier as SSP

interactionTriple : Cube.InteractionCube → Orbit.TritTriple
interactionTriple (Cube.interactionCube a b c) = Branch.triple a b c

appraisalTriple : Cube.ParticipantAppraisal → Orbit.TritTriple
appraisalTriple (Cube.participantAppraisal feeling preferred synthesis) =
  Branch.triple feeling preferred synthesis

invertInteraction : Cube.InteractionCube → Cube.InteractionCube
invertInteraction (Cube.interactionCube a b c) =
  Cube.interactionCube
    (Orbit.strictAntipode a)
    (Orbit.strictAntipode b)
    (Orbit.strictAntipode c)

invertAppraisal : Cube.ParticipantAppraisal → Cube.ParticipantAppraisal
invertAppraisal (Cube.participantAppraisal a b c) =
  Cube.participantAppraisal
    (Orbit.strictAntipode a)
    (Orbit.strictAntipode b)
    (Orbit.strictAntipode c)

flipInteractionBlock : Cube.OneRoundInteractionState → Cube.OneRoundInteractionState
flipInteractionBlock (Cube.oneRoundInteractionState interaction fibre) =
  Cube.oneRoundInteractionState (invertInteraction interaction) fibre

flipAppraisalABlock : Cube.OneRoundInteractionState → Cube.OneRoundInteractionState
flipAppraisalABlock
  (Cube.oneRoundInteractionState interaction
    (Cube.appraisalFibre appraisalA appraisalB)) =
  Cube.oneRoundInteractionState interaction
    (Cube.appraisalFibre (invertAppraisal appraisalA) appraisalB)

flipAppraisalBBlock : Cube.OneRoundInteractionState → Cube.OneRoundInteractionState
flipAppraisalBBlock
  (Cube.oneRoundInteractionState interaction
    (Cube.appraisalFibre appraisalA appraisalB)) =
  Cube.oneRoundInteractionState interaction
    (Cube.appraisalFibre appraisalA (invertAppraisal appraisalB))

globalAntipode : Cube.OneRoundInteractionState → Cube.OneRoundInteractionState
globalAntipode state =
  flipInteractionBlock (flipAppraisalABlock (flipAppraisalBBlock state))

------------------------------------------------------------------------
-- Blockwise orientation-forgotten base: 14 x 14 x 14 = 2744 classes.
------------------------------------------------------------------------

record BlockOrientationQuotient : Set where
  constructor blockOrientationQuotient
  field
    interactionClass : Orbit.AntipodalClass27
    appraisalAClass : Orbit.AntipodalClass27
    appraisalBClass : Orbit.AntipodalClass27

open BlockOrientationQuotient public

forgetBlockOrientation : Cube.OneRoundInteractionState → BlockOrientationQuotient
forgetBlockOrientation
  (Cube.oneRoundInteractionState interaction
    (Cube.appraisalFibre appraisalA appraisalB)) =
  blockOrientationQuotient
    (Orbit.classifyAntipodal27 (interactionTriple interaction))
    (Orbit.classifyAntipodal27 (appraisalTriple appraisalA))
    (Orbit.classifyAntipodal27 (appraisalTriple appraisalB))

forgetInteractionFlip :
  (state : Cube.OneRoundInteractionState) →
  forgetBlockOrientation (flipInteractionBlock state)
  ≡ forgetBlockOrientation state
forgetInteractionFlip
  (Cube.oneRoundInteractionState (Cube.interactionCube a b c) fibre)
  rewrite Orbit.classifyAntipodal27Invariant (Branch.triple a b c) = refl

forgetAppraisalAFlip :
  (state : Cube.OneRoundInteractionState) →
  forgetBlockOrientation (flipAppraisalABlock state)
  ≡ forgetBlockOrientation state
forgetAppraisalAFlip
  (Cube.oneRoundInteractionState interaction
    (Cube.appraisalFibre (Cube.participantAppraisal a b c) appraisalB))
  rewrite Orbit.classifyAntipodal27Invariant (Branch.triple a b c) = refl

forgetAppraisalBFlip :
  (state : Cube.OneRoundInteractionState) →
  forgetBlockOrientation (flipAppraisalBBlock state)
  ≡ forgetBlockOrientation state
forgetAppraisalBFlip
  (Cube.oneRoundInteractionState interaction
    (Cube.appraisalFibre appraisalA (Cube.participantAppraisal a b c)))
  rewrite Orbit.classifyAntipodal27Invariant (Branch.triple a b c) = refl

------------------------------------------------------------------------
-- Exact finite arithmetic of the repo-native 27^3 carrier and quotient.
------------------------------------------------------------------------

threeCubesAreThreePowerNine : Cube.threeCubesStateCount ≡ Hyper.ternaryLatticeCount 9
threeCubesAreThreePowerNine = refl

fineInteractionStateCount : Nat
fineInteractionStateCount = Cube.threeCubesStateCount

fineInteractionStateCountIs19683 : fineInteractionStateCount ≡ 19683
fineInteractionStateCountIs19683 = Cube.threeCubesStateCountIs19683

blockOrientationClassCount : Nat
blockOrientationClassCount = 14 * 14 * 14

blockOrientationClassCountIs2744 : blockOrientationClassCount ≡ 2744
blockOrientationClassCountIs2744 = refl

globalAntipodalClassCount : Nat
globalAntipodalClassCount = 9842

globalAntipodalCountEquation :
  fineInteractionStateCount ≡ 1 + 9841 * 2
globalAntipodalCountEquation = refl

globalAndBlockwiseQuotientCountsDiffer :
  globalAntipodalClassCount ≡ blockOrientationClassCount → ⊥
globalAndBlockwiseQuotientCountsDiffer ()

blockQuotientStratification :
  blockOrientationClassCount ≡ 1 + 39 + 507 + 2197
blockQuotientStratification = refl

fineFibreStratification :
  fineInteractionStateCount ≡ 1 + 78 + 2028 + 17576
fineFibreStratification = refl

allThreeNoncentralClassCount : Nat
allThreeNoncentralClassCount = 13 * 13 * 13

allThreeNoncentralClassCountIs2197 : allThreeNoncentralClassCount ≡ 2197
allThreeNoncentralClassCountIs2197 = refl

allThreeNoncentralOrientationFibreSize : Nat
allThreeNoncentralOrientationFibreSize = 2 * 2 * 2

allThreeNoncentralOrientationFibreSizeIsEight :
  allThreeNoncentralOrientationFibreSize ≡ 8
allThreeNoncentralOrientationFibreSizeIsEight = refl

------------------------------------------------------------------------
-- Literal eight-state orientation fibre over one all-noncentral base class.
------------------------------------------------------------------------

positiveInteraction : Cube.InteractionCube
positiveInteraction =
  Cube.interactionCube SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne

positiveAppraisal : Cube.ParticipantAppraisal
positiveAppraisal =
  Cube.participantAppraisal SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne

allPositiveRound : Cube.OneRoundInteractionState
allPositiveRound =
  Cube.oneRoundInteractionState positiveInteraction
    (Cube.appraisalFibre positiveAppraisal positiveAppraisal)

baseFlipped : Cube.OneRoundInteractionState
baseFlipped = flipInteractionBlock allPositiveRound

appraisalAFlipped : Cube.OneRoundInteractionState
appraisalAFlipped = flipAppraisalABlock allPositiveRound

appraisalBFlipped : Cube.OneRoundInteractionState
appraisalBFlipped = flipAppraisalBBlock allPositiveRound

baseAFlipped : Cube.OneRoundInteractionState
baseAFlipped = flipInteractionBlock appraisalAFlipped

baseBFlipped : Cube.OneRoundInteractionState
baseBFlipped = flipInteractionBlock appraisalBFlipped

appraisalsFlipped : Cube.OneRoundInteractionState
appraisalsFlipped = flipAppraisalABlock appraisalBFlipped

allBlocksFlipped : Cube.OneRoundInteractionState
allBlocksFlipped = globalAntipode allPositiveRound

allEightShareBlockOrientationQuotient :
  forgetBlockOrientation allPositiveRound ≡ forgetBlockOrientation baseFlipped
  × forgetBlockOrientation allPositiveRound ≡ forgetBlockOrientation appraisalAFlipped
  × forgetBlockOrientation allPositiveRound ≡ forgetBlockOrientation appraisalBFlipped
  × forgetBlockOrientation allPositiveRound ≡ forgetBlockOrientation baseAFlipped
  × forgetBlockOrientation allPositiveRound ≡ forgetBlockOrientation baseBFlipped
  × forgetBlockOrientation allPositiveRound ≡ forgetBlockOrientation appraisalsFlipped
  × forgetBlockOrientation allPositiveRound ≡ forgetBlockOrientation allBlocksFlipped
allEightShareBlockOrientationQuotient =
  refl , refl , refl , refl , refl , refl , refl

allPositiveDiffersFromBaseFlip : allPositiveRound ≡ baseFlipped → ⊥
allPositiveDiffersFromBaseFlip ()

------------------------------------------------------------------------
-- Aggregate cancellation: structural zero and internal opposition can share
-- the same scalar zero while remaining distinct fine states.
------------------------------------------------------------------------

sspInteger : SSP.SSPTrit → ℤ
sspInteger SSP.sspNegOne = -[1+ 0 ]
sspInteger SSP.sspZero = + 0
sspInteger SSP.sspPosOne = + 1

tripleSum : Orbit.TritTriple → ℤ
tripleSum (Branch.triple a b c) =
  sspInteger a +ℤ sspInteger b +ℤ sspInteger c

aggregateSum : Cube.OneRoundInteractionState → ℤ
aggregateSum
  (Cube.oneRoundInteractionState interaction
    (Cube.appraisalFibre appraisalA appraisalB)) =
  tripleSum (interactionTriple interaction)
  +ℤ tripleSum (appraisalTriple appraisalA)
  +ℤ tripleSum (appraisalTriple appraisalB)

allPositiveAggregatesToNine : aggregateSum allPositiveRound ≡ + 9
allPositiveAggregatesToNine = refl

baseFlipAggregatesToThree : aggregateSum baseFlipped ≡ + 3
baseFlipAggregatesToThree = refl

nineIsNotThree : (+ 9 : ℤ) ≡ + 3 → ⊥
nineIsNotThree ()

blockOrientationCollisionSeparatedByAggregate :
  forgetBlockOrientation allPositiveRound ≡ forgetBlockOrientation baseFlipped
  × (aggregateSum allPositiveRound ≡ aggregateSum baseFlipped → ⊥)
blockOrientationCollisionSeparatedByAggregate =
  refl , (λ aggregateEquality →
    nineIsNotThree
      (trans (sym allPositiveAggregatesToNine)
        (trans aggregateEquality baseFlipAggregatesToThree)))

zeroInteraction : Cube.InteractionCube
zeroInteraction = Cube.interactionCube SSP.sspZero SSP.sspZero SSP.sspZero

zeroAppraisal : Cube.ParticipantAppraisal
zeroAppraisal = Cube.participantAppraisal SSP.sspZero SSP.sspZero SSP.sspZero

structuralZeroRound : Cube.OneRoundInteractionState
structuralZeroRound =
  Cube.oneRoundInteractionState zeroInteraction
    (Cube.appraisalFibre zeroAppraisal zeroAppraisal)

cancelledInteraction : Cube.InteractionCube
cancelledInteraction =
  Cube.interactionCube SSP.sspPosOne SSP.sspNegOne SSP.sspZero

cancellationZeroRound : Cube.OneRoundInteractionState
cancellationZeroRound =
  Cube.oneRoundInteractionState cancelledInteraction
    (Cube.appraisalFibre zeroAppraisal zeroAppraisal)

structuralZeroAggregatesToZero : aggregateSum structuralZeroRound ≡ + 0
structuralZeroAggregatesToZero = refl

cancellationAlsoAggregatesToZero : aggregateSum cancellationZeroRound ≡ + 0
cancellationAlsoAggregatesToZero = refl

structuralZeroIsNotCancellationState : structuralZeroRound ≡ cancellationZeroRound → ⊥
structuralZeroIsNotCancellationState ()

structuralZeroBlockClass :
  forgetBlockOrientation structuralZeroRound
  ≡ blockOrientationQuotient Orbit.centre27 Orbit.centre27 Orbit.centre27
structuralZeroBlockClass = refl

cancellationBlockClass :
  forgetBlockOrientation cancellationZeroRound
  ≡ blockOrientationQuotient
      (Orbit.firstPositive27 SSP.sspNegOne SSP.sspZero)
      Orbit.centre27
      Orbit.centre27
cancellationBlockClass = refl

centreBlockClassIsNotCancellationClass :
  blockOrientationQuotient Orbit.centre27 Orbit.centre27 Orbit.centre27
  ≡ blockOrientationQuotient
      (Orbit.firstPositive27 SSP.sspNegOne SSP.sspZero)
      Orbit.centre27
      Orbit.centre27 → ⊥
centreBlockClassIsNotCancellationClass ()

aggregateCollisionSeparatedByBlockOrientation :
  aggregateSum structuralZeroRound ≡ aggregateSum cancellationZeroRound
  × (forgetBlockOrientation structuralZeroRound
      ≡ forgetBlockOrientation cancellationZeroRound → ⊥)
aggregateCollisionSeparatedByBlockOrientation =
  refl , (λ classEquality →
    centreBlockClassIsNotCancellationClass
      (trans (sym structuralZeroBlockClass)
        (trans classEquality cancellationBlockClass)))

cancellationToNeutralDoesNotImplyTrivialFineState :
  aggregateSum structuralZeroRound ≡ aggregateSum cancellationZeroRound
  × (structuralZeroRound ≡ cancellationZeroRound → ⊥)
cancellationToNeutralDoesNotImplyTrivialFineState = refl , structuralZeroIsNotCancellationState

------------------------------------------------------------------------
-- The two summaries are incomparable: each has a collision the other splits.
------------------------------------------------------------------------

record ProjectionIncomparabilityWitness : Set where
  constructor projectionIncomparabilityWitness
  field
    blockCollisionAggregateSeparates :
      forgetBlockOrientation allPositiveRound ≡ forgetBlockOrientation baseFlipped
      × (aggregateSum allPositiveRound ≡ aggregateSum baseFlipped → ⊥)
    aggregateCollisionBlockSeparates :
      aggregateSum structuralZeroRound ≡ aggregateSum cancellationZeroRound
      × (forgetBlockOrientation structuralZeroRound
          ≡ forgetBlockOrientation cancellationZeroRound → ⊥)

canonicalProjectionIncomparabilityWitness : ProjectionIncomparabilityWitness
canonicalProjectionIncomparabilityWitness =
  projectionIncomparabilityWitness
    blockOrientationCollisionSeparatedByAggregate
    aggregateCollisionSeparatedByBlockOrientation

------------------------------------------------------------------------
-- Boundary: blockwise and global orbit quotients, scalar aggregation, and
-- world/epistemic semantics are distinct projections of the same fine carrier.
------------------------------------------------------------------------

record InteractionAntipodalFibreBoundary : Set where
  field
    blockwiseOrientationQuotientEqualsScalarSum : Bool
    globalAntipodeEqualsContextualCounterposition : Bool
    aggregateZeroImpliesStructuralZero : Bool
    orientationForgottenBaseReconstructsFineState : Bool
    globalAndBlockwiseQuotientsSame : Bool
    blockOrientationAndAggregateTotallyOrderedByRefinement : Bool

canonicalInteractionAntipodalFibreBoundary : InteractionAntipodalFibreBoundary
canonicalInteractionAntipodalFibreBoundary = record
  { blockwiseOrientationQuotientEqualsScalarSum = false
  ; globalAntipodeEqualsContextualCounterposition = false
  ; aggregateZeroImpliesStructuralZero = false
  ; orientationForgottenBaseReconstructsFineState = false
  ; globalAndBlockwiseQuotientsSame = false
  ; blockOrientationAndAggregateTotallyOrderedByRefinement = false
  }
