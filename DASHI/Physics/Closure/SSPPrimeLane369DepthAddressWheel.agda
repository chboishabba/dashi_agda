module DASHI.Physics.Closure.SSPPrimeLane369DepthAddressWheel where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Biology.TernaryCantorWheelDiffusionExact as Cantor
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Foundations.SSPPrimeLane369Refinement as Ref
import DASHI.Foundations.SSPPrimeLaneUnitAction as Action
import DASHI.Geometry.SSP369TreeAutomorphism as Tree
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel
import DASHI.TrackedPrimes as Tracked

------------------------------------------------------------------------
-- Quotient/remainder-style wheel coordinate.
--
-- completedWheels is the quotient by one full period; residualPhase is the
-- depth residue.  The representation is recursive rather than postulating a
-- division theorem, so the phase law is executable on every Nat.

record WheelDepthCoordinate : Set where
  constructor wheelDepthCoordinate
  field
    completedWheels : Nat
    residualPhase : Wheel.DepthWheelPhase

open WheelDepthCoordinate public

advanceWheelDepthCoordinate : WheelDepthCoordinate → WheelDepthCoordinate
advanceWheelDepthCoordinate (wheelDepthCoordinate q Wheel.phase-0) =
  wheelDepthCoordinate q Wheel.phase-1
advanceWheelDepthCoordinate (wheelDepthCoordinate q Wheel.phase-1) =
  wheelDepthCoordinate q Wheel.phase-2
advanceWheelDepthCoordinate (wheelDepthCoordinate q Wheel.phase-2) =
  wheelDepthCoordinate (suc q) Wheel.phase-0

wheelDepthCoordinate : Nat → WheelDepthCoordinate
wheelDepthCoordinate zero = wheelDepthCoordinate zero Wheel.phase-0
wheelDepthCoordinate (suc d) =
  advanceWheelDepthCoordinate (wheelDepthCoordinate d)

wheelCoordinatePhaseMatchesDepth :
  (d : Nat) →
  residualPhase (wheelDepthCoordinate d) ≡ Wheel.depthWheelPhase d
wheelCoordinatePhaseMatchesDepth zero = refl
wheelCoordinatePhaseMatchesDepth (suc d)
  with wheelDepthCoordinate d | wheelCoordinatePhaseMatchesDepth d
... | wheelDepthCoordinate q Wheel.phase-0 | refl = refl
... | wheelDepthCoordinate q Wheel.phase-1 | refl = refl
... | wheelDepthCoordinate q Wheel.phase-2 | refl = refl

advanceCoordinateThree :
  (c : WheelDepthCoordinate) →
  advanceWheelDepthCoordinate
    (advanceWheelDepthCoordinate
      (advanceWheelDepthCoordinate c))
  ≡ wheelDepthCoordinate (suc (completedWheels c)) (residualPhase c)
advanceCoordinateThree (wheelDepthCoordinate q Wheel.phase-0) = refl
advanceCoordinateThree (wheelDepthCoordinate q Wheel.phase-1) = refl
advanceCoordinateThree (wheelDepthCoordinate q Wheel.phase-2) = refl

threeTimes : Nat → Nat
threeTimes zero = zero
threeTimes (suc q) = suc (suc (suc (threeTimes q)))

phaseAtThreeTimes :
  (q : Nat) →
  Wheel.depthWheelPhase (threeTimes q) ≡ Wheel.phase-0
phaseAtThreeTimes zero = refl
phaseAtThreeTimes (suc q) =
  trans
    (Wheel.depthWheelPhaseAfterThree (threeTimes q))
    (phaseAtThreeTimes q)

coordinateAtThreeTimes :
  (q : Nat) →
  wheelDepthCoordinate (threeTimes q)
  ≡ wheelDepthCoordinate q Wheel.phase-0
coordinateAtThreeTimes zero = refl
coordinateAtThreeTimes (suc q)
  rewrite coordinateAtThreeTimes q = refl

phaseOrdinal : Wheel.DepthWheelPhase → Nat
phaseOrdinal Wheel.phase-0 = 0
phaseOrdinal Wheel.phase-1 = 1
phaseOrdinal Wheel.phase-2 = 2

threeCoordinateIsOneWheel :
  wheelDepthCoordinate 3 ≡ wheelDepthCoordinate 1 Wheel.phase-0
threeCoordinateIsOneWheel = refl

sixCoordinateIsTwoWheels :
  wheelDepthCoordinate 6 ≡ wheelDepthCoordinate 2 Wheel.phase-0
sixCoordinateIsTwoWheels = refl

nineCoordinateIsThreeWheels :
  wheelDepthCoordinate 9 ≡ wheelDepthCoordinate 3 Wheel.phase-0
nineCoordinateIsThreeWheels = refl

------------------------------------------------------------------------
-- One complete refinement wheel has the already-checked depth-three branch
-- multiplicities: 2^3 for the polar/Cantor restriction and 3^3 for the full
-- ternary carrier.  These aliases deliberately reuse the existing proofs.

polarOneWheelBranchMultiplicity : Cantor.polarAddressCount 3 ≡ 8
polarOneWheelBranchMultiplicity = Cantor.polarDepthThreeCount

fullOneWheelBranchMultiplicity : Cantor.ternaryAddressCount 3 ≡ 27
fullOneWheelBranchMultiplicity = Cantor.ternaryDepthThreeCount

------------------------------------------------------------------------
-- Residual-bearing polar projection.
--
-- There is no canonical total 9 -> 6 retraction because the zero trit has no
-- polar image.  Rather than choosing a branch, keep zero as an explicit
-- residual.  On the embedded polar carrier this is a genuine left inverse.

data PolarProjectionResult : Set where
  projectedPolar : Wheel.PolarPhaseCell → PolarProjectionResult
  zeroBranchResidual : Wheel.DepthWheelPhase → PolarProjectionResult

polarProject : Wheel.FullPhaseCell → PolarProjectionResult
polarProject (Triadic.negativeTrit , phase) =
  projectedPolar (Cantor.polarNegative , phase)
polarProject (Triadic.zeroTrit , phase) =
  zeroBranchResidual phase
polarProject (Triadic.positiveTrit , phase) =
  projectedPolar (Cantor.polarPositive , phase)

polarProjectAfterEmbedding :
  (cell : Wheel.PolarPhaseCell) →
  polarProject (Wheel.embedPolarPhaseCell cell) ≡ projectedPolar cell
polarProjectAfterEmbedding (Cantor.polarNegative , phase) = refl
polarProjectAfterEmbedding (Cantor.polarPositive , phase) = refl

zeroProjectionRetainsPhase :
  (phase : Wheel.DepthWheelPhase) →
  polarProject (Triadic.zeroTrit , phase) ≡ zeroBranchResidual phase
zeroProjectionRetainsPhase phase = refl

------------------------------------------------------------------------
-- The depth wheel and the existing 3/6/9 address wheel are independent local
-- C3 actions.  Their product is a nine-cell phase torus; because each action
-- touches only one coordinate, they commute definitionally.

DepthAddressPhaseCell : Set
DepthAddressPhaseCell = Ref.Lane369Digit × Wheel.DepthWheelPhase

depthPhaseAction : DepthAddressPhaseCell → DepthAddressPhaseCell
depthPhaseAction (digit , phase) =
  digit , Wheel.nextDepthWheelPhase phase

addressPhaseAction : DepthAddressPhaseCell → DepthAddressPhaseCell
addressPhaseAction (digit , phase) =
  Action.rotateLane369DigitOnce digit , phase

depthAddressActionsCommute :
  (cell : DepthAddressPhaseCell) →
  depthPhaseAction (addressPhaseAction cell)
  ≡ addressPhaseAction (depthPhaseAction cell)
depthAddressActionsCommute (digit , phase) = refl

addressPhaseActionThree :
  (cell : DepthAddressPhaseCell) →
  addressPhaseAction
    (addressPhaseAction
      (addressPhaseAction cell))
  ≡ cell
addressPhaseActionThree (Ref.digit-3 , phase) = refl
addressPhaseActionThree (Ref.digit-6 , phase) = refl
addressPhaseActionThree (Ref.digit-9 , phase) = refl

depthPhaseActionThree :
  (cell : DepthAddressPhaseCell) →
  depthPhaseAction
    (depthPhaseAction
      (depthPhaseAction cell))
  ≡ cell
depthPhaseActionThree (digit , Wheel.phase-0) = refl
depthPhaseActionThree (digit , Wheel.phase-1) = refl
depthPhaseActionThree (digit , Wheel.phase-2) = refl

depthAddressPhaseAtlas : List DepthAddressPhaseCell
depthAddressPhaseAtlas =
  (Ref.digit-3 , Wheel.phase-0) ∷
  (Ref.digit-3 , Wheel.phase-1) ∷
  (Ref.digit-3 , Wheel.phase-2) ∷
  (Ref.digit-6 , Wheel.phase-0) ∷
  (Ref.digit-6 , Wheel.phase-1) ∷
  (Ref.digit-6 , Wheel.phase-2) ∷
  (Ref.digit-9 , Wheel.phase-0) ∷
  (Ref.digit-9 , Wheel.phase-1) ∷
  (Ref.digit-9 , Wheel.phase-2) ∷
  []

depthAddressPhaseAtlasCount :
  Wheel.listLength depthAddressPhaseAtlas ≡ Ref.nine
depthAddressPhaseAtlasCount = refl

------------------------------------------------------------------------
-- Actual tree action: the canonical p7 generator rotates every 369 digit and
-- has order three on every finite refinement address.  The imported tree
-- theorem already proves that the same action preserves depth and commutes
-- with prefix truncation.

p7AddressWheel :
  ∀ {d : Nat} → Ref.Lane369Address d → Ref.Lane369Address d
p7AddressWheel = Action.actOnAddress Tracked.p7 Action.canonicalGeneratorStep

p7AddressWheelThree :
  ∀ {d : Nat} (address : Ref.Lane369Address d) →
  p7AddressWheel (p7AddressWheel (p7AddressWheel address)) ≡ address
p7AddressWheelThree Ref.root = refl
p7AddressWheelThree (Ref.extend path Ref.digit-3)
  rewrite p7AddressWheelThree path = refl
p7AddressWheelThree (Ref.extend path Ref.digit-6)
  rewrite p7AddressWheelThree path = refl
p7AddressWheelThree (Ref.extend path Ref.digit-9)
  rewrite p7AddressWheelThree path = refl

p7AddressWheelPreservesDepth :
  ∀ {d : Nat} (address : Ref.Lane369Address d) →
  Ref.addressDepth (p7AddressWheel address) ≡ d
p7AddressWheelPreservesDepth =
  Tree.actionPreservesAddressDepth Tracked.p7 Action.canonicalGeneratorStep

p7AddressWheelCommutesWithPrefix :
  ∀ {d : Nat} (address : Ref.Lane369Address (suc d)) →
  Ref.prefix (p7AddressWheel address)
  ≡ p7AddressWheel (Ref.prefix address)
p7AddressWheelCommutesWithPrefix =
  Tree.actionCommutesWithPrefix Tracked.p7 Action.canonicalGeneratorStep

p7AddressWheelPreservesTaggedDepthPhase :
  ∀ {d : Nat} (address : Ref.Lane369Address d) →
  Wheel.phase (Wheel.tag369Address (p7AddressWheel address))
  ≡ Wheel.phase (Wheel.tag369Address address)
p7AddressWheelPreservesTaggedDepthPhase address = refl

------------------------------------------------------------------------
-- Equivariance of one refinement step under the address wheel.  This is the
-- concrete skew-product seam: rotating an already-refined address is the same
-- as rotating its parent and the newly attached digit together.

p7AddressWheelRefinementEquivariant :
  ∀ {d : Nat}
    (parent : Ref.Lane369Address d)
    (digit : Ref.Lane369Digit) →
  p7AddressWheel (Ref.extend parent digit)
  ≡ Ref.extend
      (p7AddressWheel parent)
      (Action.rotateLane369DigitOnce digit)
p7AddressWheelRefinementEquivariant parent digit = refl

------------------------------------------------------------------------
-- Boundary: commuting local product actions are proved above.  No claim is
-- made here that every future phase-dependent refinement law factors as that
-- direct product; a state-dependent cocycle remains a stronger structure.

record DepthAddressWheelBoundary : Set where
  constructor depthAddressWheelBoundary
  field
    localDepthAndAddressActionsCommute : Bool
    p7AddressWheelHasOrderThree : Bool
    addressWheelPreservesRefinementDepth : Bool
    arbitraryPhaseDependentRefinementIsDirectProductClaimed : Bool
    arbitraryPhaseDependentRefinementIsDirectProductClaimedIsFalse :
      arbitraryPhaseDependentRefinementIsDirectProductClaimed ≡ false

canonicalDepthAddressWheelBoundary : DepthAddressWheelBoundary
canonicalDepthAddressWheelBoundary =
  depthAddressWheelBoundary true true true false refl
