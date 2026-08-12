module DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_×_; _,_; proj₂)

import DASHI.Biology.TernaryCantorWheelDiffusionExact as Cantor
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Foundations.SSPPrimeLane369Refinement as Ref
import DASHI.Physics.Closure.SSPPrimeLane369DepthPhaseBridge as Existing

------------------------------------------------------------------------
-- Depthwise wheel semantics.
--
-- The pre-existing Cantor module rotates trit values at a fixed depth.  This
-- module adds the distinct construction in which the wheel acts on refinement
-- morphisms themselves: the depth coordinate carries a period-three phase.
--
-- No external citation is asserted here.  This is a repository-internal
-- synthesis of the existing balanced-ternary/Cantor and 369 refinement lanes.

data DepthWheelPhase : Set where
  phase-0 : DepthWheelPhase
  phase-1 : DepthWheelPhase
  phase-2 : DepthWheelPhase

nextDepthWheelPhase : DepthWheelPhase → DepthWheelPhase
nextDepthWheelPhase phase-0 = phase-1
nextDepthWheelPhase phase-1 = phase-2
nextDepthWheelPhase phase-2 = phase-0

nextDepthWheelPhaseThree :
  (phase : DepthWheelPhase) →
  nextDepthWheelPhase
    (nextDepthWheelPhase
      (nextDepthWheelPhase phase))
  ≡ phase
nextDepthWheelPhaseThree phase-0 = refl
nextDepthWheelPhaseThree phase-1 = refl
nextDepthWheelPhaseThree phase-2 = refl

depthWheelPhase : Nat → DepthWheelPhase
depthWheelPhase zero = phase-0
depthWheelPhase (suc d) = nextDepthWheelPhase (depthWheelPhase d)

depthWheelPhaseAfterThree :
  (d : Nat) →
  depthWheelPhase (suc (suc (suc d))) ≡ depthWheelPhase d
depthWheelPhaseAfterThree d with depthWheelPhase d
... | phase-0 = refl
... | phase-1 = refl
... | phase-2 = refl

threeDepthPhaseIsZero :
  depthWheelPhase 3 ≡ phase-0
threeDepthPhaseIsZero = refl

sixDepthPhaseIsZero :
  depthWheelPhase 6 ≡ phase-0
sixDepthPhaseIsZero = refl

nineDepthPhaseIsZero :
  depthWheelPhase 9 ≡ phase-0
nineDepthPhaseIsZero = refl

threeDepthIsOneWheel :
  depthWheelPhase Ref.three ≡ phase-0
threeDepthIsOneWheel = refl

sixDepthIsTwoWheels :
  depthWheelPhase Ref.six ≡ phase-0
sixDepthIsTwoWheels = refl

nineDepthIsThreeWheels :
  depthWheelPhase Ref.nine ≡ phase-0
nineDepthIsThreeWheels = refl

------------------------------------------------------------------------
-- Phase-dependent refinement morphisms.

record DepthWheelSystem (X : Set) : Set where
  constructor depthWheelSystem
  field
    phase0Refinement : X → X
    phase1Refinement : X → X
    phase2Refinement : X → X

open DepthWheelSystem public

refinementAtPhase :
  ∀ {X : Set} →
  DepthWheelSystem X →
  DepthWheelPhase →
  X → X
refinementAtPhase system phase-0 = phase0Refinement system
refinementAtPhase system phase-1 = phase1Refinement system
refinementAtPhase system phase-2 = phase2Refinement system

refinementAtDepth :
  ∀ {X : Set} →
  DepthWheelSystem X →
  Nat →
  X → X
refinementAtDepth system d =
  refinementAtPhase system (depthWheelPhase d)

oneWheelRenormalisation :
  ∀ {X : Set} →
  DepthWheelSystem X →
  X → X
oneWheelRenormalisation system x =
  phase2Refinement system
    (phase1Refinement system
      (phase0Refinement system x))

firstThreeDepthStepsAreOneWheel :
  ∀ {X : Set} →
  (system : DepthWheelSystem X) →
  (x : X) →
  refinementAtDepth system 2
    (refinementAtDepth system 1
      (refinementAtDepth system 0 x))
  ≡ oneWheelRenormalisation system x
firstThreeDepthStepsAreOneWheel system x = refl

------------------------------------------------------------------------
-- Phase-coloured 369 refinement addresses.

record PhaseTagged369Address (d : Nat) : Set where
  constructor phaseTagged369Address
  field
    address : Ref.Lane369Address d
    phase : DepthWheelPhase
    phaseMatchesDepth : phase ≡ depthWheelPhase d

open PhaseTagged369Address public

tag369Address :
  ∀ {d : Nat} →
  Ref.Lane369Address d →
  PhaseTagged369Address d
tag369Address {d} address =
  phaseTagged369Address address (depthWheelPhase d) refl

canonicalThreeSixNineTaggedAddress :
  PhaseTagged369Address 3
canonicalThreeSixNineTaggedAddress =
  tag369Address Ref.canonicalThreeSixNineAddress

canonicalThreeSixNineTaggedPhaseIsZero :
  phase canonicalThreeSixNineTaggedAddress ≡ phase-0
canonicalThreeSixNineTaggedPhaseIsZero = refl

------------------------------------------------------------------------
-- 3 / 6 / 9 as typed phase fibres.
--
-- 3 = depth phase.
-- 6 = polar Cantor state × depth phase.
-- 9 = full balanced-ternary state × depth phase.
--
-- The direction of the canonical carrier map is 6 -> 9 -> 3: the polar
-- carrier embeds into the full carrier, then state can be forgotten.  A
-- canonical 9 -> 6 map would need an extra policy for the zero trit.

DepthPhaseCell : Set
DepthPhaseCell = DepthWheelPhase

PolarPhaseCell : Set
PolarPhaseCell = Cantor.PolarTrit × DepthWheelPhase

FullPhaseCell : Set
FullPhaseCell = Triadic.KernelTrit × DepthWheelPhase

embedPolarPhaseCell : PolarPhaseCell → FullPhaseCell
embedPolarPhaseCell (polar , phase) =
  Cantor.polarToTrit polar , phase

forgetPolarState : PolarPhaseCell → DepthWheelPhase
forgetPolarState = proj₂

forgetFullState : FullPhaseCell → DepthWheelPhase
forgetFullState = proj₂

polarEmbeddingPreservesDepthPhase :
  (cell : PolarPhaseCell) →
  forgetFullState (embedPolarPhaseCell cell)
  ≡ forgetPolarState cell
polarEmbeddingPreservesDepthPhase (polar , phase) = refl

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

depthPhaseAtlas : List DepthPhaseCell
depthPhaseAtlas =
  phase-0 ∷ phase-1 ∷ phase-2 ∷ []

depthPhaseAtlasCount :
  listLength depthPhaseAtlas ≡ Ref.three
depthPhaseAtlasCount = refl

polarPhaseAtlas : List PolarPhaseCell
polarPhaseAtlas =
  (Cantor.polarNegative , phase-0) ∷
  (Cantor.polarNegative , phase-1) ∷
  (Cantor.polarNegative , phase-2) ∷
  (Cantor.polarPositive , phase-0) ∷
  (Cantor.polarPositive , phase-1) ∷
  (Cantor.polarPositive , phase-2) ∷
  []

polarPhaseAtlasCount :
  listLength polarPhaseAtlas ≡ Ref.six
polarPhaseAtlasCount = refl

fullPhaseAtlas : List FullPhaseCell
fullPhaseAtlas =
  (Triadic.negativeTrit , phase-0) ∷
  (Triadic.negativeTrit , phase-1) ∷
  (Triadic.negativeTrit , phase-2) ∷
  (Triadic.zeroTrit , phase-0) ∷
  (Triadic.zeroTrit , phase-1) ∷
  (Triadic.zeroTrit , phase-2) ∷
  (Triadic.positiveTrit , phase-0) ∷
  (Triadic.positiveTrit , phase-1) ∷
  (Triadic.positiveTrit , phase-2) ∷
  []

fullPhaseAtlasCount :
  listLength fullPhaseAtlas ≡ Ref.nine
fullPhaseAtlasCount = refl

------------------------------------------------------------------------
-- Bridge into the existing depth-aware 369 lane.

record SSPPrimeLane369DepthWheelCantorBridge : Set where
  constructor mkSSPPrimeLane369DepthWheelCantorBridge
  field
    existingDepthPhaseBridge : Existing.SSPPrimeLane369DepthPhaseBridge
    refinementWheelPhase : DepthWheelPhase
    refinementWheelPhaseMatchesDepth :
      refinementWheelPhase ≡
      depthWheelPhase (Existing.depth existingDepthPhaseBridge)

open SSPPrimeLane369DepthWheelCantorBridge public

fromExistingDepthPhaseBridge :
  Existing.SSPPrimeLane369DepthPhaseBridge →
  SSPPrimeLane369DepthWheelCantorBridge
fromExistingDepthPhaseBridge bridge = record
  { existingDepthPhaseBridge = bridge
  ; refinementWheelPhase = depthWheelPhase (Existing.depth bridge)
  ; refinementWheelPhaseMatchesDepth = refl
  }

canonicalRootDepthWheelCantorBridge :
  SSPPrimeLane369DepthWheelCantorBridge
canonicalRootDepthWheelCantorBridge =
  fromExistingDepthPhaseBridge Existing.canonicalRootDepthPhaseBridge

canonicalThreeSixNineDepthWheelCantorBridge :
  SSPPrimeLane369DepthWheelCantorBridge
canonicalThreeSixNineDepthWheelCantorBridge =
  fromExistingDepthPhaseBridge Existing.canonicalThreeSixNineDepthPhaseBridge

canonicalRootWheelPhaseIsZero :
  refinementWheelPhase canonicalRootDepthWheelCantorBridge ≡ phase-0
canonicalRootWheelPhaseIsZero = refl

canonicalThreeSixNineWheelPhaseIsZero :
  refinementWheelPhase canonicalThreeSixNineDepthWheelCantorBridge ≡ phase-0
canonicalThreeSixNineWheelPhaseIsZero = refl

------------------------------------------------------------------------
-- Fail-closed boundary: the new wheel is about depth/refinement morphisms,
-- not an identification with the old fixed-depth trit-value rotation.

record DepthWheelBoundary : Set where
  constructor depthWheelBoundary
  field
    depthWheelEqualsFixedDepthTritRotation : Bool
    depthWheelEqualsFixedDepthTritRotationIsFalse :
      depthWheelEqualsFixedDepthTritRotation ≡ false
    fullNineHasCanonicalRetractionToPolarSixWithoutZeroPolicy : Bool
    fullNineHasCanonicalRetractionToPolarSixWithoutZeroPolicyIsFalse :
      fullNineHasCanonicalRetractionToPolarSixWithoutZeroPolicy ≡ false

canonicalDepthWheelBoundary : DepthWheelBoundary
canonicalDepthWheelBoundary =
  depthWheelBoundary false refl false refl
