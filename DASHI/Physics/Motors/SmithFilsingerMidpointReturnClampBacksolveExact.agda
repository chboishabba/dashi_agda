module DASHI.Physics.Motors.SmithFilsingerMidpointReturnClampBacksolveExact where

-- A correction to the conditional earlier BIDI: the literal transcript
-- includes BOTH 'two off this wire, two off that wire' AND 'two diodes
-- come off the cap, two diodes come off here'. Four packages do not prove
-- either a four-diode bridge or duplicated winding-end positive rectifiers.
-- 'return to midpoint, earth, ground' is a narrated intentional path,
-- not an observed equality of source midpoint M, Earth contact and N.
--
-- All models here are INVERSE CANDIDATES, not source-photographed wiring.
-- The source's original reel identities stay distinct; no experimental
-- natural work, a real electrical phase or Agda kernel check is asserted.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Motors.SmithFilsingerTranscriptDiagramNumbersSourceIndexExact as Transcript
import DASHI.Physics.Motors.SmithFilsingerMidpointDiodeBidiReverseSolveExact as Prior

data DiodePairGrouping : Set where
  byOuterWindingEnds : DiodePairGrouping
  byCapacitorAndCoilBranches : DiodePairGrouping

narratedPackageCount : DiodePairGrouping → Nat
narratedPackageCount byOuterWindingEnds = 4
narratedPackageCount byCapacitorAndCoilBranches = 4

differentPairing : byOuterWindingEnds ≡ byCapacitorAndCoilBranches → ⊥
differentPairing ()

noUniqueDiodeInputGroupingFromFourPackages :
  (infer : Nat → DiodePairGrouping) →
  ((g : DiodePairGrouping) →
     infer (narratedPackageCount g) ≡ g) → ⊥
noUniqueDiodeInputGroupingFromFourPackages infer agrees =
  differentPairing
    (trans (sym (agrees byOuterWindingEnds))
           (agrees byCapacitorAndCoilBranches))

-- Retain the exact source-indexed four-package count; two distinct
-- diagrams can instantiate it, but do not assert either was built.
literalNarratedFour : Transcript.numberMagnitude
  Transcript.midpointFourDiodes ≡ 4
literalNarratedFour = refl

-- There are at least THREE independent questions:
-- (1) diode orientation/connectivity, (2) load/earth return choice, and
-- (3) direct wire vs finite source/return impedance. Do not silently
-- conflate them into a single named 'bridge topology'.
data DiodeSkeleton : Set where
  positiveDiodeOr : DiodeSkeleton
  positiveCentreTap : DiodeSkeleton
  conventionalFourDiodeBridge : DiodeSkeleton

data ReturnConnection : Set where
  centreTapIsLoadReturn : ReturnConnection
  bridgeNegativeUnbonded : ReturnConnection
  bridgeNegativeDirectlyBondedToMidpoint : ReturnConnection
  bridgeNegativeThroughResistance : ReturnConnection
  bridgeNegativeThroughCapacitance : ReturnConnection
  bridgeNegativeThroughInductiveReactivePath : ReturnConnection

data HalfCycle : Set where
  outerAHigh outerBHigh : HalfCycle

data WindingEnd : Set where
  outerA outerB : WindingEnd

lowEnd : HalfCycle → WindingEnd
lowEnd outerAHigh = outerB
lowEnd outerBHigh = outerA

highEnd : HalfCycle → WindingEnd
highEnd outerAHigh = outerA
highEnd outerBHigh = outerB

differentSourceWindingEnds :
  (p : HalfCycle) → highEnd p ≡ lowEnd p → ⊥
differentSourceWindingEnds outerAHigh ()
differentSourceWindingEnds outerBHigh ()

-- The *direct-bond + conventional-bridge* model creates a potential
-- M -> negative-bus N -> forward diode -> negative outer winding.
-- For a nonzero ideal symmetric secondary this contradicts the unloaded
-- negative end's prescribed potential. A finite winding resistance DOES
-- admit that path with current/heat; it does NOT forbid real hardware.
data NegativeReturnDiodePath : HalfCycle → Set where
  fromMidpointViaNToOuterB : NegativeReturnDiodePath outerAHigh
  fromMidpointViaNToOuterA : NegativeReturnDiodePath outerBHigh

conditionalClampingRoute :
  (p : HalfCycle) → NegativeReturnDiodePath p
conditionalClampingRoute outerAHigh = fromMidpointViaNToOuterB
conditionalClampingRoute outerBHigh = fromMidpointViaNToOuterA

-- Reuse exact ideal no-go, without asserting all finite-impedance
-- combinations are physically impossible.
idealHardBridgeContradiction :
  (p : Prior.ActiveHalfCycle) →
  Prior.bridgeNegativePotential p
    ≡ Prior.sourceCentrePotential → ⊥
idealHardBridgeContradiction = Prior.bridgeNegativeIsNotSourceMidpoint

-- Separate input grouping and centre return *can* both be part of
-- an intended power circuit with capacitor/coil interactions; whether
-- the physical circuit is passive, overdriven, or externally replenished
-- requires original source-specific signed v*i and full stored work.
