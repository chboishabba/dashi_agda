module DASHI.Wikimedia.KeyShoeCLARAR13DihedralExact where

-- Source: @bigshoesjqz English Radial R13 / CLARA J13 diagram,
-- supplied by a DASHI contributor on 2026-11-16.
-- DASHI reconstruction; not a claim about the creator's undisclosed decoder.
-- Use an independent 13-body type: StageAtlasZeroToTwelve is a semantic
-- stage carrier, whereas this module owns a cyclic alphabet chart.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Foundations.StageAtlasZeroToTwelve as Stage
import DASHI.Foundations.JPlusOneScaleBridge as J
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.ComputerScience.BalancedTernaryC2C3DihedralCodecBridgeExact as PriorC3

data Body13 : Set where
  b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : Body13

-- Reading-order hypothesis from the natural G/H chart. Needs source PDF
-- for byte-exact authority; the finite theorem below is conditional on it.
bodyLabel : Body13 → String
bodyLabel b0 = "GH"
bodyLabel b1 = "IJ"
bodyLabel b2 = "KL"
bodyLabel b3 = "MN"
bodyLabel b4 = "OP"
bodyLabel b5 = "QR"
bodyLabel b6 = "ST"
bodyLabel b7 = "UV"
bodyLabel b8 = "WX"
bodyLabel b9 = "YZ"
bodyLabel b10 = "AB"
bodyLabel b11 = "CD"
bodyLabel b12 = "EF"

nextBody : Body13 → Body13
nextBody b0 = b1
nextBody b1 = b2
nextBody b2 = b3
nextBody b3 = b4
nextBody b4 = b5
nextBody b5 = b6
nextBody b6 = b7
nextBody b7 = b8
nextBody b8 = b9
nextBody b9 = b10
nextBody b10 = b11
nextBody b11 = b12
nextBody b12 = b0

previousBody : Body13 → Body13
previousBody b0 = b12
previousBody b1 = b0
previousBody b2 = b1
previousBody b3 = b2
previousBody b4 = b3
previousBody b5 = b4
previousBody b6 = b5
previousBody b7 = b6
previousBody b8 = b7
previousBody b9 = b8
previousBody b10 = b9
previousBody b11 = b10
previousBody b12 = b11

reflectBody : Body13 → Body13
reflectBody b0 = b6
reflectBody b1 = b5
reflectBody b2 = b4
reflectBody b3 = b3
reflectBody b4 = b2
reflectBody b5 = b1
reflectBody b6 = b0
reflectBody b7 = b12
reflectBody b8 = b11
reflectBody b9 = b10
reflectBody b10 = b9
reflectBody b11 = b8
reflectBody b12 = b7

reflectBodyInvolutive : (b : Body13) → reflectBody (reflectBody b) ≡ b
reflectBodyInvolutive b0 = refl
reflectBodyInvolutive b1 = refl
reflectBodyInvolutive b2 = refl
reflectBodyInvolutive b3 = refl
reflectBodyInvolutive b4 = refl
reflectBodyInvolutive b5 = refl
reflectBodyInvolutive b6 = refl
reflectBodyInvolutive b7 = refl
reflectBodyInvolutive b8 = refl
reflectBodyInvolutive b9 = refl
reflectBodyInvolutive b10 = refl
reflectBodyInvolutive b11 = refl
reflectBodyInvolutive b12 = refl

nextPreviousBody : (b : Body13) → previousBody (nextBody b) ≡ b
nextPreviousBody b0 = refl
nextPreviousBody b1 = refl
nextPreviousBody b2 = refl
nextPreviousBody b3 = refl
nextPreviousBody b4 = refl
nextPreviousBody b5 = refl
nextPreviousBody b6 = refl
nextPreviousBody b7 = refl
nextPreviousBody b8 = refl
nextPreviousBody b9 = refl
nextPreviousBody b10 = refl
nextPreviousBody b11 = refl
nextPreviousBody b12 = refl

reflectConjugatesNextToPrevious :
  (b : Body13) →
  reflectBody (nextBody (reflectBody b)) ≡ previousBody b
reflectConjugatesNextToPrevious b0 = refl
reflectConjugatesNextToPrevious b1 = refl
reflectConjugatesNextToPrevious b2 = refl
reflectConjugatesNextToPrevious b3 = refl
reflectConjugatesNextToPrevious b4 = refl
reflectConjugatesNextToPrevious b5 = refl
reflectConjugatesNextToPrevious b6 = refl
reflectConjugatesNextToPrevious b7 = refl
reflectConjugatesNextToPrevious b8 = refl
reflectConjugatesNextToPrevious b9 = refl
reflectConjugatesNextToPrevious b10 = refl
reflectConjugatesNextToPrevious b11 = refl
reflectConjugatesNextToPrevious b12 = refl

iterateBody : Nat → (Body13 → Body13) → Body13 → Body13
iterateBody zero f b = b
iterateBody (suc n) f b = iterateBody n f (f b)

nextBodyOrder13 : (b : Body13) → iterateBody 13 nextBody b ≡ b
nextBodyOrder13 b0 = refl
nextBodyOrder13 b1 = refl
nextBodyOrder13 b2 = refl
nextBodyOrder13 b3 = refl
nextBodyOrder13 b4 = refl
nextBodyOrder13 b5 = refl
nextBodyOrder13 b6 = refl
nextBodyOrder13 b7 = refl
nextBodyOrder13 b8 = refl
nextBodyOrder13 b9 = refl
nextBodyOrder13 b10 = refl
nextBodyOrder13 b11 = refl
nextBodyOrder13 b12 = refl

-- One fixed natural body: MN. Every other body is exchanged.
onlyMNFixed : (b : Body13) → reflectBody b ≡ b → b ≡ b3
onlyMNFixed b0 ()
onlyMNFixed b1 ()
onlyMNFixed b2 ()
onlyMNFixed b3 _ = refl
onlyMNFixed b4 ()
onlyMNFixed b5 ()
onlyMNFixed b6 ()
onlyMNFixed b7 ()
onlyMNFixed b8 ()
onlyMNFixed b9 ()
onlyMNFixed b10 ()
onlyMNFixed b11 ()
onlyMNFixed b12 ()

data Side : Set where
  first second : Side

flipSide : Side → Side
flipSide first = second
flipSide second = first

data LetterSlot : Set where
  slot : Body13 → Side → LetterSlot

-- Consecutive natural pair swap, and A<->Z reversal in this chart.
pairSwap : LetterSlot → LetterSlot
pairSwap (slot b side) = slot b (flipSide side)

alphabetReversal : LetterSlot → LetterSlot
alphabetReversal (slot b side) = slot (reflectBody b) (flipSide side)

pairSwapInvolutive : (x : LetterSlot) → pairSwap (pairSwap x) ≡ x
pairSwapInvolutive (slot b0 first) = refl
pairSwapInvolutive (slot b0 second) = refl
pairSwapInvolutive (slot b1 first) = refl
pairSwapInvolutive (slot b1 second) = refl
pairSwapInvolutive (slot b2 first) = refl
pairSwapInvolutive (slot b2 second) = refl
pairSwapInvolutive (slot b3 first) = refl
pairSwapInvolutive (slot b3 second) = refl
pairSwapInvolutive (slot b4 first) = refl
pairSwapInvolutive (slot b4 second) = refl
pairSwapInvolutive (slot b5 first) = refl
pairSwapInvolutive (slot b5 second) = refl
pairSwapInvolutive (slot b6 first) = refl
pairSwapInvolutive (slot b6 second) = refl
pairSwapInvolutive (slot b7 first) = refl
pairSwapInvolutive (slot b7 second) = refl
pairSwapInvolutive (slot b8 first) = refl
pairSwapInvolutive (slot b8 second) = refl
pairSwapInvolutive (slot b9 first) = refl
pairSwapInvolutive (slot b9 second) = refl
pairSwapInvolutive (slot b10 first) = refl
pairSwapInvolutive (slot b10 second) = refl
pairSwapInvolutive (slot b11 first) = refl
pairSwapInvolutive (slot b11 second) = refl
pairSwapInvolutive (slot b12 first) = refl
pairSwapInvolutive (slot b12 second) = refl

alphabetReversalInvolutive :
  (x : LetterSlot) → alphabetReversal (alphabetReversal x) ≡ x
alphabetReversalInvolutive (slot b0 first) = refl
alphabetReversalInvolutive (slot b0 second) = refl
alphabetReversalInvolutive (slot b1 first) = refl
alphabetReversalInvolutive (slot b1 second) = refl
alphabetReversalInvolutive (slot b2 first) = refl
alphabetReversalInvolutive (slot b2 second) = refl
alphabetReversalInvolutive (slot b3 first) = refl
alphabetReversalInvolutive (slot b3 second) = refl
alphabetReversalInvolutive (slot b4 first) = refl
alphabetReversalInvolutive (slot b4 second) = refl
alphabetReversalInvolutive (slot b5 first) = refl
alphabetReversalInvolutive (slot b5 second) = refl
alphabetReversalInvolutive (slot b6 first) = refl
alphabetReversalInvolutive (slot b6 second) = refl
alphabetReversalInvolutive (slot b7 first) = refl
alphabetReversalInvolutive (slot b7 second) = refl
alphabetReversalInvolutive (slot b8 first) = refl
alphabetReversalInvolutive (slot b8 second) = refl
alphabetReversalInvolutive (slot b9 first) = refl
alphabetReversalInvolutive (slot b9 second) = refl
alphabetReversalInvolutive (slot b10 first) = refl
alphabetReversalInvolutive (slot b10 second) = refl
alphabetReversalInvolutive (slot b11 first) = refl
alphabetReversalInvolutive (slot b11 second) = refl
alphabetReversalInvolutive (slot b12 first) = refl
alphabetReversalInvolutive (slot b12 second) = refl

alphabetReversalCommutesWithPairSwap :
  (x : LetterSlot) →
  alphabetReversal (pairSwap x) ≡ pairSwap (alphabetReversal x)
alphabetReversalCommutesWithPairSwap (slot b side) = refl

-- 12+1 is a pointed C13 wheel count, not 14 stages J0..J13.
twelvePlusMarkedOne : 12 + 1 ≡ 13
twelvePlusMarkedOne = refl

-- Reuse the existing guarded 0..12 stage count WITHOUT identifying
-- any of its semantic stages with a natural alphabet body.
priorStageCountIs13 : Stage.canonicalStageCount ≡ 13
priorStageCountIs13 = refl

priorStage12OpensRelation :
  Stage.recursiveRole Stage.stage-12 ≡ Stage.relationOpenedAtScale
priorStage12OpensRelation = Stage.stage12OpensRelationAtNewScale

-- Reuse the existing three-state dihedral producer; this is D3,
-- not the D13 action on the independent 13-body alphabet carrier.
priorC3DihedralConjugation :
  (t : SSP.SSPTrit) →
  PriorC3.antipode (PriorC3.cycle (PriorC3.antipode t))
  ≡ PriorC3.cycleInverse t
priorC3DihedralConjugation = PriorC3.antipodeConjugatesCycleToInverse
