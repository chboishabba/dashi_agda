module DASHI.Physics.Motors.SmithFilsingerFinitePhaseMatchingExact where

-- User-origin Smith/Filsinger source/sink timing steelman; finite mathematical
-- certificates only, NOT physical measurements, original netlist identity,
-- real Earth source admission, or full Maxwell/plasma propagation.
-- Reuses established DASHI arithmetic solver and existing midpoint work owner.
--
-- Related producers:
-- DASHI.Chemistry.HydrogenEfficiencyCrossMultiplyExact (Nat solver use)
-- DASHI.Physics.Motors.SmithFilsingerMidpointPhaseWorkExact
-- DASHI.Physics.Motors.SmithFilsingerTimeIndexedTransferExact
-- PR #1521 physical source-admittance model (separate unmerged branch).
--
-- Source attribution / methodology:
-- user-proposed differential off-phase environmental coupling;
-- classical maximum-power-transfer relation for positive linear Thevenin R.
-- Filsinger's plate remains a proposed device, not this proven DC network.
-- Source-selected modal/Maxwell coefficients and actual work still OPEN.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

import DASHI.Physics.Motors.SmithFilsingerMidpointPhaseWorkExact as Midpoint

-- F01: clearing the common drive gives exactly the same normalized
-- two-channel cross ratio for a scalar multiplier in the Nat semiring.
-- This does not define real/complex phase or prove source coherence.
commonDriverCrossRatioInvariant :
  (gain first second : Nat) →
  (gain * first) * second ≡ (gain * second) * first
commonDriverCrossRatioInvariant gain first second =
  solve 3
    (λ k a b → ((k :* a) :* b) := ((k :* b) :* a))
    refl gain first second

-- F05: source matching, denominator-cleared square gap above the exact
-- normalized match u = R_s G = 1.  For u = 1 + k, the difference between
-- the normalized maximum and load work is k² / [4 (1+u)²].
-- Energy/voltage units, division and positive denominator require a
-- separately admitted ordered rational interpretation.
sourceMatchSquareGapAbove :
  (k : Nat) →
  (1 + (1 + k)) * (1 + (1 + k))
   ≡ 4 * (1 + k) + k * k
sourceMatchSquareGapAbove k =
  solve 1
    (λ x →
       ((con 1 :+ (con 1 :+ x)) :* (con 1 :+ (con 1 :+ x)))
         := ((con 4 :* (con 1 :+ x)) :+ (x :* x)))
    refl k

-- The complementary below-match identity uses a witness u + gap = 1.
sourceMatchSquareGapBelow :
  (u gap : Nat) → u + gap ≡ 1 →
  (1 + u) * (1 + u) ≡ 4 * u + gap * gap
sourceMatchSquareGapBelow u gap split =
  trans
    (cong (λ z → (z + u) * (z + u)) (sym split))
    (trans
      (solve 2
        (λ x y →
          (((x :+ y) :+ x) :* ((x :+ y) :+ x))
          := ((con 4 :* x :* (x :+ y)) :+ (y :* y)))
        refl u gap)
      (trans
        (cong (λ z → (4 * u * z) + gap * gap) split)
        (solve 2
          (λ x y →
            ((con 4 :* x :* con 1) :+ (y :* y))
            := ((con 4 :* x) :+ (y :* y)))
          refl u gap)))

-- F05 strengthened: *all rationally representable* positive source
-- ratios u=x/y (y>0 for physical interpretation), denominator cleared.
-- In either branch of the order comparison x=y+d or y=x+d,
-- (x+y)^2 = 4xy+d^2. This is a cross-multiplied square-gap certificate
-- over arbitrary Nat x,y,d; no unproved division or subtraction.
sourceMatchRationalAbove :
  (denominator gap : Nat) →
  ((denominator + gap) + denominator) *
    ((denominator + gap) + denominator)
    ≡ 4 * ((denominator + gap) * denominator) + gap * gap
sourceMatchRationalAbove denominator gap =
  solve 2
    (λ y d →
      (((y :+ d) :+ y) :* ((y :+ d) :+ y))
      := ((con 4 :* ((y :+ d) :* y)) :+ (d :* d)))
    refl denominator gap

sourceMatchRationalBelow :
  (numerator gap : Nat) →
  (numerator + (numerator + gap)) *
    (numerator + (numerator + gap))
    ≡ 4 * (numerator * (numerator + gap)) + gap * gap
sourceMatchRationalBelow numerator gap =
  solve 2
    (λ x d →
      ((x :+ (x :+ d)) :* (x :+ (x :+ d)))
      := ((con 4 :* (x :* (x :+ d))) :+ (d :* d)))
    refl numerator gap

-- F06: exact two-slot complementarity is the discrete, nontrigonometric
-- analogue of g + a sin(t), g + a sin(t+pi). At every slot, an internally
-- controlled branch goes high exactly when the other goes low.
data Slot : Set where
  slotA slotB : Slot

high : Nat → Nat → Nat
high base excursion = base + (excursion + excursion)

branchOne : Slot → Nat → Nat → Nat
branchOne slotA base excursion = high base excursion
branchOne slotB base excursion = base

branchTwo : Slot → Nat → Nat → Nat
branchTwo slotA base excursion = base
branchTwo slotB base excursion = high base excursion

complementaryConstantTotal :
  (slot : Slot) (base excursion : Nat) →
  branchOne slot base excursion + branchTwo slot base excursion
    ≡ high base excursion + base
complementaryConstantTotal slotA base excursion = refl
complementaryConstantTotal slotB base excursion =
  solve 2
    (λ b a →
      b :+ (b :+ (a :+ a))
       := (b :+ (a :+ a)) :+ b)
    refl base excursion

-- F04: for the four equally sampled quadrature phases 0,90,180,270,
-- the signed Re[(a+i b) e^(i theta)] cross contribution is represented
-- by positive/negative Nat magnitudes.  Sums coincide exactly.
-- This is NOT an arbitrary stochastic phase, plasma, or nonlinear theorem.
data QuarterPhase : Set where
  zeroPhase quarterPhase halfPhase threeQuarterPhase : QuarterPhase

positiveCross : QuarterPhase → Nat → Nat → Nat
positiveCross zeroPhase re im = re
positiveCross quarterPhase re im = 0
positiveCross halfPhase re im = 0
positiveCross threeQuarterPhase re im = im

negativeCross : QuarterPhase → Nat → Nat → Nat
negativeCross zeroPhase re im = 0
negativeCross quarterPhase re im = im
negativeCross halfPhase re im = re
negativeCross threeQuarterPhase re im = 0

positiveFourPhaseSum : Nat → Nat → Nat
positiveFourPhaseSum re im =
  positiveCross zeroPhase re im +
    (positiveCross quarterPhase re im +
      (positiveCross halfPhase re im +
        positiveCross threeQuarterPhase re im))

negativeFourPhaseSum : Nat → Nat → Nat
negativeFourPhaseSum re im =
  negativeCross zeroPhase re im +
    (negativeCross quarterPhase re im +
      (negativeCross halfPhase re im +
        negativeCross threeQuarterPhase re im))

fourPhaseQuadraticCrossCancellation :
  (re im : Nat) →
  positiveFourPhaseSum re im ≡ negativeFourPhaseSum re im
fourPhaseQuadraticCrossCancellation re im =
  solve 2
    (λ x y → (x :+ y) := (y :+ (x :+ con 0)))
    refl re im

-- F07: strictly positive exact *rational* witness for reversal of
-- optimum between the SAME two-state phase schedules.
--
-- G states in-phase = 1/2 and 3/2, each half a cycle.
-- Anti-phase total G = 1 constant.
-- V_oc=1.
-- R_s=1: anti = 1/4, inphase average = 52/225, difference = 17/900.
-- R_s=3: anti = 1/16, inphase average = 196/3025,
--         inphase - anti = 111/48400.
-- Cross-multiplication positive gaps below are normal-form kernel targets.
record StrictCrossGap (largerCross smallerCross : Nat) : Set where
  constructor strictCrossGap
  field
    gapTail : Nat
    exactGap : largerCross ≡ smallerCross + suc gapTail

resistanceOneAntiStrictlyBetter : StrictCrossGap 225 (4 * 52)
resistanceOneAntiStrictlyBetter = strictCrossGap 16 refl

resistanceThreeInphaseStrictlyBetter :
  StrictCrossGap (196 * 16) 3025
resistanceThreeInphaseStrictlyBetter = strictCrossGap 110 refl


-- F02/F03 finite *causal* counterexamples. A common transmitter may launch
-- two path signals at different times that arrive simultaneously with
-- different phases. Likewise an undriven detuned mode need not preserve the
-- phase of a slower mode. These are deliberately finite clock examples:
-- NOT a Maxwell group velocity, spatial Green function or continuous mode
-- locking theorem.
import DASHI.Physics.Motors.SmithFilsingerTimeIndexedTransferExact as Time

data BinaryFieldPhase : Set where
  phasePlus phaseMinus : BinaryFieldPhase

togglePhase : BinaryFieldPhase → BinaryFieldPhase
togglePhase phasePlus = phaseMinus
togglePhase phaseMinus = phasePlus

alternatingSourcePhase : Nat → BinaryFieldPhase
alternatingSourcePhase zero = phasePlus
alternatingSourcePhase (suc t) = togglePhase (alternatingSourcePhase t)

fastPath : Time.RetardedFlight
fastPath = Time.scheduled 1 0

slowPath : Time.RetardedFlight
slowPath = Time.scheduled 0 1

twoPathsReachSameTime :
  Time.RetardedFlight.arrival fastPath
    ≡ Time.RetardedFlight.arrival slowPath
twoPathsReachSameTime = refl

arrivalDoesNotIdentifyLaunchPhase :
  alternatingSourcePhase (Time.RetardedFlight.launch fastPath)
    ≡ alternatingSourcePhase (Time.RetardedFlight.launch slowPath)
      → Midpoint.Contradiction
arrivalDoesNotIdentifyLaunchPhase ()

freeRunningDifferentClocksStartAligned :
  alternatingSourcePhase zero ≡ phasePlus
freeRunningDifferentClocksStartAligned = refl

freeRunningDifferentClocksCanSeparate :
  alternatingSourcePhase (suc zero) ≡ phasePlus
    → Midpoint.Contradiction
freeRunningDifferentClocksCanSeparate ()

-- F08: if there is no incoming naturally powered work, a positive
-- *net incoming* natural-port classification is impossible even though
-- driver energy may radiate out of the natural-facing port.
record PositiveNaturalNet (r : Midpoint.MidpointTwoPortWorkWindow) : Set where
  field
    surplus : Nat
    incomingPaysReturnAndSurplus :
      Midpoint.MidpointTwoPortWorkWindow.naturalIncident r
        ≡ Midpoint.MidpointTwoPortWorkWindow.naturalOutgoing r + suc surplus

zeroCannotPayPositiveSum :
  (outgoing extra : Nat) →
  zero ≡ outgoing + suc extra → Midpoint.Contradiction
zeroCannotPayPositiveSum zero extra ()
zeroCannotPayPositiveSum (suc outgoing) extra ()

naturalOffCannotSupplyPositiveNet :
  (r : Midpoint.MidpointTwoPortWorkWindow) →
  Midpoint.MidpointTwoPortWorkWindow.naturalIncident r ≡ zero →
  PositiveNaturalNet r → Midpoint.Contradiction
naturalOffCannotSupplyPositiveNet r sourceOff positive =
  zeroCannotPayPositiveSum
    (Midpoint.MidpointTwoPortWorkWindow.naturalOutgoing r)
    (PositiveNaturalNet.surplus positive)
    (trans (sym sourceOff)
      (PositiveNaturalNet.incomingPaysReturnAndSurplus positive))

-- F11: exact paired-world work equality, no subtraction or assumption
-- that the realised natural-source work is identical in the two cases.
-- Both trajectories share the initial state inventory, but can have
-- different final storage, load, natural response and dissipation.
record SameBoundaryStep (initial : Nat) : Set where
  field
    natural controller modulator load loss finalStorage : Nat
    balance :
      ((natural + controller) + modulator) + initial
        ≡ (load + loss) + finalStorage

input : ∀ {initial} → SameBoundaryStep initial → Nat
input {initial} r =
  ((SameBoundaryStep.natural r + SameBoundaryStep.controller r)
    + SameBoundaryStep.modulator r) + initial

output : ∀ {initial} → SameBoundaryStep initial → Nat
output r =
  (SameBoundaryStep.load r + SameBoundaryStep.loss r)
    + SameBoundaryStep.finalStorage r

commuteInputs : (first second : Nat) →
  first + second ≡ second + first
commuteInputs first second =
  solve 2 (λ x y → (x :+ y) := (y :+ x)) refl first second

matchedWorldsCrossBalance :
  ∀ {initial} (tuned control : SameBoundaryStep initial) →
    output tuned + input control ≡ output control + input tuned
matchedWorldsCrossBalance tuned control =
  trans
    (cong (λ z → z + input control)
      (sym (SameBoundaryStep.balance tuned)))
    (trans
      (commuteInputs (input tuned) (input control))
      (cong (λ z → z + input tuned)
        (SameBoundaryStep.balance control)))

-- F09 already belongs to Midpoint.phaseReadoutAloneCannotIdentifyNaturalWork;
-- no duplicate. F12 belongs to #1521 RepeatableSourceReceiverCycle.
-- Physical S0/P1/P2/R1/R2/R3 and radiation/cloud endpoints remain open.
