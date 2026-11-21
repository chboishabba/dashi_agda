module DASHI.Physics.Motors.SmithFilsingerMidpointDiodeBidiReverseSolveExact where

-- CONDITIONAL finite topology reverse-solve from the user's literal
-- midpoint/NST + 4-diode transcript, not a verified photo/netlist.
-- Source labels are retained from the existing original-number index.
-- The actual exact reel identity is still provisional.  No source,
-- meter observation, capacitor voltage or historical pin is fabricated.
--
-- Source owner: original Filsinger narrated midpoint/spark proposal,
-- distinct from the three-Earth reel, ZVS shunt reel and Kelly diagrams.
-- Classical ideal-diode/transformer model is an INDEPENDENT comparison.
--
-- Companion full exact physical/algebraic regression:
-- scripts/check_filsinger_midpoint_bidi_reverse_sympy.py

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)
import DASHI.Physics.Motors.SmithFilsingerTranscriptDiagramNumbersSourceIndexExact as Source
import DASHI.Physics.Motors.SmithFilsingerReflectedPortBidiExact as Reel

-- The physical/graph completion is an INVERSE hypothesis.  Its label is
-- NOT an assertion of original wiring.  The first three satisfy the four
-- diode / two wires / ganged positive statement at different unknown DC
-- negative and midpoint connections; the fourth carries an ideal conflict.
data RectifierCompletion : Set where
  centreTapDuplicateForwardDiodes : RectifierCompletion
  fullWindingBridgeMidpointSeparate : RectifierCompletion
  fullWindingBridgeSplitRails : RectifierCompletion
  bridgeNegativeHardBondedToMidpoint : RectifierCompletion

nDiodes : RectifierCompletion → Nat
nDiodes centreTapDuplicateForwardDiodes = 4
nDiodes fullWindingBridgeMidpointSeparate = 4
nDiodes fullWindingBridgeSplitRails = 4
nDiodes bridgeNegativeHardBondedToMidpoint = 4

nDiodesPerOuterWire : RectifierCompletion → Nat
nDiodesPerOuterWire centreTapDuplicateForwardDiodes = 2
nDiodesPerOuterWire fullWindingBridgeMidpointSeparate = 2
nDiodesPerOuterWire fullWindingBridgeSplitRails = 2
nDiodesPerOuterWire bridgeNegativeHardBondedToMidpoint = 2

data DiodeEdge : Set where
  AtoPositive BtoPositive : DiodeEdge
  negativeToA negativeToB : DiodeEdge

firstDiode secondDiode thirdDiode fourthDiode :
  RectifierCompletion → DiodeEdge
firstDiode centreTapDuplicateForwardDiodes = AtoPositive
firstDiode fullWindingBridgeMidpointSeparate = AtoPositive
firstDiode fullWindingBridgeSplitRails = AtoPositive
firstDiode bridgeNegativeHardBondedToMidpoint = AtoPositive

secondDiode centreTapDuplicateForwardDiodes = AtoPositive
secondDiode fullWindingBridgeMidpointSeparate = negativeToA
secondDiode fullWindingBridgeSplitRails = negativeToA
secondDiode bridgeNegativeHardBondedToMidpoint = negativeToA

thirdDiode centreTapDuplicateForwardDiodes = BtoPositive
thirdDiode fullWindingBridgeMidpointSeparate = BtoPositive
thirdDiode fullWindingBridgeSplitRails = BtoPositive
thirdDiode bridgeNegativeHardBondedToMidpoint = BtoPositive

fourthDiode centreTapDuplicateForwardDiodes = BtoPositive
fourthDiode fullWindingBridgeMidpointSeparate = negativeToB
fourthDiode fullWindingBridgeSplitRails = negativeToB
fourthDiode bridgeNegativeHardBondedToMidpoint = negativeToB

-- 'All forward facing' if LITERALLY anode at winding end and cathode
-- towards positive bus discriminates the duplicated-positive completion.
-- Physical visual diode orientation/terminals in the original is UNKNOWN.
data OrientationAnswer : Set where
  allOuterEndsTowardsPositive mixedOutputAndReturn : OrientationAnswer

predictedOrientation : RectifierCompletion → OrientationAnswer
predictedOrientation centreTapDuplicateForwardDiodes =
  allOuterEndsTowardsPositive
predictedOrientation fullWindingBridgeMidpointSeparate =
  mixedOutputAndReturn
predictedOrientation fullWindingBridgeSplitRails =
  mixedOutputAndReturn
predictedOrientation bridgeNegativeHardBondedToMidpoint =
  mixedOutputAndReturn

-- Ideal symmetric source: VA-VM = +x and VB-VM = -x, with x != 0.
-- Potential is a SYMBOLIC sign/order tag, not a measured SI voltage.
data ActiveHalfCycle : Set where
  AaboveB BaboveA : ActiveHalfCycle

data PotentialLevel : Set where
  lowHalf midpoint highHalf : PotentialLevel

sourceCentrePotential : PotentialLevel
sourceCentrePotential = midpoint

bridgeNegativePotential : ActiveHalfCycle → PotentialLevel
bridgeNegativePotential AaboveB = lowHalf
bridgeNegativePotential BaboveA = lowHalf

bridgePositivePotential : ActiveHalfCycle → PotentialLevel
bridgePositivePotential AaboveB = highHalf
bridgePositivePotential BaboveA = highHalf

-- WARNING: ONLY THE IDEAL FIXED-VOLTAGE BRIDGE is excluded here.
-- A physically finite-resistance transformer with N hard bonded M would
-- clamp the negative end each active half cycle, causing source-fed
-- current/heat; see SmithFilsingerMidpointReturnClampBacksolveExact.
-- The original transcript ALSO says two diodes off cap, two off here,
-- so four diodes need not even form a conventional bridge.
-- Conditional nonzero-winding counterexample: a conventional four-diode
-- full bridge has DC-negative at -x relative to centre, not at centre.
-- Therefore ordinary bridge N=M is NOT an ideal nonzero-winding solution.
bridgeNegativeIsNotSourceMidpoint :
  (p : ActiveHalfCycle) →
  bridgeNegativePotential p ≡ sourceCentrePotential → ⊥
bridgeNegativeIsNotSourceMidpoint AaboveB ()
bridgeNegativeIsNotSourceMidpoint BaboveA ()

-- All four counts and two per outer wire admit more than one topology.
-- One universal topology assignment based on count alone is impossible.
twoCompatibleNamesDifferent :
  centreTapDuplicateForwardDiodes ≡ fullWindingBridgeMidpointSeparate → ⊥
twoCompatibleNamesDifferent ()

noUniqueTopologyFromDiodeCount :
  (infer : Nat → RectifierCompletion) →
  ((h : RectifierCompletion) → infer (nDiodes h) ≡ h) → ⊥
noUniqueTopologyFromDiodeCount infer agrees =
  twoCompatibleNamesDifferent
    (trans (sym (agrees centreTapDuplicateForwardDiodes))
           (agrees fullWindingBridgeMidpointSeparate))

-- Strongest reuse: the source FIRST records actual four narrated diode
-- packages but keeps original/source scope, not physical equality.
transcriptContainsFourDiodes :
  Source.numberMagnitude Source.midpointFourDiodes ≡ 4
transcriptContainsFourDiodes = refl

-- A distinct reel cannot be welded by a shared verbal term 'ground'.
earthReelNotMidpointTranscript :
  Source.earthThreeElectrodeReel ≡ Source.midpointSparkTranscript →
  Source.Contradiction
earthReelNotMidpointTranscript =
  Source.originalEarthReelIsNotMidpointTranscript

filmedEarthIsNotProposedPortable :
  Reel.filsingerEarthNarration ≡ Reel.filsingerPortableProposal →
  Reel.Contradiction
filmedEarthIsNotProposedPortable = Reel.earthNotPortable

-- Forward predictions: conditional ideal CT gives |half winding| relative
-- to M; full bridge gives 2|half winding| between P and N; split rails
-- give +|half winding| and -|half winding| relative to M. No original
-- source's 4kV description selects a measured output terminal.
--
-- Source access after diode operation is STILL a real energy input
-- problem; phase shifts or spring-return capacitance do not prove it.
