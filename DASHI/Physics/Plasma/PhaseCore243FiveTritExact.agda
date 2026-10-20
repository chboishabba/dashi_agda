module DASHI.Physics.Plasma.PhaseCore243FiveTritExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Algebra.Trit as Trit
import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as T27
import DASHI.Physics.Plasma.PhaseRook270Exact as Rook

------------------------------------------------------------------------
-- PHASE CORE 243 <-> FIVE-TRIT CARRIER
------------------------------------------------------------------------

phaseToTrit : C3.C3Phase → Trit.Trit
phaseToTrit C3.phase0 = Trit.zer
phaseToTrit C3.phase1 = Trit.pos
phaseToTrit C3.phase2 = Trit.neg

tritToPhase : Trit.Trit → C3.C3Phase
tritToPhase Trit.zer = C3.phase0
tritToPhase Trit.pos = C3.phase1
tritToPhase Trit.neg = C3.phase2

tritPhaseRoundTrip : (p : C3.C3Phase) → tritToPhase (phaseToTrit p) ≡ p
tritPhaseRoundTrip C3.phase0 = refl
tritPhaseRoundTrip C3.phase1 = refl
tritPhaseRoundTrip C3.phase2 = refl

phaseTritRoundTrip : (t : Trit.Trit) → phaseToTrit (tritToPhase t) ≡ t
phaseTritRoundTrip Trit.neg = refl
phaseTritRoundTrip Trit.zer = refl
phaseTritRoundTrip Trit.pos = refl

toFiveTrits : Rook.Core243 → Codec.FiveTrits
toFiveTrits (Rook.core243 k u v p q) =
  Codec.five
    (phaseToTrit k)
    (phaseToTrit u)
    (phaseToTrit v)
    (phaseToTrit p)
    (phaseToTrit q)

fromFiveTrits : Codec.FiveTrits → Rook.Core243
fromFiveTrits (Codec.five a b c d e) =
  Rook.core243
    (tritToPhase a)
    (tritToPhase b)
    (tritToPhase c)
    (tritToPhase d)
    (tritToPhase e)

coreFiveRoundTrip : (x : Rook.Core243) → fromFiveTrits (toFiveTrits x) ≡ x
coreFiveRoundTrip (Rook.core243 k u v p q)
  rewrite tritPhaseRoundTrip k
        | tritPhaseRoundTrip u
        | tritPhaseRoundTrip v
        | tritPhaseRoundTrip p
        | tritPhaseRoundTrip q = refl

fiveCoreRoundTrip : (x : Codec.FiveTrits) → toFiveTrits (fromFiveTrits x) ≡ x
fiveCoreRoundTrip (Codec.five a b c d e)
  rewrite phaseTritRoundTrip a
        | phaseTritRoundTrip b
        | phaseTritRoundTrip c
        | phaseTritRoundTrip d
        | phaseTritRoundTrip e = refl

------------------------------------------------------------------------
-- AXIS BOUNDARY 27 <-> LITERAL TERNARY27POINT
------------------------------------------------------------------------

phaseToSSP : C3.C3Phase → SSP.SSPTrit
phaseToSSP C3.phase0 = SSP.sspZero
phaseToSSP C3.phase1 = SSP.sspPosOne
phaseToSSP C3.phase2 = SSP.sspNegOne

sspToPhase : SSP.SSPTrit → C3.C3Phase
sspToPhase SSP.sspZero = C3.phase0
sspToPhase SSP.sspPosOne = C3.phase1
sspToPhase SSP.sspNegOne = C3.phase2

sspPhaseRoundTrip : (p : C3.C3Phase) → sspToPhase (phaseToSSP p) ≡ p
sspPhaseRoundTrip C3.phase0 = refl
sspPhaseRoundTrip C3.phase1 = refl
sspPhaseRoundTrip C3.phase2 = refl

phaseSSPRoundTrip : (t : SSP.SSPTrit) → phaseToSSP (sspToPhase t) ≡ t
phaseSSPRoundTrip SSP.sspNegOne = refl
phaseSSPRoundTrip SSP.sspZero = refl
phaseSSPRoundTrip SSP.sspPosOne = refl

toTernary27Point : Rook.AxisBoundary27 → T27.Ternary27Point
toTernary27Point (Rook.axis-boundary27 m p q) =
  T27.ternary27Point (phaseToSSP m) (phaseToSSP p) (phaseToSSP q)

fromTernary27Point : T27.Ternary27Point → Rook.AxisBoundary27
fromTernary27Point (T27.ternary27Point m p q) =
  Rook.axis-boundary27 (sspToPhase m) (sspToPhase p) (sspToPhase q)

boundary27RoundTrip : (x : Rook.AxisBoundary27) →
  fromTernary27Point (toTernary27Point x) ≡ x
boundary27RoundTrip (Rook.axis-boundary27 m p q)
  rewrite sspPhaseRoundTrip m | sspPhaseRoundTrip p | sspPhaseRoundTrip q = refl

ternary27BoundaryRoundTrip : (x : T27.Ternary27Point) →
  toTernary27Point (fromTernary27Point x) ≡ x
ternary27BoundaryRoundTrip (T27.ternary27Point m p q)
  rewrite phaseSSPRoundTrip m | phaseSSPRoundTrip p | phaseSSPRoundTrip q = refl

record CarrierRecognitionBoundary : Set where
  constructor carrier-recognition-boundary
  field
    core243SameFiniteCarrierAsFiveTrits : Bool
    core243SameFiniteCarrierAsFiveTritsIsTrue :
      core243SameFiniteCarrierAsFiveTrits ≡ true
    boundary27SameFiniteCarrierAsTernary27 : Bool
    boundary27SameFiniteCarrierAsTernary27IsTrue :
      boundary27SameFiniteCarrierAsTernary27 ≡ true
    fiveTritBijectionCreatesCodecOrPadicSemantics : Bool
    fiveTritBijectionCreatesCodecOrPadicSemanticsIsFalse :
      fiveTritBijectionCreatesCodecOrPadicSemantics ≡ false
    ternary27BijectionCreatesHyperformalSemantics : Bool
    ternary27BijectionCreatesHyperformalSemanticsIsFalse :
      ternary27BijectionCreatesHyperformalSemantics ≡ false

canonicalCarrierRecognitionBoundary : CarrierRecognitionBoundary
canonicalCarrierRecognitionBoundary =
  carrier-recognition-boundary true refl true refl false refl false refl

recognitionReference : String
recognitionReference =
  "Explicit total round-trip bijections: magnet Core243 <-> TriadicPAdicCodec.FiveTrits and AxisBoundary27 <-> Base369 Ternary27Point; semantics remain application-local."
