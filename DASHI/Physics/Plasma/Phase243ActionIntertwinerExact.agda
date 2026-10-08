module DASHI.Physics.Plasma.Phase243ActionIntertwinerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as T27
import DASHI.Physics.Plasma.PhaseRook270Exact as Rook
import DASHI.Physics.Plasma.PhaseCore243FiveTritExact as Bridge

------------------------------------------------------------------------
-- ACTION TRANSPORT THROUGH THE EXPLICIT CARRIER BIJECTIONS
--
-- We define the action on the existing FiveTrits / Ternary27Point carriers by
-- conjugation through the proven bijections.  Consequently the intertwining
-- statements are exact same-action theorems rather than cardinality matches.
------------------------------------------------------------------------

advanceFiveTrits : Codec.FiveTrits → Codec.FiveTrits
advanceFiveTrits x =
  Bridge.toFiveTrits (Rook.advanceCore (Bridge.fromFiveTrits x))

inverseFiveTrits : Codec.FiveTrits → Codec.FiveTrits
inverseFiveTrits x =
  Bridge.toFiveTrits (Rook.inverseCore (Bridge.fromFiveTrits x))

advanceTernary27 : T27.Ternary27Point → T27.Ternary27Point
advanceTernary27 x =
  Bridge.toTernary27Point
    (Rook.advanceBoundary (Bridge.fromTernary27Point x))

inverseTernary27 : T27.Ternary27Point → T27.Ternary27Point
inverseTernary27 x =
  Bridge.toTernary27Point
    (Rook.inverseBoundary (Bridge.fromTernary27Point x))

coreAdvanceIntertwines : (x : Rook.Core243) →
  Bridge.toFiveTrits (Rook.advanceCore x)
  ≡ advanceFiveTrits (Bridge.toFiveTrits x)
coreAdvanceIntertwines x
  rewrite Bridge.coreFiveRoundTrip x = refl

coreInverseIntertwines : (x : Rook.Core243) →
  Bridge.toFiveTrits (Rook.inverseCore x)
  ≡ inverseFiveTrits (Bridge.toFiveTrits x)
coreInverseIntertwines x
  rewrite Bridge.coreFiveRoundTrip x = refl

boundaryAdvanceIntertwines : (x : Rook.AxisBoundary27) →
  Bridge.toTernary27Point (Rook.advanceBoundary x)
  ≡ advanceTernary27 (Bridge.toTernary27Point x)
boundaryAdvanceIntertwines x
  rewrite Bridge.boundary27RoundTrip x = refl

boundaryInverseIntertwines : (x : Rook.AxisBoundary27) →
  Bridge.toTernary27Point (Rook.inverseBoundary x)
  ≡ inverseTernary27 (Bridge.toTernary27Point x)
boundaryInverseIntertwines x
  rewrite Bridge.boundary27RoundTrip x = refl

------------------------------------------------------------------------
-- Group-law transport.  These follow from the source carrier laws plus the
-- bijection round trips; no new exceptional-group action is inferred.
------------------------------------------------------------------------

advanceFiveThree : (x : Codec.FiveTrits) →
  advanceFiveTrits (advanceFiveTrits (advanceFiveTrits x)) ≡ x
advanceFiveThree x
  rewrite Bridge.fiveCoreRoundTrip x
        | Rook.advanceCoreThree (Bridge.fromFiveTrits x)
        | Bridge.fiveCoreRoundTrip x = refl

inverseFiveInvolutive : (x : Codec.FiveTrits) →
  inverseFiveTrits (inverseFiveTrits x) ≡ x
inverseFiveInvolutive x
  rewrite Bridge.fiveCoreRoundTrip x
        | Rook.inverseCoreInvolutive (Bridge.fromFiveTrits x)
        | Bridge.fiveCoreRoundTrip x = refl

advanceTernary27Three : (x : T27.Ternary27Point) →
  advanceTernary27 (advanceTernary27 (advanceTernary27 x)) ≡ x
advanceTernary27Three x
  rewrite Bridge.ternary27BoundaryRoundTrip x
        | Rook.advanceBoundaryThree (Bridge.fromTernary27Point x)
        | Bridge.ternary27BoundaryRoundTrip x = refl

inverseTernary27Involutive : (x : T27.Ternary27Point) →
  inverseTernary27 (inverseTernary27 x) ≡ x
inverseTernary27Involutive x
  rewrite Bridge.ternary27BoundaryRoundTrip x
        | Rook.inverseBoundaryInvolutive (Bridge.fromTernary27Point x)
        | Bridge.ternary27BoundaryRoundTrip x = refl

record ActionIntertwinerBoundary : Set where
  constructor action-intertwiner-boundary
  field
    sameCarrierOnly : Bool
    sameCarrierOnlyIsFalse : sameCarrierOnly ≡ false
    sameActionTransportPaid : Bool
    sameActionTransportPaidIsTrue : sameActionTransportPaid ≡ true
    createsM24Action : Bool
    createsM24ActionIsFalse : createsM24Action ≡ false
    createsMonsterAction : Bool
    createsMonsterActionIsFalse : createsMonsterAction ≡ false

canonicalActionIntertwinerBoundary : ActionIntertwinerBoundary
canonicalActionIntertwinerBoundary =
  action-intertwiner-boundary false refl true refl false refl false refl

intertwinerReference : String
intertwinerReference =
  "C3 advance and inversion are transported exactly through the explicit Core243/FiveTrits and AxisBoundary27/Ternary27Point bijections; this is a phase-action intertwiner only."
