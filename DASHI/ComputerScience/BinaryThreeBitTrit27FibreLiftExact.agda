module DASHI.ComputerScience.BinaryThreeBitTrit27FibreLiftExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.BinaryThreeBitTwoTritAntipodalCodecExact as Block
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369AddressSymmetryAndBranchGeometryExact as Branch
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit
import DASHI.Foundations.BalancedTernaryAntipodalResidualCodecExact as Residual

------------------------------------------------------------------------
-- 3-BIT BLOCK -> 2 TRITS -> EXPLICIT FRAMING TRIT -> 27-STATE FIBRE
--
-- The third trit is not silently invented.  It is an explicit framing/residual
-- coordinate.  The canonical section uses the antipode-fixed centre, but the
-- generic lift exposes the frame as data.
------------------------------------------------------------------------

record FramedTrit2 : Set where
  constructor framedTrit2
  field
    payload : Block.Trit2
    frame : SSP.SSPTrit

open FramedTrit2 public

liftTo27 : FramedTrit2 → Orbit.TritTriple
liftTo27 (framedTrit2 (Block.trits2 a b) frame) =
  Branch.triple a b frame

projectPayload : Orbit.TritTriple → Block.Trit2
projectPayload (Branch.triple a b c) = Block.trits2 a b

projectFrame : Orbit.TritTriple → SSP.SSPTrit
projectFrame (Branch.triple a b c) = c

payloadAfterLift :
  (framed : FramedTrit2) →
  projectPayload (liftTo27 framed) ≡ payload framed
payloadAfterLift (framedTrit2 (Block.trits2 a b) frame) = refl

frameAfterLift :
  (framed : FramedTrit2) →
  projectFrame (liftTo27 framed) ≡ frame framed
frameAfterLift (framedTrit2 (Block.trits2 a b) frame) = refl

------------------------------------------------------------------------
-- Canonical section: neutral framing coordinate.
------------------------------------------------------------------------

canonicalFrame : SSP.SSPTrit
canonicalFrame = SSP.sspZero

canonicalLift : Block.Trit2 → Orbit.TritTriple
canonicalLift pair = liftTo27 (framedTrit2 pair canonicalFrame)

canonicalFrameIsNeutral :
  (pair : Block.Trit2) →
  projectFrame (canonicalLift pair) ≡ SSP.sspZero
canonicalFrameIsNeutral (Block.trits2 a b) = refl

canonicalPayloadRoundTrip :
  (pair : Block.Trit2) →
  projectPayload (canonicalLift pair) ≡ pair
canonicalPayloadRoundTrip (Block.trits2 a b) = refl

------------------------------------------------------------------------
-- Antipodal compatibility.
--
-- Since the canonical frame is zero and zero is fixed by strict antipode,
-- antipoding the 27 lift is exactly lifting the antipoded 2-trit payload.
------------------------------------------------------------------------

antipodeTriple : Orbit.TritTriple → Orbit.TritTriple
antipodeTriple = Orbit.strictAntipodeTriple

canonicalLiftPreservesAntipode :
  (pair : Block.Trit2) →
  canonicalLift (Block.antipodeTrit2 pair)
  ≡ antipodeTriple (canonicalLift pair)
canonicalLiftPreservesAntipode (Block.trits2 a b)
  rewrite Orbit.zeroIsAntipodeFixedCentre = refl

encodeBit3To27 : Block.Bit3 → Orbit.TritTriple
encodeBit3To27 bits = canonicalLift (Block.encode3to2 bits)

decodeBit3From27Payload : Orbit.TritTriple → Block.Bit3
decodeBit3From27Payload triple =
  Block.decode2to3 (projectPayload triple)

bit3LiftRoundTrip :
  (bits : Block.Bit3) →
  decodeBit3From27Payload (encodeBit3To27 bits) ≡ bits
bit3LiftRoundTrip bits = Block.blockRoundTrip bits

bitComplementBecomes27Antipode :
  (bits : Block.Bit3) →
  encodeBit3To27 (Block.complementBit3 bits)
  ≡ antipodeTriple (encodeBit3To27 bits)
bitComplementBecomes27Antipode bits
  rewrite Block.complementAntipodeEquivariant bits
        | canonicalLiftPreservesAntipode (Block.encode3to2 bits) = refl

------------------------------------------------------------------------
-- Canonical 27 quotient + dependent orientation residual.
--
-- This is the repo-owned exact codec.  No information is lost unless the
-- orientation residual is discarded.
------------------------------------------------------------------------

encodeBit3ToResidual27 : Block.Bit3 → Residual.AntipodalCode27
encodeBit3ToResidual27 bits =
  Residual.encode27 (encodeBit3To27 bits)

residual27DecodesToLiftedBit3 :
  (bits : Block.Bit3) →
  Residual.decode27 (encodeBit3ToResidual27 bits)
  ≡ encodeBit3To27 bits
residual27DecodesToLiftedBit3 bits =
  Residual.decodeAfterEncode27 (encodeBit3To27 bits)

bit3Residual27RoundTrip :
  (bits : Block.Bit3) →
  decodeBit3From27Payload
    (Residual.decode27 (encodeBit3ToResidual27 bits))
  ≡ bits
bit3Residual27RoundTrip bits
  rewrite residual27DecodesToLiftedBit3 bits =
  bit3LiftRoundTrip bits

------------------------------------------------------------------------
-- Complexity / representation receipt.
--
-- The logical payload is 2 trits; realization in the canonical 27 carrier
-- carries one additional explicit framing coordinate.  These are deliberately
-- separate costs.
------------------------------------------------------------------------

record Trit27LiftCost : Set where
  constructor trit27LiftCost
  field
    payloadTritCells : Nat
    framingTritCells : Nat
    realisedTritCells : Nat

open Trit27LiftCost public

canonicalTrit27LiftCost : Trit27LiftCost
canonicalTrit27LiftCost = trit27LiftCost 2 1 3

payloadCostIsTwo : payloadTritCells canonicalTrit27LiftCost ≡ 2
payloadCostIsTwo = refl

framingCostIsOne : framingTritCells canonicalTrit27LiftCost ≡ 1
framingCostIsOne = refl

realisedCostIsThree : realisedTritCells canonicalTrit27LiftCost ≡ 3
realisedCostIsThree = refl

record BinaryThreeBitTrit27FibreLiftBoundary : Set where
  constructor binaryThreeBitTrit27FibreLiftBoundary
  field
    thirdCoordinateExplicit : Bool
    canonicalFrameIsAntipodeFixedCentre : Bool
    payloadRoundTripsThrough27 : Bool
    complementIntertwines27Antipode : Bool
    canonicalResidualCodecReused : Bool
    framingCostCollapsedIntoPayloadCost : Bool
    interactionAppraisalSemanticsClaimedForCSFrame : Bool

canonicalBinaryThreeBitTrit27FibreLiftBoundary :
  BinaryThreeBitTrit27FibreLiftBoundary
canonicalBinaryThreeBitTrit27FibreLiftBoundary =
  binaryThreeBitTrit27FibreLiftBoundary
    true true true true true false false
