module DASHI.Foundations.E6F3DepthQuadraticInteractionCrossKernelReceiptExact where

------------------------------------------------------------------------
-- CROSS-KERNEL RECEIPT: PREFIX-DEPTH x QUADRATIC-STRATUM INTERACTION
--
-- Companion Lean PR #58 now source-writes exact finite intersection profiles
-- on the SAME standardized F3^5 carrier.  Profiles are ordered as
--
--   (zero point, nonzero Q=0, Q=1, Q=2).
--
-- Depth 1:
--   prefix 0    -> (1,32,24,24)
--   prefix +/-1 -> (0,24,33,24)
--
-- Depth 2:
--   (0,0)                    -> (1,8,6,12)
--   exactly one nonzero      -> (0,12,9,6)
--   both nonzero             -> (0,6,12,9)
--
-- Depth 3:
--   all zero                 -> (1,0,4,4)
--   exactly one nonzero      -> (0,4,1,4)
--   exactly two nonzero      -> (0,4,4,1)
--   all nonzero              -> (0,1,4,4)
--
-- Hence depth and quadratic stratum are explicitly not a Cartesian-product
-- decomposition.  This receipt records source status only.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

leanRepository : String
leanRepository = "chboishabba/dashi_lean4"

leanPR : Nat
leanPR = 58

leanOwner : String
leanOwner = "Integration/E6F3DepthQuadraticInteraction.lean"

record Profile : Set where
  constructor profile
  field
    zeroCount : Nat
    nonzeroQZeroCount : Nat
    qOneCount : Nat
    qTwoCount : Nat
open Profile public

depth1Zero : Profile
depth1Zero = profile 1 32 24 24

depth1Nonzero : Profile
depth1Nonzero = profile 0 24 33 24

depth2ZeroZero : Profile
depth2ZeroZero = profile 1 8 6 12

depth2OneNonzero : Profile
depth2OneNonzero = profile 0 12 9 6

depth2BothNonzero : Profile
depth2BothNonzero = profile 0 6 12 9

depth3ZeroZeroZero : Profile
depth3ZeroZeroZero = profile 1 0 4 4

depth3OneNonzero : Profile
depth3OneNonzero = profile 0 4 1 4

depth3TwoNonzero : Profile
depth3TwoNonzero = profile 0 4 4 1

depth3AllNonzero : Profile
depth3AllNonzero = profile 0 1 4 4

record Boundary : Set where
  constructor boundary
  field
    sameStandardF3FiveCarrierConsumed : Bool
    depth1ProfilesLeanSourceWritten : Bool
    depth2ProfilesLeanSourceWritten : Bool
    depth3ProfilesLeanSourceWritten : Bool
    exactIntersectionTensorNamedInLean : Bool
    nonProductWitnessLeanSourceWritten : Bool
    leanExactHeadKernelReceiptObserved : Bool
    agdaIntersectionTensorProducerKernelPaidHere : Bool
    depthQuadraticDeclaredIndependentProduct : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary =
  boundary true true true true true true false false false
