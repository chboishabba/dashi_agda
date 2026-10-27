{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkCorrectedCutNetworkBoundaryExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Cross-kernel authority boundary.
--
-- Native Lean sibling PR #68 now owns a corrected finite RT replacement
-- network with exactly k independent Schmidt/Bell cut bonds.  On that same
-- finite model, the boundary subsystem has dimension 2^k and the reduced
-- density matrix entropy is k log 2.  Agda records that theorem-source status
-- only; it does not pretend the Lean theorem is an Agda proof term.
------------------------------------------------------------------------

record CorrectedCutNetworkAuthority : Set where
  constructor correctedCutNetworkAuthority
  field
    cutDepth : Nat
    exactKBondCut : Bool
    subsystemDimensionTwoPowK : Bool
    contractedStateIsCorrectedSchmidtState : Bool
    reducedStateEntropyIsKLogTwo : Bool
    minimalCutEntropyIsKLogTwo : Bool
    sameObjectEntropyCutEquality : Bool

canonicalCorrectedCutNetworkAuthority : (k : Nat) → CorrectedCutNetworkAuthority
canonicalCorrectedCutNetworkAuthority k =
  correctedCutNetworkAuthority k true true true true true true

correctedReplacementNetworkOwned : Bool
correctedReplacementNetworkOwned = true

correctedMinimalCutIdentificationOwned : Bool
correctedMinimalCutIdentificationOwned = true

correctedNetworkSameObjectRTClosed : Bool
correctedNetworkSameObjectRTClosed = true

-- The inspected upstream source remains different: its current copy-isometry
-- tree / named pure state / diagonal contract do not by themselves produce the
-- corrected k-independent-bond state.  Therefore only replacement of those
-- definitions or a genuine equivalence theorem can weld upstream to the closed
-- corrected model.
upstreamReplacementOrEquivalenceStillRequired : Bool
upstreamReplacementOrEquivalenceStillRequired = true

physicalAdSCFTStillRequired : Bool
physicalAdSCFTStillRequired = true

currentRTSourceStatus : String
currentRTSourceStatus =
  "Corrected finite RT is source-closed on an explicit k-independent-bond replacement network: subsystem dimension, Schmidt rank, cut-bond count, reduced density matrix and k log 2 entropy are same-object. The inspected upstream copy tree is not identified with this replacement and requires source replacement or a genuine equivalence theorem. Physical AdS/CFT remains separate."
