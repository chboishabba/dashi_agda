module DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact where

------------------------------------------------------------------------
-- ACCEPTING FINITE RUN <-> ENDPOINT-CERTIFIED LOCAL-CNF PATH
--
-- This closes the semantic endpoint layer above ConcreteTapeRunCNFWeldExact:
-- the start row literally carries the machine initial state at its unique
-- interior head, and the final row literally carries the accepting state.
--
-- The conversions preserve those exact endpoints while transporting the full
-- finite run to/from its per-edge local-CNF characterization.
--
-- What remains intentionally separate is the unavailable canonical Cell/Bits
-- specialization that turns these endpoint predicates themselves into placed
-- clauses of one flat global SAT assignment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Locality
import DASHI.Mathematics.Complexity.ConcreteTapeWindowCodecCNFWeldExact as Codec
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as RunCNF

record InitialInteriorRow
    (machine : Local.ConcreteTapeMachine)
    (row : Local.TapeRow machine) : Set where
  field
    interior :
      Locality.InteriorHeadConfiguration machine row

    headIsInitial :
      Locality.headState interior
      ≡ Local.initialState machine

open InitialInteriorRow public

record AcceptingInteriorRow
    (machine : Local.ConcreteTapeMachine)
    (row : Local.TapeRow machine) : Set where
  field
    interior :
      Locality.InteriorHeadConfiguration machine row

    headIsAccepting :
      Locality.headState interior
      ≡ Local.acceptingState machine

open AcceptingInteriorRow public

record AcceptingWellFormedRun
    (machine : Local.ConcreteTapeMachine)
    (start : Local.TapeRow machine)
    (rows : List (Local.TapeRow machine))
    (finish : Local.TapeRow machine) : Set where
  field
    initial :
      InitialInteriorRow machine start

    run :
      RunCNF.WellFormedTapeRun machine start rows finish

    accepting :
      AcceptingInteriorRow machine finish

open AcceptingWellFormedRun public

record AcceptingEncodedCNFPath
    {machine : Local.ConcreteTapeMachine}
    {width : Nat}
    (codec : Codec.FixedWidthWindowCodec machine width)
    (start : Local.TapeRow machine)
    (rows : List (Local.TapeRow machine))
    (finish : Local.TapeRow machine) : Set where
  field
    initial :
      InitialInteriorRow machine start

    path :
      RunCNF.EncodedCNFRunPath codec start rows finish

    accepting :
      AcceptingInteriorRow machine finish

open AcceptingEncodedCNFPath public

acceptingRunToEncodedPath :
  ∀ {machine width start rows finish}
    (codec : Codec.FixedWidthWindowCodec machine width) →
  AcceptingWellFormedRun machine start rows finish →
  AcceptingEncodedCNFPath codec start rows finish
acceptingRunToEncodedPath codec certificate = record
  { initial =
      initial certificate
  ; path =
      RunCNF.runToEncodedCNFPath
        codec (run certificate)
  ; accepting =
      accepting certificate
  }

encodedPathToAcceptingRun :
  ∀ {machine width start rows finish}
    {codec : Codec.FixedWidthWindowCodec machine width} →
  AcceptingEncodedCNFPath codec start rows finish →
  AcceptingWellFormedRun machine start rows finish
encodedPathToAcceptingRun certificate = record
  { initial =
      initial certificate
  ; run =
      RunCNF.encodedCNFPathToRun
        (path certificate)
  ; accepting =
      accepting certificate
  }

acceptingRunLength :
  ∀ {machine start rows finish} →
  AcceptingWellFormedRun machine start rows finish →
  Nat
acceptingRunLength certificate =
  RunCNF.runLength (run certificate)

acceptingEncodedPathLength :
  ∀ {machine width start rows finish}
    {codec : Codec.FixedWidthWindowCodec machine width} →
  AcceptingEncodedCNFPath codec start rows finish →
  Nat
acceptingEncodedPathLength certificate =
  RunCNF.encodedRunLength (path certificate)

acceptingRunToEncodedPathPreservesLength :
  ∀ {machine width start rows finish}
    (codec : Codec.FixedWidthWindowCodec machine width)
    (certificate :
      AcceptingWellFormedRun machine start rows finish) →
  acceptingEncodedPathLength
    (acceptingRunToEncodedPath codec certificate)
  ≡ acceptingRunLength certificate
acceptingRunToEncodedPathPreservesLength codec certificate =
  RunCNF.runToCNFPreservesLength
    codec (run certificate)

record ConcreteTapeAcceptingRunCNFBoundary : Set where
  constructor concrete-tape-accepting-run-cnf-boundary
  field
    literalInitialStateEndpointPaid : Bool
    literalAcceptingStateEndpointPaid : Bool
    acceptingRunCarrierPaid : Bool
    acceptingEncodedPathCarrierPaid : Bool
    acceptingRunToEncodedPathPaid : Bool
    encodedPathToAcceptingRunPaid : Bool
    acceptingLengthPreservationPaid : Bool
    canonicalConcreteCodecSpecializationPaid : Bool
    literalEndpointCNFPlacementPaid : Bool
    flatGlobalAssignmentPaid : Bool
    acceptingRunToSATPaid : Bool
    satToAcceptingRunPaid : Bool
    polynomialManyOneReductionPaid : Bool
    genericCookLevinPaid : Bool
    pVsNPResolved : Bool

canonicalConcreteTapeAcceptingRunCNFBoundary :
  ConcreteTapeAcceptingRunCNFBoundary
canonicalConcreteTapeAcceptingRunCNFBoundary =
  concrete-tape-accepting-run-cnf-boundary
    true true true true true true true
    false false false false false false false false
