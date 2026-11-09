module DASHI.Mathematics.Complexity.Karp21NativeEndpointHistoryConservationExact where

------------------------------------------------------------------------
-- F2.2 SAME-EXECUTION BINARY ENDPOINT HISTORY MEMORY INVARIANT.
--
-- The original sparse N21 certificate supplies two Boolean labels
-- for every parsed signed raw edge. A valid actual binary first-
-- enabled "advance" consumes one signed edge and two certificate
-- bits, and prepends the edge's original LE u/v binary registers
-- and those same two bits to chronological endpoint history.
--
-- Thus live history-bit-payload + remaining endpoint bit-registers
-- + unconsumed certificate bits is INVARIANT under every actual
-- first-enabled binary source step, including invalid/reject and
-- threshold terminal branches.
--
-- Source graph field input theorem bounds initial edge endpoint
-- bits by original graph word; resulting actual history length is
-- bounded by |original graph word| + |original certificate word|.
--
-- Excludes list cell pointers/tags, copying, head moves and clock.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.List.Base using (length)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
open import Data.Nat.Tactic.RingSolver using (solve)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointHistoryExact as History
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphRuntimeExact as Graph
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryPriorityMachineExact as Machine
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryFiniteRunExact as Run
import DASHI.Mathematics.Complexity.Karp21NativeFullEdgeFieldInputBoundExact as Fields
import DASHI.Mathematics.Complexity.Karp21NativeWholeGraphEdgeFieldWordBoundExact as OriginalWord

-- Every historical vertex costs its ACTUAL LE address register
-- plus the literal original cut-label Bool bit.
historyPayloadWidth : History.BinaryEndpointHistory → Nat
historyPayloadWidth [] = zero
historyPayloadWidth ((vertex , label) ∷ rest) =
  suc (length vertex) + historyPayloadWidth rest

-- Endpoint bits physically present in still-unconsumed original
-- raw-edge records; signed weight registers are charged separately.
remainingEndpointWidth : List Edge.BinaryRawEdge → Nat
remainingEndpointWidth [] = zero
remainingEndpointWidth (Edge.binary-edge u v token ∷ rest) =
  (length u + length v) + remainingEndpointWidth rest

-- All three source-original physical payload categories present in
-- actual binary cursor states, counting label bits only ONCE.
stateEndpointStorageCapacity : Machine.State → Nat
stateEndpointStorageCapacity
  (Machine.state phase edges bits history ledger threshold) =
  historyPayloadWidth history +
    (remainingEndpointWidth edges + length bits)

-- Actual recordBinaryEndpointPair history payload plus remaining
-- edge/certificate payload has identical total bit capacity.
advanceHistoryEndpointStoragePreserved :
  (u v h e c : Nat) →
  (suc u + (suc v + h)) + (e + c)
    ≡ h + (((u + v) + e) + suc (suc c))
advanceHistoryEndpointStoragePreserved u v h e c =
  solve (u ∷ v ∷ h ∷ e ∷ c ∷ [])

-- ORIGINAL binary reference step, independent of compiled frontier,
-- preserves the capacity exactly even when it rejects or finishes.
originalBinaryStepEndpointCapacityInvariant :
  (state next : Machine.State) →
  Machine.originalBinaryWholeVerifierStep state ≡ just next →
  stateEndpointStorageCapacity next ≡ stateEndpointStorageCapacity state
originalBinaryStepEndpointCapacityInvariant
  (Machine.state Machine.accepted es bits hist ledger threshold) next ()
originalBinaryStepEndpointCapacityInvariant
  (Machine.state Machine.rejected es bits hist ledger threshold) next ()
originalBinaryStepEndpointCapacityInvariant
  (Machine.state Machine.active [] [] hist ledger threshold) next step
  with DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact.meetsOriginalPositiveThreshold ledger threshold
... | true with step
... | refl = refl
... | false with step
... | refl = refl
originalBinaryStepEndpointCapacityInvariant
  (Machine.state Machine.active [] (a ∷ bits) hist ledger threshold) next step
  with step
... | refl = refl
originalBinaryStepEndpointCapacityInvariant
  (Machine.state Machine.active (edge ∷ rest) [] hist ledger threshold) next step
  with step
... | refl = refl
originalBinaryStepEndpointCapacityInvariant
  (Machine.state Machine.active (edge ∷ rest) (a ∷ []) hist ledger threshold) next step
  with step
... | refl = refl
originalBinaryStepEndpointCapacityInvariant
  (Machine.state Machine.active
    (Edge.binary-edge u v token ∷ rest)
    (a ∷ b ∷ bits) hist ledger threshold) next step
  with History.endpointConsistentBinary u a hist
     | History.endpointConsistentBinary v b hist
... | false | _ with step
... | refl = refl
... | true | false with step
... | refl = refl
... | true | true with step
... | refl =
  advanceHistoryEndpointStoragePreserved
    (length u) (length v) (historyPayloadWidth hist)
    (remainingEndpointWidth rest) (length bits)

-- SAME first-enabled compiled source step, no substitute machine or
-- chosen arbitrary enabled rule.
firstEnabledBinaryStepEndpointCapacityInvariant :
  (state next : Machine.State) →
  Machine.Compiled.directStep Machine.rules state ≡ just next →
  stateEndpointStorageCapacity next ≡ stateEndpointStorageCapacity state
firstEnabledBinaryStepEndpointCapacityInvariant state next accepted =
  originalBinaryStepEndpointCapacityInvariant state next
    (trans
      (sym (Machine.karpNativeBinaryFirstEnabledSameVerifierStep state))
      accepted)

-- The actual source finite-run iterator conserves this budget for
-- EVERY fuel, including earlier halt and malformed/rejected cases.
actualFirstEnabledFiniteRunEndpointCapacityInvariant :
  (fuel : Nat) (state : Machine.State) →
  stateEndpointStorageCapacity (Run.runBinaryWithFuel fuel state)
    ≡ stateEndpointStorageCapacity state
actualFirstEnabledFiniteRunEndpointCapacityInvariant zero state = refl
actualFirstEnabledFiniteRunEndpointCapacityInvariant (suc fuel) state
  with Machine.Compiled.directStep Machine.rules state in step
... | nothing = refl
... | just next =
  trans
    (actualFirstEnabledFiniteRunEndpointCapacityInvariant fuel next)
    (firstEnabledBinaryStepEndpointCapacityInvariant state next step)

-- Endpoint payload bits constitute a nonnegative part of all actual
-- parsed u/v/signed-w edge registers.
oneEdgeEndpointChargeAtMostAllFields :
  (u v : Word.BitWord)
  (token : DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact.SignedMagnitudeBits) →
  length u + length v
    ≤ Fields.binaryRawEdgeRegisterCharge
        (Edge.binary-edge u v token)
oneEdgeEndpointChargeAtMostAllFields u v token =
  NatP.≤-trans
    (NatP.m≤m+n
      (length u + length v)
      (DASHI.Mathematics.Complexity.Karp21NativeSignedLedgerWidthBudgetExact.signedTokenBitCharge token))
    (NatP.≤-reflexive
      (NatP.+-assoc
        (length u) (length v)
        (DASHI.Mathematics.Complexity.Karp21NativeSignedLedgerWidthBudgetExact.signedTokenBitCharge token)))

remainingEndpointWidthAtMostAllFieldCharge :
  (edges : List Edge.BinaryRawEdge) →
  remainingEndpointWidth edges ≤
    Fields.allBinaryRawEdgeRegisterCharges edges
remainingEndpointWidthAtMostAllFieldCharge [] = NatP.≤-refl
remainingEndpointWidthAtMostAllFieldCharge
  (Edge.binary-edge u v token ∷ rest) =
  NatP.+-mono-≤
    (oneEdgeEndpointChargeAtMostAllFields u v token)
    (remainingEndpointWidthAtMostAllFieldCharge rest)

-- The original graph reader's initial source cursor contains no
-- history at all. Therefore its original endpoint+certificate bits
-- fit within the original two supplied input WORD lengths.
initialBinaryGraphEndpointCapacityBound :
  (word certificate : Word.BitWord) →
  stateEndpointStorageCapacity
    (Machine.initialBinaryWholeWordState word certificate)
    ≤ length word + length certificate
initialBinaryGraphEndpointCapacityBound word certificate
  with Graph.readNativeWholeBinaryGraphWord word in parsed
... | nothing = NatP.m≤m+n zero (length word + length certificate)
... | just (Graph.whole-binary-graph n edges threshold) =
  NatP.+-mono-≤
    (NatP.≤-trans
      (remainingEndpointWidthAtMostAllFieldCharge edges)
      (OriginalWord.actualWholeBinaryGraphEdgeFieldWidthAtMostOriginalWord
        word n threshold edges parsed))
    NatP.≤-refl

-- A useful exact output bound on the LIVE chronological endpoint
-- history of the actual source machine, after its finite run.
-- This is the real F2.2 endpoint-history source-input charge.
actualBinaryFirstEnabledEndpointHistoryFitsInputs :
  (word certificate : Word.BitWord) →
  historyPayloadWidth
    (Machine.history
      (Run.runBinaryWithFuel
        (DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryStepPotentialExact.binaryStatePotential
          (Machine.initialBinaryWholeWordState word certificate))
        (Machine.initialBinaryWholeWordState word certificate)))
    ≤ length word + length certificate
actualBinaryFirstEnabledEndpointHistoryFitsInputs word certificate =
  NatP.≤-trans
    (NatP.m≤m+n
      (historyPayloadWidth
        (Machine.history (Run.runBinaryWithFuel
          (DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryStepPotentialExact.binaryStatePotential
            (Machine.initialBinaryWholeWordState word certificate))
          (Machine.initialBinaryWholeWordState word certificate))))
      (remainingEndpointWidth
        (Machine.edges (Run.runBinaryWithFuel
          (DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryStepPotentialExact.binaryStatePotential
            (Machine.initialBinaryWholeWordState word certificate))
          (Machine.initialBinaryWholeWordState word certificate))) +
       length (Machine.bits (Run.runBinaryWithFuel
          (DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryStepPotentialExact.binaryStatePotential
            (Machine.initialBinaryWholeWordState word certificate))
          (Machine.initialBinaryWholeWordState word certificate)))))
    (NatP.≤-trans
      (NatP.≤-reflexive
        (sym (actualFirstEnabledFiniteRunEndpointCapacityInvariant
          (DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryStepPotentialExact.binaryStatePotential
            (Machine.initialBinaryWholeWordState word certificate))
          (Machine.initialBinaryWholeWordState word certificate))))
      (initialBinaryGraphEndpointCapacityBound word certificate))
