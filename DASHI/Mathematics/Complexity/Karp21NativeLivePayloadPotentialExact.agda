module DASHI.Mathematics.Complexity.Karp21NativeLivePayloadPotentialExact where

------------------------------------------------------------------------
-- F2.2: ONE SAME-STATE LIVE BINARY PAYLOAD POTENTIAL, actual N21
-- first-enabled source machine, NOT an independently assembled
-- token-list/edge-list/oracle.
--
-- The potential counts the literal payload lengths held in the real
-- State:  historical endpoint addresses and labels; remaining
-- original binary u/v/signed-w fields; remaining certificate bits;
-- and the two signed ripple-accumulator registers.
--
-- An ACTUAL successful advance consumes u,v, signed w and two
-- certificate bits, records u,v plus their labels, and inserts w in
-- the appropriate ripple lane iff selected. The original add-width
-- lemma proves that all of that cannot increase this potential.
-- Reject and finish preserve it.
--
-- This is payload length only. Physical cons/pointer/tag cells,
-- persistent sharing, parser temporaries, copying, tape head motion
-- and actual bit-TM clocks remain independent unproved gates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (length)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Data.Nat.Tactic.RingSolver using (solve)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Boolean
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointHistoryExact as History
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryPriorityMachineExact as Machine
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryFiniteRunExact as Run
import DASHI.Mathematics.Complexity.Karp21NativeSignedLedgerWidthBudgetExact as LedgerWidth
import DASHI.Mathematics.Complexity.Karp21NativeFullEdgeFieldInputBoundExact as EdgeWidth
import DASHI.Mathematics.Complexity.Karp21NativeEndpointHistoryConservationExact as HistoryWidth
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive

-- All source SAME-STATE binary payload registers, NOT original Nat/ℤ.
stateLivePayload : Machine.State → Nat
stateLivePayload
  (Machine.state phase edges certificate history ledger threshold) =
  HistoryWidth.historyPayloadWidth history +
    (EdgeWidth.allBinaryRawEdgeRegisterCharges edges
      + length certificate)
    + LedgerWidth.actualLedgerWidth ledger

-- The actual runtime selection operation never grows the two-lane
-- ledger by more than the exact signed-weight register it consumes.
actualAdvanceLedgerWidthCharge :
  (a b : Bool) (u v : Word.BitWord)
  (token : Signed.SignedMagnitudeBits)
  (ledger : Ledger.SignedLedger) →
  LedgerWidth.actualLedgerWidth
    (Machine.addSelectedBinaryToken a b
      (Edge.binary-edge u v token) ledger)
    ≤ LedgerWidth.actualLedgerWidth ledger
       + LedgerWidth.signedTokenBitCharge token
actualAdvanceLedgerWidthCharge a b u v token ledger
  with Boolean.boolEqual a b
... | true =
  NatP.m≤m+n
    (LedgerWidth.actualLedgerWidth ledger)
    (LedgerWidth.signedTokenBitCharge token)
... | false =
  LedgerWidth.actualInsertSignedWidthBound token ledger

-- The arithmetic cost of moving two endpoint addresses plus two
-- labels into history while spending the original signed-weight
-- token and source certificate bits, including a possible carry.
advanceLivePayloadRearrange :
  (u v w h e c l : Nat) →
  (suc u + (suc v + h)) + (e + c) + (l + w)
    ≡ h + ((u + (v + w) + e) + suc (suc c)) + l
advanceLivePayloadRearrange u v w h e c l =
  solve (u ∷ v ∷ w ∷ h ∷ e ∷ c ∷ l ∷ [])

-- This is a theorem on the ACTUAL original-wire next-state function,
-- including all invalid/short certificate rejection and W terminal
-- cases, not just a result about chosen hypothetical edges.
originalBinaryStepLivePayloadNonincreasing :
  (before after : Machine.State) →
  Machine.originalBinaryWholeVerifierStep before ≡ just after →
  stateLivePayload after ≤ stateLivePayload before
originalBinaryStepLivePayloadNonincreasing
  (Machine.state Machine.accepted edges bits hist ledger w) after ()
originalBinaryStepLivePayloadNonincreasing
  (Machine.state Machine.rejected edges bits hist ledger w) after ()
originalBinaryStepLivePayloadNonincreasing
  (Machine.state Machine.active [] [] hist ledger w) after step
  with Positive.meetsOriginalPositiveThreshold ledger w
... | true with step
... | refl = NatP.≤-refl
... | false with step
... | refl = NatP.≤-refl
originalBinaryStepLivePayloadNonincreasing
  (Machine.state Machine.active [] (a ∷ bits) hist ledger w) after step
  with step
... | refl = NatP.≤-refl
originalBinaryStepLivePayloadNonincreasing
  (Machine.state Machine.active (edge ∷ rest) [] hist ledger w) after step
  with step
... | refl = NatP.≤-refl
originalBinaryStepLivePayloadNonincreasing
  (Machine.state Machine.active (edge ∷ rest) (a ∷ []) hist ledger w) after step
  with step
... | refl = NatP.≤-refl
originalBinaryStepLivePayloadNonincreasing
  (Machine.state Machine.active
    (Edge.binary-edge u v token ∷ rest)
    (a ∷ b ∷ bits) hist ledger w) after step
  with History.endpointConsistentBinary u a hist
     | History.endpointConsistentBinary v b hist
... | false | _ with step
... | refl = NatP.≤-refl
... | true | false with step
... | refl = NatP.≤-refl
... | true | true with step
... | refl =
  NatP.≤-trans
    (NatP.+-mono-≤ NatP.≤-refl
      (actualAdvanceLedgerWidthCharge a b u v token ledger))
    (NatP.≤-reflexive
      (advanceLivePayloadRearrange
        (length u) (length v)
        (LedgerWidth.signedTokenBitCharge token)
        (HistoryWidth.historyPayloadWidth hist)
        (EdgeWidth.allBinaryRawEdgeRegisterCharges rest)
        (length bits) (LedgerWidth.actualLedgerWidth ledger)))

-- Real ordered first-enabled compiled decision, no independent rule
-- selection or conditional recurrence.
firstEnabledBinaryStepLivePayloadNonincreasing :
  (before after : Machine.State) →
  Machine.Compiled.directStep Machine.rules before ≡ just after →
  stateLivePayload after ≤ stateLivePayload before
firstEnabledBinaryStepLivePayloadNonincreasing before after step =
  originalBinaryStepLivePayloadNonincreasing before after
    (trans
      (sym (Machine.karpNativeBinaryFirstEnabledSameVerifierStep before))
      step)

-- All finite prefixes of ACTUAL first-enabled execution preserve the
-- live source payload upper bound, even on rejection and early halt.
actualFirstEnabledRunLivePayloadBound :
  (fuel : Nat) (state : Machine.State) →
  stateLivePayload (Run.runBinaryWithFuel fuel state)
    ≤ stateLivePayload state
actualFirstEnabledRunLivePayloadBound zero state = NatP.≤-refl
actualFirstEnabledRunLivePayloadBound (suc fuel) state
  with Machine.Compiled.directStep Machine.rules state in step
... | nothing = NatP.≤-refl
... | just next =
  NatP.≤-trans
    (actualFirstEnabledRunLivePayloadBound fuel next)
    (firstEnabledBinaryStepLivePayloadNonincreasing state next step)
