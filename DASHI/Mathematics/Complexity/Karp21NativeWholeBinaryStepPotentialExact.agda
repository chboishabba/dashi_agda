module DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryStepPotentialExact where

------------------------------------------------------------------------
-- D2/F2: strict potential of the REAL whole-word binary N21
-- first-enabled machine, rather than earlier Nat-based raw cursor.
--
-- Active states have remaining-edge-count+1 potential; accepted and
-- rejected states have zero. Every actual enabled first-priority step
-- strictly decreases that potential. No rule can execute once halted.
--
-- High-level bound is <= original parsed edge count + 1; this is NOT
-- a bound on actual head moves, allocations, intermediate tape width,
-- parsing or any physical bit-TM instruction count.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just)
open import Data.List.Base using (length)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryPriorityMachineExact as Binary
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointHistoryExact as History
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive

binaryStatePotential : Binary.State → Nat
binaryStatePotential (Binary.state Binary.active edges bits history ledger threshold) =
  suc (length edges)
binaryStatePotential (Binary.state Binary.accepted edges bits history ledger threshold) =
  zero
binaryStatePotential (Binary.state Binary.rejected edges bits history ledger threshold) =
  zero

binaryReferenceStepStrictPotential :
  (s next : Binary.State) →
  Binary.originalBinaryWholeVerifierStep s ≡ just next →
  suc (binaryStatePotential next) ≤ binaryStatePotential s
binaryReferenceStepStrictPotential
  (Binary.state Binary.accepted edges bits hist ledger threshold) next ()
binaryReferenceStepStrictPotential
  (Binary.state Binary.rejected edges bits hist ledger threshold) next ()
binaryReferenceStepStrictPotential
  (Binary.state Binary.active [] [] hist ledger threshold) next eq
  with Positive.meetsOriginalPositiveThreshold ledger threshold
... | true with eq
... | refl = s≤s z≤n
... | false with eq
... | refl = s≤s z≤n
binaryReferenceStepStrictPotential
  (Binary.state Binary.active [] (bit ∷ bits) hist ledger threshold)
  next eq with eq
... | refl = s≤s z≤n
binaryReferenceStepStrictPotential
  (Binary.state Binary.active (edge ∷ rest) [] hist ledger threshold)
  next eq with eq
... | refl = s≤s z≤n
binaryReferenceStepStrictPotential
  (Binary.state Binary.active (edge ∷ rest) (a ∷ []) hist ledger threshold)
  next eq with eq
... | refl = s≤s z≤n
binaryReferenceStepStrictPotential
  (Binary.state Binary.active
    (Edge.binary-edge u v token ∷ rest)
    (a ∷ b ∷ bits) hist ledger threshold)
  next eq
  with History.endpointConsistentBinary u a hist
     | History.endpointConsistentBinary v b hist
... | false | _ with eq
... | refl = s≤s z≤n
... | true | false with eq
... | refl = s≤s z≤n
... | true | true with eq
... | refl = NatP.≤-refl

-- Same bound for the compiled source's genuinely FIRST enabled rule,
-- not an assumed arbitrary enabled operation or a cached heuristic.
karpNativeBinaryFirstEnabledStrictPotential :
  (s next : Binary.State) →
  Binary.Compiled.directStep Binary.rules s ≡ just next →
  suc (binaryStatePotential next) ≤ binaryStatePotential s
karpNativeBinaryFirstEnabledStrictPotential s next transition =
  binaryReferenceStepStrictPotential s next
    (trans
      (sym (Binary.karpNativeBinaryFirstEnabledSameVerifierStep s))
      transition)
