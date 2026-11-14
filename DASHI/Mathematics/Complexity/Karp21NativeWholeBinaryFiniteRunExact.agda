module DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryFiniteRunExact where

------------------------------------------------------------------------
-- D2/F2: actual FIRST-ENABLED binary N21 machine reaches a halted
-- state using no more than the initial remaining-edge-count+1 rule
-- firings. This is a theorem ABOUT THE EXECUTABLE SOURCE RUN, not
-- a proxy original Nat cursor or an assumed machine oracle.
--
-- It is NOT the physical bit-Turing-machine clock: a single source
-- transition can scan historical endpoints, perform ripple additions,
-- and allocate/move bit-list cells. Those costs remain F1/F3/F4.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (length)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryPriorityMachineExact as Machine
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryStepPotentialExact as Potential
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointHistoryExact as History
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive

-- Execute exactly the real first-enabled rule choice, or stop if no
-- such rule exists. Fuel is the machine-run bound, never a decoded
-- gamma endpoint or graph vertex magnitude.
runBinaryWithFuel : Nat → Machine.State → Machine.State
runBinaryWithFuel zero s = s
runBinaryWithFuel (suc fuel) s
  with Machine.Compiled.directStep Machine.rules s
... | nothing = s
... | just next = runBinaryWithFuel fuel next

-- Accepted/rejected states have no enabled rule, and EVERY active
-- state has at least the fallback reject rule. This is stronger than
-- assuming that a cached frontier always has something enabled.
noBinaryFirstEnabledStepImpliesHalt :
  (s : Machine.State) →
  Machine.Compiled.directStep Machine.rules s ≡ nothing →
  Potential.binaryStatePotential s ≡ zero
noBinaryFirstEnabledStepImpliesHalt
  (Machine.state Machine.accepted es bits hist ledger w) noStep = refl
noBinaryFirstEnabledStepImpliesHalt
  (Machine.state Machine.rejected es bits hist ledger w) noStep = refl
noBinaryFirstEnabledStepImpliesHalt
  (Machine.state Machine.active [] [] hist ledger w) noStep
  with Positive.meetsOriginalPositiveThreshold ledger w
... | true with noStep
... | ()
... | false with noStep
... | ()
noBinaryFirstEnabledStepImpliesHalt
  (Machine.state Machine.active [] (b ∷ bits) hist ledger w) ()
noBinaryFirstEnabledStepImpliesHalt
  (Machine.state Machine.active (edge ∷ rest) [] hist ledger w) ()
noBinaryFirstEnabledStepImpliesHalt
  (Machine.state Machine.active (edge ∷ rest) (a ∷ []) hist ledger w) ()
noBinaryFirstEnabledStepImpliesHalt
  (Machine.state Machine.active
    (Edge.binary-edge u v token ∷ rest)
    (a ∷ b ∷ bits) hist ledger w) noStep
  with History.endpointConsistentBinary u a hist
     | History.endpointConsistentBinary v b hist
... | false | _ with noStep
... | ()
... | true | false with noStep
... | ()
... | true | true with noStep
... | ()

-- Potential zero implies either accepted or rejected; it is not an
-- active empty-edge state, whose potential is one until terminal
-- positive threshold/rejection has actually been checked.
potentialBelowZero :
  (s : Machine.State) →
  Potential.binaryStatePotential s ≤ zero →
  Potential.binaryStatePotential s ≡ zero
potentialBelowZero
  (Machine.state Machine.active es bits hist ledger w) ()
potentialBelowZero
  (Machine.state Machine.accepted es bits hist ledger w) proof = refl
potentialBelowZero
  (Machine.state Machine.rejected es bits hist ledger w) proof = refl

sucBoundPeel :
  (x bound : Nat) → suc x ≤ suc bound → x ≤ bound
sucBoundPeel x bound (s≤s proof) = proof

-- A source transition strictly spends the finite potential. So a
-- run with fuel >= initial potential cannot remain active.
binaryRunFuelReachesHalt :
  (fuel : Nat) (s : Machine.State) →
  Potential.binaryStatePotential s ≤ fuel →
  Potential.binaryStatePotential (runBinaryWithFuel fuel s) ≡ zero
binaryRunFuelReachesHalt zero s bounded =
  potentialBelowZero s bounded
binaryRunFuelReachesHalt (suc fuel) s bounded
  with Machine.Compiled.directStep Machine.rules s in nextStep
... | nothing = noBinaryFirstEnabledStepImpliesHalt s nextStep
... | just next =
  binaryRunFuelReachesHalt fuel next
    (sucBoundPeel
      (Potential.binaryStatePotential next) fuel
      (NatP.≤-trans
        (Potential.karpNativeBinaryFirstEnabledStrictPotential
          s next nextStep)
        bounded))

-- Concrete original binary whole-graph run, not just step potential:
-- at most (number of source binary parsed edges)+1 first-enabled
-- transitions can actually occur. If graph parsing fails, the initial
-- state is already rejected and potential zero.
binaryRunTerminatesWithinOriginalEdgeCountPlusOne :
  (s : Machine.State) →
  Potential.binaryStatePotential
    (runBinaryWithFuel (Potential.binaryStatePotential s) s)
    ≡ zero
binaryRunTerminatesWithinOriginalEdgeCountPlusOne s =
  binaryRunFuelReachesHalt
    (Potential.binaryStatePotential s) s NatP.≤-refl
