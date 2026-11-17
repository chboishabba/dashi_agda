module DASHI.Arithmetic.TwinPrimeFRACDASHReuseExact where

------------------------------------------------------------------------
-- Reuse the existing paired-prime TAG machine, NOT an invented twin-prime
-- prover.  The FRACDASH paired primes are macro/register representations.
-- Arithmetic twins are two Nat primes separated by 2.  These referents
-- must not be identified without a sound concrete encoding.
--
-- Existing proof owners:
--   DASHI.Arithmetic.TwinPrimeSixWheelExact:
--     finite paired {2,3}-sieve residue classification
--   DASHI.Programmes.FRACDASHPairedPrimeActivityExact:
--     active-tag / first-applicable rule composition
--   DASHI.Programmes.FRACDASHNumericInterpreterTargetExact:
--     semantics of deterministic first-applicable execution
--
-- A concrete machine adapter must prove that active prime-tag selection
-- really corresponds to a local prime-pair sieve survivor.  This module
-- does not manufacture such a witness or establish Nat prime infinitude.
-- The existing SSP15 fixed basis does not cover all primes.  Therefore
-- finite SSP15 valuations cannot be promoted into a complete unbounded
-- sieve for arithmetic twins.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Arithmetic.SixWheelSieveCountExact as Wheel
import DASHI.Arithmetic.TwinPrimeSixWheelExact as Twin
import DASHI.Programmes.FRACDASHPairedPrimeActivityExact as Activity
import DASHI.Programmes.FRACDASHNumericInterpreterTargetExact as Numeric
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed

-- A proof-carrying representation interface, not a concrete instance.
-- It names the bridge needed to compare a source arithmetic residue
-- with the active-tag semantics of a FRACDASH machine step.
record TwinWheelActivityBridge (r : Wheel.Residue6) : Set₁ where
  field
    machine : Activity.PairedPrimeActivityInterface
    sourceState : Activity.State machine
    blockedPrefix : List (Activity.Rule machine)
    chosenRule : Activity.Rule machine
    remainingRules : List (Activity.Rule machine)

    prefixInactive :
      Activity.AllInactive machine sourceState blockedPrefix

    intendedActive :
      Activity.Active machine sourceState
        (Activity.denominatorTag machine chosenRule)

    activeIsGenuineWheelSurvivor :
      Activity.Active machine sourceState
        (Activity.denominatorTag machine chosenRule) →
      Twin.PairWheelSurvivor r

open TwinWheelActivityBridge public

-- Compose two existing proof owners.  The machine step is established
-- only *when* an adapter supplies the prefix and active-tag witnesses.
bridgeChoosesFirstApplicable :
  (r : Wheel.Residue6) →
  (bridge : TwinWheelActivityBridge r) →
  Numeric.FirstApplicableStep
    (Activity.applies (machine bridge))
    (Activity.apply (machine bridge))
    (Numeric.append (blockedPrefix bridge)
      (chosenRule bridge ∷ remainingRules bridge))
    (sourceState bridge)
    (Activity.apply (machine bridge)
      (sourceState bridge) (chosenRule bridge))
bridgeChoosesFirstApplicable r bridge =
  Activity.activityReceiptYieldsFirstApplicableStep
    (machine bridge)
    (sourceState bridge)
    (blockedPrefix bridge)
    (chosenRule bridge)
    (remainingRules bridge)
    (Activity.activePrefixSelectionReceipt
      (prefixInactive bridge)
      (intendedActive bridge))

-- Under the REQUIRED soundness hypothesis, a machine activation
-- can only represent the r5 twin-offset survivor class.
bridgeActivationForcesResidueFive :
  (r : Wheel.Residue6) →
  (bridge : TwinWheelActivityBridge r) →
  r ≡ Wheel.r5
bridgeActivationForcesResidueFive r bridge =
  Twin.pairSurvivorMustBeR5 r
    (activeIsGenuineWheelSurvivor bridge (intendedActive bridge))

-- This is merely the existing selected-prime valuation address.  It
-- is not an arithmetic primality certificate for the represented Nat.
signedPrimeAddress : Signed.SSPPrime → Nat
signedPrimeAddress = Signed.primeValue
