module DASHI.Physics.Closure.NSTriadKNComCommonHatSupportLeafRound58 where

------------------------------------------------------------------------
-- Lightweight B-leaf.
--
-- This is the physical common-hat boundary only.  It intentionally does not
-- import the Cotlar, Gram, or six-three consumer modules.  Once inhabited,
-- it supplies the width-one fact needed by the normalized fibre calculation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSPeriodicNearShellOverlapCount as Hat
import DASHI.Physics.Closure.NSTriadKNComDyadicHatWidthOneRound46Exact as HatWidth

record PhysicalOddPQCommonHatIdentification : Set₁ where
  field
    -- This is the active projection of the literal odd-(P/Q) output fibre.
    -- The public `supportActive` view below is definitionally this field.
    literalOddPQOutputFibreActive : Nat → Nat → Bool
    commonHatSupport : Nat → Nat → Hat.DyadicHatSupport

    leftActiveInCommonHat : ∀ q r →
      literalOddPQOutputFibreActive q r ≡ true →
      q HatWidth.∈ Hat.activeShells (commonHatSupport q r)

    rightActiveInCommonHat : ∀ q r →
      literalOddPQOutputFibreActive q r ≡ true →
      r HatWidth.∈ Hat.activeShells (commonHatSupport q r)

open PhysicalOddPQCommonHatIdentification public

supportActive : PhysicalOddPQCommonHatIdentification → Nat → Nat → Bool
supportActive identification = literalOddPQOutputFibreActive identification

commonHatWidthOne :
  (identification : PhysicalOddPQCommonHatIdentification) →
  ∀ q r →
  literalOddPQOutputFibreActive identification q r ≡ true →
  HatWidth.WithinOne q r
commonHatWidthOne identification q r active =
  HatWidth.activeShellPairWithinOne
    (commonHatSupport identification q r)
    q r
    (leftActiveInCommonHat identification q r active)
    (rightActiveInCommonHat identification q r active)
