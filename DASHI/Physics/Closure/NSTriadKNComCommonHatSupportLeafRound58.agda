module DASHI.Physics.Closure.NSTriadKNComCommonHatSupportLeafRound58 where

------------------------------------------------------------------------
-- Lightweight B-leaf.
--
-- This is the physical common-hat boundary only.  It intentionally does not
-- import the Cotlar, Gram, or six-three consumer modules.  Once inhabited, it
-- supplies the width-one fact needed by the normalized fibre calculation.
--
-- ROUND 62 AUTHORITY CORRECTION
--
-- The field name `literalOddPQOutputFibreActive` predates the literal Round57
-- hard-low-pass kernel and is retained for dependency compatibility.  It MUST
-- NOT be interpreted as the raw statement
--
--   "the same hard-low-pass odd-P/Q entry is active at cutoffs q and r".
--
-- Round62 gives an explicit canonical-selector counterexample: one raw entry
-- with input shell 0 and output shell 3 is active at cutoffs 0 and 2, while no
-- `DyadicHatSupport` can contain both 0 and 2.  Raw nested low-pass activity is
-- therefore wider than one.
--
-- The only mathematically viable meaning of this record is POST-LOCALIZATION
-- pair support: after the physical odd-P/Q commutator has been decomposed into
-- its annular / hatted shell pieces, `literalOddPQOutputFibreActive q r` says
-- that the q and r localized pieces occur in one common hat.  The missing B2
-- producer must construct exactly that localization and this identification.
-- The record itself does not construct the localization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSPeriodicNearShellOverlapCount as Hat
import DASHI.Physics.Closure.NSTriadKNComDyadicHatWidthOneRound46Exact as HatWidth

record PhysicalOddPQCommonHatIdentification : Set₁ where
  field
    -- POST-LOCALIZATION pair support only.  Do not feed this field the raw
    -- hard-low-pass cutoff activity from Round57.
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
