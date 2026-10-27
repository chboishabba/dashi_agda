module DASHI.Moonshine.OggSSP2B279FirewallValidation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.OggSSP2B279FirewalledCrossPollinationExact as X

scalar279DoesNotPayActualQ10 :
  X.arithmetic279PaysActualQ10 X.canonical279TwoBBoundary ≡ false
scalar279DoesNotPayActualQ10 = refl

scalar279DoesNotPayOuterAction :
  X.arithmetic279PaysOuterActionDescent X.canonical279TwoBBoundary ≡ false
scalar279DoesNotPayOuterAction = refl
