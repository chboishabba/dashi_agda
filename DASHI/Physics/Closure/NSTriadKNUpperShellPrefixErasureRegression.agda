module DASHI.Physics.Closure.NSTriadKNUpperShellPrefixErasureRegression where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNUpperShellPrefixErasureExact as Subject

selectedPrefixErasureClosed :
  Subject.upperShellSelectedBelowPrefixErasureClosed ≡ true
selectedPrefixErasureClosed =
  Subject.upperShellSelectedBelowPrefixErasureClosedIsTrue

dropPrefixErasureClosed :
  Subject.upperShellDropBelowPrefixErasureClosed ≡ true
dropPrefixErasureClosed =
  Subject.upperShellDropBelowPrefixErasureClosedIsTrue
