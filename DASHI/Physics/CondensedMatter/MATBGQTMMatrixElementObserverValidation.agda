module DASHI.Physics.CondensedMatter.MATBGQTMMatrixElementObserverValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.CondensedMatter.MATBGQTMMatrixElementObserverReceiptExact as QTM

observer-executed : QTM.wavefunctionObserverExecutionPaid QTM.canonicalQTMMatrixElementObserverBoundary ≡ true
observer-executed = refl

experimental-fit-open : QTM.experimentalQTMFitPaid QTM.canonicalQTMMatrixElementObserverBoundary ≡ false
experimental-fit-open = refl
