module DASHI.Physics.Foundations.CasimirFiniteDiskGravityProxyValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CasimirFiniteDiskGravityProxyReceiptExact as Proxy

finite-disk-proxy-executed : Proxy.finiteDiskWeakFieldProxyPaid Proxy.canonicalCasimirFiniteDiskGravityProxyBoundary ≡ true
finite-disk-proxy-executed = refl

finite-gr-still-open : Proxy.finitePlateGRSolutionPaid Proxy.canonicalCasimirFiniteDiskGravityProxyBoundary ≡ false
finite-gr-still-open = refl
