module DASHI.Moonshine.JInvariantEisensteinBishopConvergenceFrontierValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.JInvariantEisensteinBishopConvergenceFrontierExact as P

vendoredBishopIsOwned :
  P.vendoredBishopBackendOwned P.canonicalEisensteinBishopConvergenceFrontier ≡ true
vendoredBishopIsOwned = refl

finiteSumBridgeIsOwned :
  P.finiteSumToBishopSeriesBridgeOwned P.canonicalEisensteinBishopConvergenceFrontier ≡ true
finiteSumBridgeIsOwned = refl

absoluteToLimitCompilerIsOwned :
  P.absoluteConvergenceToLimitCompilerOwned P.canonicalEisensteinBishopConvergenceFrontier ≡ true
absoluteToLimitCompilerIsOwned = refl

complexCarrierLiftIsStillUnpaid :
  P.constructedComplexComponentwiseConvergenceOwned P.canonicalEisensteinBishopConvergenceFrontier ≡ false
complexCarrierLiftIsStillUnpaid = refl

e4MajorantIsStillUnpaid :
  P.e4ConcreteAbsoluteConvergenceOwned P.canonicalEisensteinBishopConvergenceFrontier ≡ false
e4MajorantIsStillUnpaid = refl

e6MajorantIsStillUnpaid :
  P.e6ConcreteAbsoluteConvergenceOwned P.canonicalEisensteinBishopConvergenceFrontier ≡ false
e6MajorantIsStillUnpaid = refl

analyticSameObjectIsStillUnpaid :
  P.bishopLimitEqualsAnalyticLatticeEisenstein P.canonicalEisensteinBishopConvergenceFrontier ≡ false
analyticSameObjectIsStillUnpaid = refl
