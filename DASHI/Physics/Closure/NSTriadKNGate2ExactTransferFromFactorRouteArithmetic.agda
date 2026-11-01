module DASHI.Physics.Closure.NSTriadKNGate2ExactTransferFromFactorRouteArithmetic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.Closure.NSTriadKNGate2ExactConditionalArithmetic
  using ( canonicalExactKNAOperatorTransferModel
        ; canonicalSchurLinearityTransfer
        ; canonicalExactRestrictionIdentity
        ; canonicalDirectionalTransportBound
        ; canonicalSubcriticalDirectionalBudget
        )
open import DASHI.Physics.Closure.NSTriadKNGate2ExactFactorRouteArithmetic
  using (canonicalExactFactorRouteHypotheses)
open import DASHI.Physics.Closure.NSTriadKNGate2ExactTransferFromFactorRoute
  using ( NSTriadKNGate2ExactTransferFromFactorRoute
        ; mkNSTriadKNGate2ExactTransferFromFactorRoute
        ; mkExactTransferFromFactorRouteConsequences
        )

----------------------------------------------------------------------
-- Concrete arithmetic inhabitant of the exact-transfer bridge from the
-- factor route.
--
-- This remains seam-local arithmetic, but it packages the exact-transfer
-- theorem-facing quarter bound together with the sharper factor-route
-- source certificate on a single surface.

canonicalExactTransferQuarterBound =
  mkExactTransferFromFactorRouteConsequences
    canonicalExactKNAOperatorTransferModel

canonicalExactTransferFromFactorRoute :
  NSTriadKNGate2ExactTransferFromFactorRoute
canonicalExactTransferFromFactorRoute =
  mkNSTriadKNGate2ExactTransferFromFactorRoute
    canonicalExactKNAOperatorTransferModel
    "Exact transfer from factor-route package: once the true carrier supplies the exact K_N(A) transfer witnesses and the directional factor-route source certificate, the theorem-facing exact K_N(A) quarter bound is carried as the true-carrier transfer input for Gate 2."
    refl
    canonicalExactFactorRouteHypotheses
    canonicalSchurLinearityTransfer
    canonicalExactRestrictionIdentity
    canonicalDirectionalTransportBound
    canonicalSubcriticalDirectionalBudget
    canonicalExactTransferQuarterBound
    true
    refl
    true
    refl
    false
    refl
