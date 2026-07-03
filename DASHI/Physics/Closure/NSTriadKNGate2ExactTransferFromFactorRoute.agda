module DASHI.Physics.Closure.NSTriadKNGate2ExactTransferFromFactorRoute where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import DASHI.Physics.Closure.ExactKNAOperatorTransferBase
  using (ExactKNAOperatorTransferModel)
open import DASHI.Physics.Closure.NSTriadKNGate2ExactFactorRouteHypotheses
  using (NSTriadKNGate2ExactFactorRouteHypotheses)
open import DASHI.Physics.Closure.NSTriadKNGate2ExactKNAOperatorTransfer
  using ( exactKNAExtremizerAwareConditionalBound
        )

----------------------------------------------------------------------
-- Exact-transfer bridge from the directional factor route.
--
-- The factor-route package is the sharp source-side certificate for the
-- surviving Gate 2 transfer strategy.  The exact-transfer model is the
-- theorem-facing true-carrier surface.  This package records that both
-- layers are present simultaneously, together with the theorem-facing
-- exact K_N(A) quarter bound.  The remaining analytic burden is then to
-- instantiate both layers on the actual NS carrier, not to invent a new
-- transfer mechanism.

canonicalBoundaryText : String
canonicalBoundaryText =
  "Exact transfer from factor-route package: once the true carrier supplies the exact K_N(A) transfer witnesses and the directional factor-route source certificate, the theorem-facing exact K_N(A) quarter bound is carried as the true-carrier transfer input for Gate 2."

record NSTriadKNGate2ExactTransferFromFactorRoute : Setω where
  constructor mkNSTriadKNGate2ExactTransferFromFactorRoute
  field
    exactTransferModel :
      ExactKNAOperatorTransferModel

    boundaryText : String
    boundaryTextIsCanonical :
      boundaryText ≡ canonicalBoundaryText

    factorRouteHypotheses :
      NSTriadKNGate2ExactFactorRouteHypotheses

    schurLinearityTransferWitness :
      ExactKNAOperatorTransferModel.schurLinearityTransfer
        exactTransferModel

    exactRestrictionIdentityWitness :
      ExactKNAOperatorTransferModel.exactRestrictionIdentity
        exactTransferModel

    directionalTransportBoundWitness :
      ExactKNAOperatorTransferModel.directionalTransportBound
        exactTransferModel

    subcriticalDirectionalBudgetWitness :
      ExactKNAOperatorTransferModel.subcriticalDirectionalBudget
        exactTransferModel

    exactTransferQuarterBound :
      ExactKNAOperatorTransferModel._≤_ exactTransferModel
        (ExactKNAOperatorTransferModel.exact-kna-ratio exactTransferModel)
        (ExactKNAOperatorTransferModel.one-quarter exactTransferModel)

    packageInstalled : Bool
    packageInstalledIsTrue :
      packageInstalled ≡ true

    hypothesesAreAnalyticNotYetGeneralNS : Bool
    hypothesesAreAnalyticNotYetGeneralNSIsTrue :
      hypothesesAreAnalyticNotYetGeneralNS ≡ true

    exactTransferFromFactorRouteProved : Bool
    exactTransferFromFactorRouteProvedIsFalse :
      exactTransferFromFactorRouteProved ≡ false

open NSTriadKNGate2ExactTransferFromFactorRoute public

mkExactTransferFromFactorRouteConsequences :
  (m : ExactKNAOperatorTransferModel) →
  ExactKNAOperatorTransferModel._≤_ m
    (ExactKNAOperatorTransferModel.exact-kna-ratio m)
    (ExactKNAOperatorTransferModel.one-quarter m)
mkExactTransferFromFactorRouteConsequences =
  exactKNAExtremizerAwareConditionalBound
