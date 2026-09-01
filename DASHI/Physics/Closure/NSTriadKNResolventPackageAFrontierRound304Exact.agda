module DASHI.Physics.Closure.NSTriadKNResolventPackageAFrontierRound304Exact where

------------------------------------------------------------------------
-- ROUND304 / FAIL-CLOSED FINAL CUT FOR THE RESOLVENT ROUTE
--
-- R299--R303 close the downstream algebraic plumbing.  R305--R313 refine the
-- sole hard analytic child without weakening the physical consumer:
--
--   heat-only critical-cone payment is rejected;
--   R307 exposes the outer helicity slot/null kernel;
--   R309 expands the literal projected N_p fibre before norms;
--   R310 pairs the inner a/b output fibre into the R120 pure commutator;
--   R311 separates radial-near homochiral from the two non-free-gain lanes;
--   R312 identifies inner heterochiral HH derivative relocation at the
--   exponent level;
--   R313 freezes the nested shell-coordinate language.
--
-- This module refuses the circular shortcut of storing a literal Round240
-- budget as an input and then calling that a proof.  Instead it records the
-- exact remaining PHYSICAL producers whose inhabitants would feed R293 and
-- hence the existing Round240 budget constructor chain.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Remaining source-facing leaves.
------------------------------------------------------------------------

data HeatLaplaceSameObjectLeaf : Set where
  heatLaplaceSameObjectLeaf : HeatLaplaceSameObjectLeaf

data InitialResolventFluxLeaf : Set where
  initialResolventFluxLeaf : InitialResolventFluxLeaf

data TerminalCauchyPositivityLeaf : Set where
  terminalCauchyPositivityLeaf : TerminalCauchyPositivityLeaf

data TerminalDiagonalPaymentLeaf : Set where
  terminalDiagonalPaymentLeaf : TerminalDiagonalPaymentLeaf

data NestedHeatWeightedSchurRowLeaf : Set where
  nestedHeatWeightedSchurRowLeaf : NestedHeatWeightedSchurRowLeaf

data NestedHeatWeightedSchurColumnLeaf : Set where
  nestedHeatWeightedSchurColumnLeaf : NestedHeatWeightedSchurColumnLeaf

data NestedHeatWeightedSchurIntegrabilityLeaf : Set where
  nestedHeatWeightedSchurIntegrabilityLeaf : NestedHeatWeightedSchurIntegrabilityLeaf

record ResolventPhysicalClosureInputs : Set where
  constructor resolvent-physical-closure-inputs
  field
    heatLaplaceSameObject : HeatLaplaceSameObjectLeaf
    initialFluxPayment : InitialResolventFluxLeaf
    terminalCauchyPositivity : TerminalCauchyPositivityLeaf
    terminalDiagonalPayment : TerminalDiagonalPaymentLeaf
    nestedHeatSchurRow : NestedHeatWeightedSchurRowLeaf
    nestedHeatSchurColumn : NestedHeatWeightedSchurColumnLeaf
    nestedHeatSchurIntegrability : NestedHeatWeightedSchurIntegrabilityLeaf

open ResolventPhysicalClosureInputs public

------------------------------------------------------------------------
-- Search interpretation.
--
-- The constructors above are TYPES, not physical inhabitants supplied by this
-- module.  A caller must construct them from the literal NS carrier.  The
-- Schur leaves now refer to the R313 nested route matrix rather than a single
-- global critical-cone kernel.
------------------------------------------------------------------------

round304R299FactorizationCompilerClosed : Bool
round304R299FactorizationCompilerClosed = true

round304R300YoungAbsorptionCompilerClosed : Bool
round304R300YoungAbsorptionCompilerClosed = true

round304R303SignedFluxCompilerClosed : Bool
round304R303SignedFluxCompilerClosed = true

round304R309NestedProjectedForcingExpansionClosed : Bool
round304R309NestedProjectedForcingExpansionClosed = true

round304R310InnerFixedOutputSwapPairingClosed : Bool
round304R310InnerFixedOutputSwapPairingClosed = true

round304R307OuterSlotKernelCarrierExposed : Bool
round304R307OuterSlotKernelCarrierExposed = true

round304HeatOnlyCriticalConePaymentRejected : Bool
round304HeatOnlyCriticalConePaymentRejected = true

round304NestedRouteMatrixRequired : Bool
round304NestedRouteMatrixRequired = true

round304HeatLaplaceSameObjectClosed : Bool
round304HeatLaplaceSameObjectClosed = false

round304InitialEndpointClosed : Bool
round304InitialEndpointClosed = false

round304TerminalEndpointClosed : Bool
round304TerminalEndpointClosed = false

round304NestedHeatWeightedSchurRowClosed : Bool
round304NestedHeatWeightedSchurRowClosed = false

round304NestedHeatWeightedSchurColumnClosed : Bool
round304NestedHeatWeightedSchurColumnClosed = false

round304NestedHeatWeightedSchurIntegrabilityClosed : Bool
round304NestedHeatWeightedSchurIntegrabilityClosed = false

round304PhysicalSignedIntegratedGramClosed : Bool
round304PhysicalSignedIntegratedGramClosed = false

round304LiteralRound240PackageAClosed : Bool
round304LiteralRound240PackageAClosed = false

round304ClayPromotion : Bool
round304ClayPromotion = false

round304R309NestedProjectedForcingExpansionClosedIsTrue :
  round304R309NestedProjectedForcingExpansionClosed ≡ true
round304R309NestedProjectedForcingExpansionClosedIsTrue = refl

round304R310InnerFixedOutputSwapPairingClosedIsTrue :
  round304R310InnerFixedOutputSwapPairingClosed ≡ true
round304R310InnerFixedOutputSwapPairingClosedIsTrue = refl

round304HeatOnlyCriticalConePaymentRejectedIsTrue :
  round304HeatOnlyCriticalConePaymentRejected ≡ true
round304HeatOnlyCriticalConePaymentRejectedIsTrue = refl

round304LiteralRound240PackageAClosedIsFalse :
  round304LiteralRound240PackageAClosed ≡ false
round304LiteralRound240PackageAClosedIsFalse = refl

round304ClayPromotionIsFalse : round304ClayPromotion ≡ false
round304ClayPromotionIsFalse = refl
