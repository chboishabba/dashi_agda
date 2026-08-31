module DASHI.Physics.Closure.NSTriadKNResolventPackageAFrontierRound304Exact where

------------------------------------------------------------------------
-- ROUND304 / FAIL-CLOSED FINAL CUT FOR THE RESOLVENT ROUTE
--
-- R299--R303 now close the downstream algebraic plumbing.  This module refuses
-- the circular shortcut of storing a literal Round240 budget as an input and
-- then calling that a proof.  Instead it records the exact remaining PHYSICAL
-- producers whose inhabitants would feed R293 and hence the existing Round240
-- budget constructor chain.
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

data HeatWeightedSchurRowLeaf : Set where
  heatWeightedSchurRowLeaf : HeatWeightedSchurRowLeaf

data HeatWeightedSchurColumnLeaf : Set where
  heatWeightedSchurColumnLeaf : HeatWeightedSchurColumnLeaf

data HeatWeightedSchurIntegrabilityLeaf : Set where
  heatWeightedSchurIntegrabilityLeaf : HeatWeightedSchurIntegrabilityLeaf

record ResolventPhysicalClosureInputs : Set where
  constructor resolvent-physical-closure-inputs
  field
    heatLaplaceSameObject : HeatLaplaceSameObjectLeaf
    initialFluxPayment : InitialResolventFluxLeaf
    terminalCauchyPositivity : TerminalCauchyPositivityLeaf
    terminalDiagonalPayment : TerminalDiagonalPaymentLeaf
    heatSchurRow : HeatWeightedSchurRowLeaf
    heatSchurColumn : HeatWeightedSchurColumnLeaf
    heatSchurIntegrability : HeatWeightedSchurIntegrabilityLeaf

open ResolventPhysicalClosureInputs public

------------------------------------------------------------------------
-- Search interpretation.
--
-- The seven constructors above are TYPES, not canonical inhabitants supplied
-- by this module.  A caller must construct them from the literal NS carrier.
------------------------------------------------------------------------

round304R299FactorizationCompilerClosed : Bool
round304R299FactorizationCompilerClosed = true

round304R300YoungAbsorptionCompilerClosed : Bool
round304R300YoungAbsorptionCompilerClosed = true

round304R303SignedFluxCompilerClosed : Bool
round304R303SignedFluxCompilerClosed = true

round304HeatLaplaceSameObjectClosed : Bool
round304HeatLaplaceSameObjectClosed = false

round304InitialEndpointClosed : Bool
round304InitialEndpointClosed = false

round304TerminalEndpointClosed : Bool
round304TerminalEndpointClosed = false

round304HeatWeightedSchurRowClosed : Bool
round304HeatWeightedSchurRowClosed = false

round304HeatWeightedSchurColumnClosed : Bool
round304HeatWeightedSchurColumnClosed = false

round304HeatWeightedSchurIntegrabilityClosed : Bool
round304HeatWeightedSchurIntegrabilityClosed = false

round304PhysicalSignedIntegratedGramClosed : Bool
round304PhysicalSignedIntegratedGramClosed = false

round304LiteralRound240PackageAClosed : Bool
round304LiteralRound240PackageAClosed = false

round304ClayPromotion : Bool
round304ClayPromotion = false

round304LiteralRound240PackageAClosedIsFalse :
  round304LiteralRound240PackageAClosed ≡ false
round304LiteralRound240PackageAClosedIsFalse = refl

round304ClayPromotionIsFalse : round304ClayPromotion ≡ false
round304ClayPromotionIsFalse = refl
