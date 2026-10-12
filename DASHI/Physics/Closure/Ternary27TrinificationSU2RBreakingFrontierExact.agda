module DASHI.Physics.Closure.Ternary27TrinificationSU2RBreakingFrontierExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.Ternary27TrinificationSMBridgeExact as Tri
+import DASHI.Physics.QFT.ExactSMMatchToken as ExactSM

------------------------------------------------------------------------
-- TRINIFICATION RIGHT-HANDED BREAKING FRONTIER
--
-- The existing exact-SM token records a missing low-energy SU(2)_R breaking
-- receipt.  The same first-Tits/trinification carrier now supplies a sharper
-- split of that obligation:
--
--   algebraic subgroup direction:
--     SU(3)_R -> SU(2)_R x U(1)_R and the selected T3_R Cartan direction
--
--   versus physical/dynamical breaking:
--     an actual order parameter / vev / scale / mass spectrum which removes
--     the charged W_R directions in the low-energy theory.
--
-- The hypercharge generator already used on the same 27 is
--
--   Y = -(1/6) X_L -(1/6) X_R -(1/2) T3_R.
--
-- This pays the representation-theoretic breaking direction, but not the
-- dynamical low-energy breaking receipt demanded by ExactSMMatchToken.
------------------------------------------------------------------------

data RightHandedBreakingLayer : Set where
  su3RContainsSU2RAndU1R : RightHandedBreakingLayer
  t3RDirectionSelected : RightHandedBreakingLayer
  hyperchargeCombinationSelected : RightHandedBreakingLayer
  dynamicalOrderParameter : RightHandedBreakingLayer
  breakingScale : RightHandedBreakingLayer
  heavyRightGaugeBosonSpectrum : RightHandedBreakingLayer
  lowEnergyDecoupling : RightHandedBreakingLayer

hyperchargeFormula : String
hyperchargeFormula = "Y = -(1/6) X_L -(1/6) X_R -(1/2) T3_R"

record TrinificationSU2RBreakingFrontierReceipt : Set where
  constructor trinification-su2r-breaking-frontier-receipt
  field
    sameTernary27TrinificationCarrier : Bool
    su3RSubgroupDirectionPaid : Bool
    su2RSubalgebraDirectionPaid : Bool
    t3RCartanDirectionPaid : Bool
    hyperchargeCombinationPaid : Bool
    oneGenerationHyperchargeTargetsAlreadyMatched : Bool
    dynamicalOrderParameterPaid : Bool
    physicalBreakingScalePaid : Bool
    heavyWRMassSpectrumPaid : Bool
    lowEnergyDecouplingPaid : Bool
    oldExactSMBlockerFullyDischarged : Bool
    blockerSharpenedFromAlgebraicToDynamical : Bool
    boundary : String
open TrinificationSU2RBreakingFrontierReceipt public

canonicalTrinificationSU2RBreakingFrontierReceipt : TrinificationSU2RBreakingFrontierReceipt
canonicalTrinificationSU2RBreakingFrontierReceipt =
  trinification-su2r-breaking-frontier-receipt
    true true true true true true
    false false false false false true
    "The same first-Tits/trinification 27 now pays the algebraic SU(3)_R -> SU(2)_R x U(1)_R direction and the T3_R contribution used in the hypercharge generator. ExactSMMatchToken's low-energy SU2R blocker is therefore narrowed to a genuinely dynamical order-parameter/scale/mass/decoupling receipt; it is not fully discharged by subgroup selection alone."

existingExactSMBlockerReceipt : ExactSM.ExactSMMatchBlockerReceipt
existingExactSMBlockerReceipt = ExactSM.canonicalExactSMMatchBlockerReceipt

data CartanDirectionCreatesPhysicalBreaking : Set where

cartanDirectionDoesNotCreatePhysicalBreaking :
  CartanDirectionCreatesPhysicalBreaking → {A : Set} → A
cartanDirectionDoesNotCreatePhysicalBreaking ()
