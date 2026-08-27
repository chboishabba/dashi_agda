module DASHI.Interop.SensibLawPressureHealingBridgeExact where

------------------------------------------------------------------------
-- SENSIBLAW RESIDUAL SEVERITY -> DASHI HEALING PRESSURE
--
-- REPOSITORY SOURCES / OWNERS
--
-- `DASHI.Interop.SensibLawResidualLattice` owns the bounded receipt-facing
-- residual chain and its map into `DASHI.Pressure`.
-- `DASHI.Interop.ITIRJoinBridge` owns the UFTC severity-to-pressure adapter.
-- `DASHI.Core.PressureQuadraticHealingExact` owns the product-order healing
-- surface that keeps immediate pressure separate from certified dependency
-- geometry.
--
-- DASHI CONTRIBUTION
--
-- Close the small application bridge needed by candidate repair/healing:
-- receipt-backed residual severity order transports monotonically into the
-- pressure axis.  Therefore a candidate known to be no worse in residual
-- severity is mechanically no worse in the pressure component of the healing
-- preorder.
--
-- This module does NOT parse text, assign residual labels, authorize ontology
-- edits, or assert that pressure alone determines a preferred repair.
------------------------------------------------------------------------

import DASHI.Pressure as Pressure
import DASHI.Interop.ITIRJoinBridge as ITIR
import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Core.PressureQuadraticHealingExact as Healing

residualToPressureMonotone :
  ∀ {left right : Residual.ResidualLevel} →
  Residual._⊑r_ left right →
  Pressure._⊑p_
    (Residual.residualToPressure left)
    (Residual.residualToPressure right)
residualToPressureMonotone = ITIR.severityToPressureMonotone

ResidualActionScore : Set → Set → Set
ResidualActionScore State Action =
  State → Action → Residual.ResidualLevel

residualPressureScore :
  ∀ {State Action : Set} →
  ResidualActionScore State Action →
  Healing.PressureScore State Action
residualPressureScore score state action =
  Residual.residualToPressure (score state action)

NoWorseResidual :
  ∀ {State Action : Set} →
  ResidualActionScore State Action →
  State → Action → Action → Set
NoWorseResidual score state preferred alternative =
  Residual._⊑r_
    (score state preferred)
    (score state alternative)

noWorseResidualGivesNoWorsePressure :
  ∀ {State Action : Set}
    {score : ResidualActionScore State Action}
    {state : State} {preferred alternative : Action} →
  NoWorseResidual score state preferred alternative →
  Healing.NoWorsePressure
    (residualPressureScore score)
    state preferred alternative
noWorseResidualGivesNoWorsePressure = residualToPressureMonotone
