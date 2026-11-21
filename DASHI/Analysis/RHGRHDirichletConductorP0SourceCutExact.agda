module DASHI.Analysis.RHGRHDirichletConductorP0SourceCutExact where

-- P0 GRH source-first conductor reconciliation.
-- Preserve original primitive-character conductor vs order conductor
-- vs modular level. These are ACTUAL DASHI Dirichlet data owners,
-- not a reconstruction of Mathlib DirichletCharacter / IsPrimitive.
-- Original infinite analytic Dirichlet L-functions, character
-- evaluation and source all-character GRH proof transport remain OPEN.
-- Source-written; Agda kernel validation pending.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Physics.QFT.ConductorVsDiscriminantReceipt as Conductor

-- Selected CM/Eisenstein D=-3 is a primitive character conductor 3
-- but has maximal-order conductor 1. Keep both original source facts.
eisensteinSelectedOrderConductor :
  Conductor.orderConductor Conductor.dMinus3Row ≡ 1
eisensteinSelectedOrderConductor =
  Conductor.orderConductorMatchesOrder Conductor.dMinus3Row

eisensteinSelectedPrimitiveDirichletConductor :
  Conductor.dirichletCharacterConductor Conductor.dMinus3Row ≡ 3
eisensteinSelectedPrimitiveDirichletConductor =
  Conductor.dirichletCharacterConductorMatchesPrimitive
    Conductor.dMinus3Row

-- The D=-12 NON-maximal order has order conductor 2 and primitive
-- quadratic Dirichlet character conductor 3. In particular, the
-- modular/order level 12 is NOT its primitive character conductor.
nonmaximalSelectedOrderConductor :
  Conductor.orderConductor Conductor.dMinus12Row ≡ 2
nonmaximalSelectedOrderConductor =
  Conductor.orderConductorMatchesOrder Conductor.dMinus12Row

nonmaximalSelectedPrimitiveDirichletConductor :
  Conductor.dirichletCharacterConductor Conductor.dMinus12Row ≡ 3
nonmaximalSelectedPrimitiveDirichletConductor =
  Conductor.dirichletCharacterConductorMatchesPrimitive
    Conductor.dMinus12Row

nonmaximalSelectedModularLevel :
  Conductor.modularLevel Conductor.dMinus12Row ≡ 12
nonmaximalSelectedModularLevel =
  Conductor.modularLevelMatchesOrderLevel Conductor.dMinus12Row

nonmaximalCharacterConductorNotModularLevel :
  Conductor.dirichletCharacterConductor Conductor.dMinus12Row
    ≡ Conductor.modularLevel Conductor.dMinus12Row → ⊥
nonmaximalCharacterConductorNotModularLevel ()

-- A second important counterexample to conflating maximal-order
-- conductor 1 with the primitive quadratic Dirichlet modulus.
dMinus8SelectedOrderConductor :
  Conductor.orderConductor Conductor.dMinus8Row ≡ 1
dMinus8SelectedOrderConductor =
  Conductor.orderConductorMatchesOrder Conductor.dMinus8Row

dMinus8PrimitiveDirichletConductor :
  Conductor.dirichletCharacterConductor Conductor.dMinus8Row ≡ 8
dMinus8PrimitiveDirichletConductor =
  Conductor.dirichletCharacterConductorMatchesPrimitive
    Conductor.dMinus8Row

-- A pair of discriminants can give the SAME primitive Dirichlet
-- conductor but different order conductors and modular levels.
samePrimitiveConductorDMinus3AndDMinus12 :
  Conductor.dirichletCharacterConductor Conductor.dMinus3Row
    ≡ Conductor.dirichletCharacterConductor Conductor.dMinus12Row
samePrimitiveConductorDMinus3AndDMinus12 = refl

differentOrderConductorDMinus3AndDMinus12 :
  Conductor.orderConductor Conductor.dMinus3Row
    ≡ Conductor.orderConductor Conductor.dMinus12Row → ⊥
differentOrderConductorDMinus3AndDMinus12 ()

-- This is NOT a Mathlib Dirichlet character or an automorphic lift.
-- The P0 proof owner remains the pinned Lean fork's original
-- UpperTheory.EveryCharacter → Dirichlet L-function theorems.
