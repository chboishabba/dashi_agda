{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.FiniteContinuityResidualExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Physics.Semiconductor.Device.ComputedFiniteDeviceCellExact as Cell

------------------------------------------------------------------------
-- FINITE STEADY-STATE CONTINUITY RESIDUAL
--
-- The earlier residual-driven owner used the scalar target Jn + Jp = 13.
-- This owner resolves that target into two independently accounted current
-- coordinates on the same already-computed cell:
--
--   electron current excess above the admitted terminal electron flow, and
--   hole current deficit below the admitted terminal hole flow.
--
-- The terminal values are still synthetic finite-fixture boundary data.  The
-- gain is structural: closure now means two current-balance coordinates vanish,
-- rather than one unexplained scalar total-current target being matched.
------------------------------------------------------------------------

terminalElectronCurrent : Nat
terminalElectronCurrent = 10

terminalHoleCurrent : Nat
terminalHoleCurrent = 3

record ContinuityResidual : Set where
  constructor mkContinuityResidual
  field
    electronExcess : Nat
    holeDeficit : Nat

open ContinuityResidual public

residualAt : Cell.SourceCharge → ContinuityResidual
residualAt Cell.q1 = mkContinuityResidual 4 2
residualAt Cell.q3 = mkContinuityResidual 2 1
residualAt Cell.q5 = mkContinuityResidual 0 0

------------------------------------------------------------------------
-- Exact accounting against the currents already computed by solveCell.
------------------------------------------------------------------------

electronContinuityAccounting :
  (q : Cell.SourceCharge) →
  terminalElectronCurrent + electronExcess (residualAt q)
    ≡ Cell.electronCurrent q
electronContinuityAccounting Cell.q1 = refl
electronContinuityAccounting Cell.q3 = refl
electronContinuityAccounting Cell.q5 = refl

holeContinuityAccounting :
  (q : Cell.SourceCharge) →
  Cell.holeCurrent q + holeDeficit (residualAt q)
    ≡ terminalHoleCurrent
holeContinuityAccounting Cell.q1 = refl
holeContinuityAccounting Cell.q3 = refl
holeContinuityAccounting Cell.q5 = refl

residualScore : Cell.SourceCharge → Nat
residualScore q =
  electronExcess (residualAt q) +
  holeDeficit (residualAt q)

q1ResidualScore : residualScore Cell.q1 ≡ 6
q1ResidualScore = refl

q3ResidualScore : residualScore Cell.q3 ≡ 3
q3ResidualScore = refl

q5ResidualScore : residualScore Cell.q5 ≡ 0
q5ResidualScore = refl

------------------------------------------------------------------------
-- Closure is coordinate-wise, not inferred merely from a scalar label.
------------------------------------------------------------------------

data ContinuityClosed : Cell.SourceCharge → Set where
  q5ContinuityClosed : ContinuityClosed Cell.q5

closedElectronExcessZero :
  (q : Cell.SourceCharge) →
  ContinuityClosed q →
  electronExcess (residualAt q) ≡ 0
closedElectronExcessZero Cell.q5 q5ContinuityClosed = refl

closedHoleDeficitZero :
  (q : Cell.SourceCharge) →
  ContinuityClosed q →
  holeDeficit (residualAt q) ≡ 0
closedHoleDeficitZero Cell.q5 q5ContinuityClosed = refl

closedScoreZero :
  (q : Cell.SourceCharge) →
  ContinuityClosed q →
  residualScore q ≡ 0
closedScoreZero Cell.q5 q5ContinuityClosed = refl

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

data PhysicalContinuityLeaf : Set where
  SignedElectronCurrentOrientation : PhysicalContinuityLeaf
  SignedHoleCurrentOrientation : PhysicalContinuityLeaf
  ContactFluxBoundaryCondition : PhysicalContinuityLeaf
  GenerationRecombinationSource : PhysicalContinuityLeaf
  DiscreteCurrentDivergence : PhysicalContinuityLeaf
  TimeDerivativeCarrierStorage : PhysicalContinuityLeaf
  PhysicalContinuityResidual : PhysicalContinuityLeaf

-- Firewalls:
-- terminal current codes 10 and 3 != measured/physical contact currents.
-- finite excess/deficit accounting != a PDE continuity discretization.
-- zero finite residual coordinates != physical steady-state device validation.
