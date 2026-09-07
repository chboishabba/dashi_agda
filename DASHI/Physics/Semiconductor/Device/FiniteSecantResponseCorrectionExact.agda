{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.FiniteSecantResponseCorrectionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Bool using (false)

import DASHI.Algebra.Jacobian.InvertibilityStrata as Jacobian
import DASHI.Physics.Semiconductor.Device.ComputedFiniteDeviceCellExact as Cell
import DASHI.Physics.Semiconductor.Device.FiniteContinuityResidualExact as Continuity

------------------------------------------------------------------------
-- FINITE SECANT RESPONSE
--
-- On the admitted source family q1 -> q3 -> q5, each charge-coordinate rise of
-- two units lowers the continuity residual score by three units:
--
--   charge:   1 -> 3 -> 5
--   residual: 6 -> 3 -> 0
--
-- This is an exact finite response law on this fixture.  It is not a physical
-- semiconductor Jacobian and is not promoted to a derivative on an ambient
-- continuous state space.
------------------------------------------------------------------------

data AdjacentSource : Cell.SourceCharge → Cell.SourceCharge → Set where
  q1ToQ3 : AdjacentSource Cell.q1 Cell.q3
  q3ToQ5 : AdjacentSource Cell.q3 Cell.q5

sourceRise :
  ∀ {before after} → AdjacentSource before after → Nat
sourceRise q1ToQ3 = 2
sourceRise q3ToQ5 = 2

residualDrop :
  ∀ {before after} → AdjacentSource before after → Nat
residualDrop q1ToQ3 = 3
residualDrop q3ToQ5 = 3

sourceRiseAccounting :
  ∀ {before after} →
  (step : AdjacentSource before after) →
  Cell.chargeCode before + sourceRise step ≡ Cell.chargeCode after
sourceRiseAccounting q1ToQ3 = refl
sourceRiseAccounting q3ToQ5 = refl

residualDropAccounting :
  ∀ {before after} →
  (step : AdjacentSource before after) →
  Continuity.residualScore after + residualDrop step
    ≡ Continuity.residualScore before
residualDropAccounting q1ToQ3 = refl
residualDropAccounting q3ToQ5 = refl

-- Exact secant response ratio: residual drop / source rise = 3 / 2.
secantResponseLaw :
  ∀ {before after} →
  (step : AdjacentSource before after) →
  residualDrop step * 2 ≡ sourceRise step * 3
secantResponseLaw q1ToQ3 = refl
secantResponseLaw q3ToQ5 = refl

------------------------------------------------------------------------
-- Invert the finite response on the admitted residual scores.
--
-- If the response is 3 residual units per 2 charge units, then a zero-residual
-- correction magnitude delta obeys
--
--   3 * delta = 2 * residual.
--
-- The three admitted residual scores {6,3,0} therefore produce corrections
-- {4,2,0}.  This is an exact inverse-secant fixture, not Newton calculus.
------------------------------------------------------------------------

data AdmittedResidual : Set where
  residual6 residual3 residual0 : AdmittedResidual

residualClass : Cell.SourceCharge → AdmittedResidual
residualClass Cell.q1 = residual6
residualClass Cell.q3 = residual3
residualClass Cell.q5 = residual0

residualClassCode : AdmittedResidual → Nat
residualClassCode residual6 = 6
residualClassCode residual3 = 3
residualClassCode residual0 = 0

residualClassMatchesScore :
  (q : Cell.SourceCharge) →
  residualClassCode (residualClass q) ≡ Continuity.residualScore q
residualClassMatchesScore Cell.q1 = refl
residualClassMatchesScore Cell.q3 = refl
residualClassMatchesScore Cell.q5 = refl

correctionForResidual : AdmittedResidual → Nat
correctionForResidual residual6 = 4
correctionForResidual residual3 = 2
correctionForResidual residual0 = 0

correctionMagnitude : Cell.SourceCharge → Nat
correctionMagnitude q = correctionForResidual (residualClass q)

inverseSecantLaw :
  (q : Cell.SourceCharge) →
  correctionMagnitude q * 3 ≡ Continuity.residualScore q * 2
inverseSecantLaw Cell.q1 = refl
inverseSecantLaw Cell.q3 = refl
inverseSecantLaw Cell.q5 = refl

------------------------------------------------------------------------
-- The corrected source state is determined by the finite inverse-response
-- magnitude on the admitted branch.
------------------------------------------------------------------------

secantCorrectedSource : Cell.SourceCharge → Cell.SourceCharge
secantCorrectedSource Cell.q1 = Cell.q5
secantCorrectedSource Cell.q3 = Cell.q5
secantCorrectedSource Cell.q5 = Cell.q5

correctionMagnitudeAccounting :
  (q : Cell.SourceCharge) →
  Cell.chargeCode q + correctionMagnitude q
    ≡ Cell.chargeCode (secantCorrectedSource q)
correctionMagnitudeAccounting Cell.q1 = refl
correctionMagnitudeAccounting Cell.q3 = refl
correctionMagnitudeAccounting Cell.q5 = refl

secantCorrectionClosesResidual :
  (q : Cell.SourceCharge) →
  Continuity.residualScore (secantCorrectedSource q) ≡ 0
secantCorrectionClosesResidual Cell.q1 = refl
secantCorrectionClosesResidual Cell.q3 = refl
secantCorrectionClosesResidual Cell.q5 = refl

secantCorrectedCell : Cell.SourceCharge → Cell.ComputedCell
secantCorrectedCell q = Cell.solveCell (secantCorrectedSource q)

q1SecantCorrectionRecomputesFixedCell :
  secantCorrectedCell Cell.q1 ≡ Cell.solveCell Cell.q5
q1SecantCorrectionRecomputesFixedCell = refl

q3SecantCorrectionRecomputesFixedCell :
  secantCorrectedCell Cell.q3 ≡ Cell.solveCell Cell.q5
q3SecantCorrectionRecomputesFixedCell = refl

q5SecantCorrectionKeepsFixedCell :
  secantCorrectedCell Cell.q5 ≡ Cell.solveCell Cell.q5
q5SecantCorrectionKeepsFixedCell = refl

------------------------------------------------------------------------
-- Cross-pollination with the existing Jacobian promotion boundary.
--
-- InvertibilityStrata already owns the firewall that local differential/local
-- inverse information does not imply a global inverse.  We instantiate its
-- branch-selection surface for the zero-residual target on this finite branch.
------------------------------------------------------------------------

data DeviceResidualBranch : Set where
  admittedFiniteBranch : DeviceResidualBranch

data ResidualHistoryReceipt : Set where
  finiteResidualHistory : ResidualHistoryReceipt

data ContinuityClosureReceipt : Set where
  finiteContinuityClosure : ContinuityClosureReceipt

zeroResidualBranchSelection :
  Jacobian.BranchSelection
    Cell.SourceCharge Nat DeviceResidualBranch Continuity.residualScore
zeroResidualBranchSelection = record
  { target = 0
  ; branch = admittedFiniteBranch
  ; selectedSource = Cell.q5
  ; selectedSourceMapsToTarget = refl
  ; historyReceipt = ResidualHistoryReceipt
  ; continuityReceipt = ContinuityClosureReceipt
  }

localInverseDoesNotImplyGlobalInverse :
  Jacobian.localImpliesGlobalInverse Jacobian.canonicalPromotionBoundary ≡ false
localInverseDoesNotImplyGlobalInverse =
  Jacobian.canonicalLocalDoesNotImplyGlobal

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

data PhysicalSecantLeaf : Set where
  SignedResidualVectorSpace : PhysicalSecantLeaf
  PhysicalResidualDerivative : PhysicalSecantLeaf
  JacobianNonsingularity : PhysicalSecantLeaf
  DampingOrLineSearch : PhysicalSecantLeaf
  BasinPreservation : PhysicalSecantLeaf
  PhysicalBranchSelection : PhysicalSecantLeaf
  PhysicalNewtonOrGummelStep : PhysicalSecantLeaf

-- Firewalls:
-- exact finite secant ratio 3/2 != a physical Jacobian derivative.
-- inverseSecantLaw on {6,3,0} != global inverse-function authority.
-- branch selection on the finite family != uniqueness of a physical solution.
-- one-step finite residual closure != convergence of a physical device solver.
