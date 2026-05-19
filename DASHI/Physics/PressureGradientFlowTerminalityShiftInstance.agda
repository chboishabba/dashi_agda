module DASHI.Physics.PressureGradientFlowTerminalityShiftInstance where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (_≤_; _<_; z≤n; s≤s)
open import Data.List.Base using (_∷_)
open import Relation.Nullary using (¬_)

open import DASHI.Physics.Closure.Basin as Basin
open import DASHI.Physics.DashiDynamicsShiftInstance as DDSI
open import DASHI.Physics.DynamicsCollapseDepth as DCD
open import DASHI.Physics.DynamicsCollapseDepthMonotone as DCDM
open import DASHI.Physics.DynamicsCollapseDepthPotentialBridge as DCDP
open import DASHI.Physics.DynamicsFixedPointUniqueness as DFPU
open import DASHI.Physics.DynamicsStepCoherence as DSC
open import DASHI.Physics.PressureGradientFlowShiftInstance as PGFSI
open import DASHI.Physics.PressureGradientFlowTerminalityGap as PGFTG
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI

------------------------------------------------------------------------
-- Bounded terminality / attractor package on the three-point shift carrier.
--
-- This module packages the exact finite-carrier facts now available:
--   * every state eventually reaches the held point,
--   * the rank-plus-potential quantity is exactly conserved on the carrier,
--   * the current bounded attractor surface packages convergence and uniqueness,
--   * the held point is the unique zero-potential point.

ShiftHeldStable : PGFSI.ShiftFlowState → Set
ShiftHeldStable s = s ≡ SPTI.shiftHeldExitPoint

ShiftEventuallyHeld : Set
ShiftEventuallyHeld =
  (s : PGFSI.ShiftFlowState) →
  Basin.Eventually PGFSI.shiftFlowEvolve ShiftHeldStable s

ShiftUniqueFixedPoint : Set
ShiftUniqueFixedPoint =
  (s : PGFSI.ShiftFlowState) →
  PGFSI.shiftFlowEvolve s ≡ s →
  s ≡ SPTI.shiftHeldExitPoint

ShiftUniquePotentialMinimum : Set
ShiftUniquePotentialMinimum =
  (s : PGFSI.ShiftFlowState) →
  PGFSI.shiftFlowPotential s ≡ 0 →
  s ≡ SPTI.shiftHeldExitPoint

ShiftConservedQuantityConstant : Set
ShiftConservedQuantityConstant =
  (s : PGFSI.ShiftFlowState) →
  PGFSI.shiftFlowConservedQuantity s ≡ suc (suc zero)

shiftEventuallyHeldWitness : ShiftEventuallyHeld
shiftEventuallyHeldWitness SPTI.shiftStartPoint =
  Basin.later (Basin.later (Basin.now refl))
shiftEventuallyHeldWitness SPTI.shiftNextPoint =
  Basin.later (Basin.now refl)
shiftEventuallyHeldWitness SPTI.shiftHeldExitPoint =
  Basin.now refl

shiftUniqueFixedPointWitness : ShiftUniqueFixedPoint
shiftUniqueFixedPointWitness SPTI.shiftStartPoint ()
shiftUniqueFixedPointWitness SPTI.shiftNextPoint ()
shiftUniqueFixedPointWitness SPTI.shiftHeldExitPoint refl = refl

shiftUniquePotentialMinimumWitness : ShiftUniquePotentialMinimum
shiftUniquePotentialMinimumWitness SPTI.shiftStartPoint ()
shiftUniquePotentialMinimumWitness SPTI.shiftNextPoint ()
shiftUniquePotentialMinimumWitness SPTI.shiftHeldExitPoint refl = refl

shiftConservedQuantityConstantWitness : ShiftConservedQuantityConstant
shiftConservedQuantityConstantWitness SPTI.shiftStartPoint = refl
shiftConservedQuantityConstantWitness SPTI.shiftNextPoint = refl
shiftConservedQuantityConstantWitness SPTI.shiftHeldExitPoint = refl

shiftDynamicsFixedPointUniqueness :
  DFPU.DynamicsFixedPointUniqueness Nat
shiftDynamicsFixedPointUniqueness =
  DFPU.mkDynamicsFixedPointUniqueness
    PGFSI.shiftDynamicsStepCoherence
    shiftUniqueFixedPointWitness

ShiftCollapseDepth : Set
ShiftCollapseDepth =
  PGFSI.ShiftFlowState → Nat

shiftCollapseDepth : ShiftCollapseDepth
shiftCollapseDepth SPTI.shiftStartPoint = suc (suc zero)
shiftCollapseDepth SPTI.shiftNextPoint = suc zero
shiftCollapseDepth SPTI.shiftHeldExitPoint = zero

ShiftCollapseDepthWitness : Set
ShiftCollapseDepthWitness =
  (s : PGFSI.ShiftFlowState) →
  DSC.iterate (shiftCollapseDepth s) PGFSI.shiftFlowEvolve s
    ≡
  SPTI.shiftHeldExitPoint

shiftCollapseDepthWitness : ShiftCollapseDepthWitness
shiftCollapseDepthWitness SPTI.shiftStartPoint = refl
shiftCollapseDepthWitness SPTI.shiftNextPoint = refl
shiftCollapseDepthWitness SPTI.shiftHeldExitPoint = refl

shiftDynamicsCollapseDepth :
  DCD.DynamicsCollapseDepth Nat
shiftDynamicsCollapseDepth =
  DCD.mkDynamicsCollapseDepth
    shiftDynamicsFixedPointUniqueness
    shiftCollapseDepth
    shiftCollapseDepthWitness

ShiftCollapseDepthMonotone : Set
ShiftCollapseDepthMonotone =
  (s : PGFSI.ShiftFlowState) →
  shiftCollapseDepth (PGFSI.shiftFlowEvolve s) ≤ shiftCollapseDepth s

ShiftCollapseDepthStrictOffHeld : Set
ShiftCollapseDepthStrictOffHeld =
  (s : PGFSI.ShiftFlowState) →
  ¬ (s ≡ SPTI.shiftHeldExitPoint) →
  shiftCollapseDepth (PGFSI.shiftFlowEvolve s) < shiftCollapseDepth s

shiftCollapseDepthMonotoneWitness : ShiftCollapseDepthMonotone
shiftCollapseDepthMonotoneWitness SPTI.shiftStartPoint = s≤s z≤n
shiftCollapseDepthMonotoneWitness SPTI.shiftNextPoint = z≤n
shiftCollapseDepthMonotoneWitness SPTI.shiftHeldExitPoint = z≤n

shiftCollapseDepthStrictOffHeldWitness : ShiftCollapseDepthStrictOffHeld
shiftCollapseDepthStrictOffHeldWitness SPTI.shiftStartPoint _ = s≤s (s≤s z≤n)
shiftCollapseDepthStrictOffHeldWitness SPTI.shiftNextPoint _ = s≤s z≤n
shiftCollapseDepthStrictOffHeldWitness SPTI.shiftHeldExitPoint neq = ⊥-elim (neq refl)

shiftCollapseDepthHeldZero : shiftCollapseDepth SPTI.shiftHeldExitPoint ≡ zero
shiftCollapseDepthHeldZero = refl

shiftDynamicsCollapseDepthMonotone :
  DCDM.DynamicsCollapseDepthMonotone Nat
shiftDynamicsCollapseDepthMonotone =
  DCDM.mkDynamicsCollapseDepthMonotone
    shiftDynamicsCollapseDepth
    shiftCollapseDepthMonotoneWitness
    shiftCollapseDepthStrictOffHeldWitness
    shiftCollapseDepthHeldZero

ShiftCollapseDepthPotentialAgreement : Set
ShiftCollapseDepthPotentialAgreement =
  (s : PGFSI.ShiftFlowState) →
  shiftCollapseDepth s ≡ PGFSI.shiftFlowPotential s

shiftCollapseDepthPotentialAgreementWitness :
  ShiftCollapseDepthPotentialAgreement
shiftCollapseDepthPotentialAgreementWitness SPTI.shiftStartPoint = refl
shiftCollapseDepthPotentialAgreementWitness SPTI.shiftNextPoint = refl
shiftCollapseDepthPotentialAgreementWitness SPTI.shiftHeldExitPoint = refl

shiftDynamicsCollapseDepthPotentialBridge :
  DCDP.DynamicsCollapseDepthPotentialBridge Nat
shiftDynamicsCollapseDepthPotentialBridge =
  DCDP.mkDynamicsCollapseDepthPotentialBridge
    shiftDynamicsCollapseDepth
    PGFSI.shiftFlowPotential
    shiftCollapseDepthPotentialAgreementWitness

shiftPressureGradientFlowTerminalityGap :
  PGFTG.PressureGradientFlowTerminalityGap Nat
shiftPressureGradientFlowTerminalityGap =
  record
    { flowGap = PGFSI.shiftPressureGradientFlowGap
    ; eventualHeld = ShiftEventuallyHeld
    ; attractorSurface = shiftDynamicsFixedPointUniqueness
    ; uniquePotentialMinimum = ShiftUniquePotentialMinimum
    ; nonClaimBoundary =
        "Shift terminality seam only"
        ∷ "rank-plus-potential conservation is exact on the current carrier"
        ∷ "eventualHeld is exact on the current three-point carrier only"
        ∷ "attractorSurface packages the finite-carrier uniqueness and iterate-from-2 attractor facts"
        ∷ "uniquePotentialMinimum is a finite-carrier fact only"
        ∷ PGFTG.nonClaimBoundary
            (PGFTG.mkPressureGradientFlowTerminalityGap
              PGFSI.shiftPressureGradientFlowGap
              ShiftEventuallyHeld
              shiftDynamicsFixedPointUniqueness
              ShiftUniquePotentialMinimum)
    }
