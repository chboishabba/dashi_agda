{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3SelectedStateHaarQuadratureExact where

------------------------------------------------------------------------
-- R3 PRESENTATION CUT: FIX THE SELECTED FINITE STATE FAMILY BY CONSTRUCTION.
--
-- The generic physical-Haar compiler allows statesAt(refinement) to vary.  The
-- factorized-density anomaly transport, however, is already formulated on one
-- selected finite state list.  The preferred R3 source package therefore fixes
-- that list at construction time and asks directly for quadrature data whose
-- sum is the sourceExpectation on that list.  No later equality
--
--      statesAt refinement = selectedStates
--
-- is charged.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.CMP119AntigravitySourceExpectationToPhysicalHaarExact as Haar
import DASHI.Physics.Foundations.CMP119CosmologyP3ApproximateExpectationHaarExact as ApproxHaar
import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityApproximationExact as Approx
import DASHI.Physics.YangMills.BalabanCMP119FiniteObservableExpectationConvergenceExact as Expect
import DASHI.Physics.YangMills.BalabanCompactHaarFiniteQuadratureErrorExact as Quad
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq

record SelectedStateCMP119PhysicalHaarQuadrature
    {SlowField Sequence Component Step Cell : Set}
    (approximation :
      Approx.CMP119FactorizedDensityApproximation
        SlowField Sequence Component Step)
    (sequenceLimit : Seq.RealSequenceLimitByVanishingError)
    (states : List SlowField)
    (scale : Nat)
    (observable : SlowField → ℝ) : Set₁ where
  field
    quadratureAt : Nat → Quad.FiniteQuadratureCellError Cell
    physicalHaarExpectation : ℝ

    sourceIntegralIsPhysical :
      ∀ refinement →
      Quad.sourceIntegral (quadratureAt refinement)
      ≡ physicalHaarExpectation

    selectedSourceExpectationIsQuadrature :
      ∀ refinement →
      Expect.sourceExpectation approximation states scale observable
      ≡ Quad.quadratureSum (quadratureAt refinement)

    quadratureErrorVanishes :
      Seq.Vanishes sequenceLimit
        (λ refinement → Quad.totalErrorBudget (quadratureAt refinement))

open SelectedStateCMP119PhysicalHaarQuadrature public

asGenericPhysicalHaarQuadrature :
  ∀ {SlowField Sequence Component Step Cell approximation sequenceLimit states scale observable} →
  SelectedStateCMP119PhysicalHaarQuadrature
    {SlowField = SlowField}
    {Sequence = Sequence}
    {Component = Component}
    {Step = Step}
    {Cell = Cell}
    approximation sequenceLimit states scale observable →
  Haar.CMP119PhysicalHaarQuadratureWeld
    {SlowField = SlowField}
    {Sequence = Sequence}
    {Component = Component}
    {Step = Step}
    {Cell = Cell}
    approximation sequenceLimit scale observable
asGenericPhysicalHaarQuadrature {states = states} data = record
  { Haar.CMP119PhysicalHaarQuadratureWeld.statesAt = λ _ → states
  ; Haar.CMP119PhysicalHaarQuadratureWeld.quadratureAt = quadratureAt data
  ; Haar.CMP119PhysicalHaarQuadratureWeld.physicalHaarExpectation =
      physicalHaarExpectation data
  ; Haar.CMP119PhysicalHaarQuadratureWeld.sourceIntegralIsPhysical =
      sourceIntegralIsPhysical data
  ; Haar.CMP119PhysicalHaarQuadratureWeld.sourceExpectationIsQuadrature =
      selectedSourceExpectationIsQuadrature data
  ; Haar.CMP119PhysicalHaarQuadratureWeld.quadratureErrorVanishes =
      quadratureErrorVanishes data
  }

asSelectedStateWeld :
  ∀ {SlowField Sequence Component Step Cell approximation sequenceLimit states scale observable}
    (data :
      SelectedStateCMP119PhysicalHaarQuadrature
        {SlowField = SlowField}
        {Sequence = Sequence}
        {Component = Component}
        {Step = Step}
        {Cell = Cell}
        approximation sequenceLimit states scale observable) →
  ApproxHaar.SelectedStatePhysicalHaarF2Weld
    states (asGenericPhysicalHaarQuadrature data)
asSelectedStateWeld data = record
  { ApproxHaar.SelectedStatePhysicalHaarF2Weld.statesAtIsSelected = λ _ → refl
  }

selectedStateFamilyIsDefinitionallyConstant : Bool
selectedStateFamilyIsDefinitionallyConstant = true

separateStatesAtEqualityNoLongerRequired : Bool
separateStatesAtEqualityNoLongerRequired = true
