{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3FactorizedPhysicalWeldExact where

------------------------------------------------------------------------
-- Q3 MAX-CUT: IDENTIFY THE PHYSICAL HAAR FINITE OBJECT WITH THE SAME
-- FACTORIZED CMP119 F^2 SOURCE EXPECTATION USED BY THE LOCAL-C LANE.
--
-- The generic Haar bridge allowed `statesAt refinement` to vary independently.
-- For the selected factorized CMP119 observable this freedom is unnecessary and
-- obscures the same-object statement.  Pin one finite SlowField list and one
-- observable O_F2.  Refinement may improve the quadrature/error certificate,
-- but it does not silently change which finite state/observable object is being
-- integrated.
--
-- This produces the existing physical-Haar representation with
--
--   finiteCMP119Expectation n = sourceExpectation states O_F2
--
-- definitionally.  The Local-C finite-observable compiler already exposes
--
--   finiteF2Numerator n = approximateExpectation_n states O_F2.
--
-- Hence the existing factorized-density expectation error is exactly the Q3
-- asymptotic bridge.  Q3 is no longer an independent source theorem; the only
-- physical source payment is the already-existing Haar quadrature semantics on
-- this same state/observable carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.CMP119AntigravityRealHaarExpectationRepresentationExact as HaarRep
import DASHI.Physics.Foundations.CMP119AntigravitySourceExpectationToPhysicalHaarExact as Haar
import DASHI.Physics.Foundations.CMP119CosmologyP3PhysicalExpectationIdentificationExact as Identification

import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityApproximationExact as Approx
import DASHI.Physics.YangMills.BalabanCMP119FiniteObservableExpectationConvergenceExact as Expect
import DASHI.Physics.YangMills.BalabanCompactHaarFiniteQuadratureErrorExact as Quad
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq

record FixedStateFactorizedPhysicalHaarWeld
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

    sourceExpectationIsQuadrature :
      ∀ refinement →
      Expect.sourceExpectation approximation states scale observable
      ≡ Quad.quadratureSum (quadratureAt refinement)

    quadratureErrorVanishes :
      Seq.Vanishes sequenceLimit
        (λ refinement →
          Quad.totalErrorBudget (quadratureAt refinement))

open FixedStateFactorizedPhysicalHaarWeld public

asPhysicalHaarQuadratureWeld :
  ∀ {SlowField Sequence Component Step Cell approximation sequenceLimit
      states scale observable} →
  FixedStateFactorizedPhysicalHaarWeld
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
asPhysicalHaarQuadratureWeld {states = states} weld = record
  { Haar.CMP119PhysicalHaarQuadratureWeld.statesAt = λ _ → states
  ; Haar.CMP119PhysicalHaarQuadratureWeld.quadratureAt = quadratureAt weld
  ; Haar.CMP119PhysicalHaarQuadratureWeld.physicalHaarExpectation =
      physicalHaarExpectation weld
  ; Haar.CMP119PhysicalHaarQuadratureWeld.sourceIntegralIsPhysical =
      sourceIntegralIsPhysical weld
  ; Haar.CMP119PhysicalHaarQuadratureWeld.sourceExpectationIsQuadrature =
      sourceExpectationIsQuadrature weld
  ; Haar.CMP119PhysicalHaarQuadratureWeld.quadratureErrorVanishes =
      quadratureErrorVanishes weld
  }

physicalHaarRepresentation :
  ∀ {SlowField Sequence Component Step Cell approximation sequenceLimit
      states scale observable} →
  FixedStateFactorizedPhysicalHaarWeld
    {SlowField = SlowField}
    {Sequence = Sequence}
    {Component = Component}
    {Step = Step}
    {Cell = Cell}
    approximation sequenceLimit states scale observable →
  HaarRep.RealHaarExpectationRepresentation sequenceLimit
physicalHaarRepresentation weld =
  Haar.compileCMP119PhysicalHaarRepresentation
    (asPhysicalHaarQuadratureWeld weld)

compiledHaarFiniteIsFactorizedSourceExpectation :
  ∀ {SlowField Sequence Component Step Cell approximation sequenceLimit
      states scale observable}
    (weld :
      FixedStateFactorizedPhysicalHaarWeld
        {SlowField = SlowField}
        {Sequence = Sequence}
        {Component = Component}
        {Step = Step}
        {Cell = Cell}
        approximation sequenceLimit states scale observable)
    refinement →
  HaarRep.finiteCMP119Expectation
    (physicalHaarRepresentation weld) refinement
  ≡ Expect.sourceExpectation approximation states scale observable
compiledHaarFiniteIsFactorizedSourceExpectation weld refinement = refl

compileFixedStatePhysicalIdentification :
  ∀ {SlowField Sequence Component Step Cell approximation sequenceLimit
      states scale observable localFinite}
    (weld :
      FixedStateFactorizedPhysicalHaarWeld
        {SlowField = SlowField}
        {Sequence = Sequence}
        {Component = Component}
        {Step = Step}
        {Cell = Cell}
        approximation sequenceLimit states scale observable) →
    (∀ refinement →
      localFinite refinement
      ≡ Expect.approximateExpectation
          approximation states refinement scale observable) →
  Identification.FactorizedPhysicalExpectationIdentification
    {approximation = approximation}
    states scale observable
    localFinite
    (HaarRep.finiteCMP119Expectation
      (physicalHaarRepresentation weld))
compileFixedStatePhysicalIdentification weld localIsApproximate = record
  { Identification.FactorizedPhysicalExpectationIdentification.localFiniteF2IsFactorizedApproximation =
      localIsApproximate
  ; Identification.FactorizedPhysicalExpectationIdentification.haarFiniteF2IsFactorizedSourceExpectation =
      compiledHaarFiniteIsFactorizedSourceExpectation weld
  }

------------------------------------------------------------------------
-- Frontier accounting.
------------------------------------------------------------------------

q3IndependentSourcePackageStillRequired : Bool
q3IndependentSourcePackageStillRequired = false

sameFiniteStateCarrierIsDefinitional : Bool
sameFiniteStateCarrierIsDefinitional = true

factorizedDensityErrorPaysQ3Bridge : Bool
factorizedDensityErrorPaysQ3Bridge = true

-- This is not a new Q3-specific bridge.  It is the pre-existing AG-S1 source
-- statement that the selected finite source expectation is the physical Haar
-- integral/quadrature on the same carrier.
remainingPaymentIsExistingPhysicalHaarQuadratureSemantics : Bool
remainingPaymentIsExistingPhysicalHaarQuadratureSemantics = true
