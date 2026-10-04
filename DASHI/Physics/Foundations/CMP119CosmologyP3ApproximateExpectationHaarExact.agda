{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3ApproximateExpectationHaarExact where

------------------------------------------------------------------------
-- Q3 MAX-CUT: PUT LOCAL-C AND PHYSICAL HAAR ON THE SAME FINITE SEQUENCE.
--
-- The older common-limit interface asked for a pointwise equality between
--   localTransport.finiteF2Numerator
-- and
--   physicalHaar.finiteCMP119Expectation.
--
-- The actual source machinery lets us do better.  The Local-C transport is
-- compiled from CMP119's factorized-density approximateExpectation sequence.
-- The physical Haar quadrature was previously represented by sourceExpectation.
-- Combine the two existing errors by the triangle inequality and compile a new
-- Haar representation whose finite sequence is *the same approximateExpectation
-- sequence*.  Then the common-limit pointwise equality is the already-owned
-- literalFiniteF2IsApproximateExpectation theorem, not a new physical weld.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; _+ℝ_; _-ℝ_; absℝ; _≤ℝ_;
   ≤ℝ-trans; +-mono-≤; absAddSubadditive; subAddCancelMiddle)

import DASHI.Physics.Foundations.CMP119AntigravityFiniteObservableToLocalCAnomalyTransportExact as Observable
import DASHI.Physics.Foundations.CMP119AntigravityFiniteToLocalCAnomalyLimitTransportExact as LocalLimit
import DASHI.Physics.Foundations.CMP119AntigravitySourceExpectationToPhysicalHaarExact as HaarSource
import DASHI.Physics.Foundations.CMP119AntigravityRealHaarExpectationRepresentationExact as HaarLimit
import DASHI.Physics.Foundations.CMP119CosmologyP3LocalCF2PhysicalHaarCommonLimitExact as Common

import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityApproximationExact as Approx
import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityConvergenceExact as Conv
import DASHI.Physics.YangMills.BalabanCMP119FiniteObservableExpectationConvergenceExact as Expect
import DASHI.Physics.YangMills.BalabanCompactHaarFiniteQuadratureErrorExact as Quad
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanRealVanishingFiniteAlgebraExact as Vanishing

record SelectedStatePhysicalHaarF2Weld
    {SlowField Sequence Component Step Cell : Set}
    {approximation :
      Approx.CMP119FactorizedDensityApproximation
        SlowField Sequence Component Step}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    {scale : Nat}
    {observable : SlowField → ℝ}
    (states : List SlowField)
    (haar :
      HaarSource.CMP119PhysicalHaarQuadratureWeld
        {SlowField = SlowField}
        {Sequence = Sequence}
        {Component = Component}
        {Step = Step}
        {Cell = Cell}
        approximation sequenceLimit scale observable)
    : Set₁ where
  field
    statesAtIsSelected :
      ∀ refinement → HaarSource.statesAt haar refinement ≡ states

open SelectedStatePhysicalHaarF2Weld public

module _
    {SlowField Sequence Component Step Cell : Set}
    {approximation :
      Approx.CMP119FactorizedDensityApproximation
        SlowField Sequence Component Step}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (convergence :
      Conv.CMP119FactorizedDensityConvergence
        approximation sequenceLimit)
    (vanishing : Vanishing.RealVanishingFiniteAlgebra sequenceLimit)
    {readout states scale}
    (identification :
      Observable.CMP119AnomalyObservableIdentification
        {approximation = approximation}
        {sequenceLimit = sequenceLimit}
        readout states scale)
    (haar :
      HaarSource.CMP119PhysicalHaarQuadratureWeld
        {SlowField = SlowField}
        {Sequence = Sequence}
        {Component = Component}
        {Step = Step}
        {Cell = Cell}
        approximation sequenceLimit scale
        (Observable.f2Observable identification))
    (selectedStates : SelectedStatePhysicalHaarF2Weld states haar)
  where

  observable : SlowField → ℝ
  observable = Observable.f2Observable identification

  sourceValue : ℝ
  sourceValue =
    Expect.sourceExpectation approximation states scale observable

  approximateValue : Nat → ℝ
  approximateValue refinement =
    Expect.approximateExpectation
      approximation states refinement scale observable

  combinedError : Nat → ℝ
  combinedError refinement =
    Quad.totalErrorBudget (HaarSource.quadratureAt haar refinement)
    +ℝ
    Expect.expectationErrorBudget
      approximation states refinement scale observable

  quadratureSumIsSelectedSource :
    ∀ refinement →
    Quad.quadratureSum (HaarSource.quadratureAt haar refinement)
    ≡ sourceValue
  quadratureSumIsSelectedSource refinement =
    trans
      (sym (HaarSource.sourceExpectationIsQuadrature haar refinement))
      (cong
        (λ selected →
          Expect.sourceExpectation approximation selected scale observable)
        (statesAtIsSelected selectedStates refinement))

  physicalToSelectedSourceBound :
    ∀ refinement →
    absℝ
      (HaarSource.physicalHaarExpectation haar -ℝ sourceValue)
    ≤ℝ
    Quad.totalErrorBudget (HaarSource.quadratureAt haar refinement)
  physicalToSelectedSourceBound refinement =
    let
      quadrature = HaarSource.quadratureAt haar refinement
      base = Quad.finiteQuadratureErrorBound quadrature
      sourceToPhysical = HaarSource.sourceIntegralIsPhysical haar refinement
      quadratureToSelected = quadratureSumIsSelectedSource refinement
    in
    subst
      (λ target →
        absℝ (HaarSource.physicalHaarExpectation haar -ℝ target)
        ≤ℝ Quad.totalErrorBudget quadrature)
      quadratureToSelected
      (subst
        (λ source →
          absℝ (source -ℝ Quad.quadratureSum quadrature)
          ≤ℝ Quad.totalErrorBudget quadrature)
        sourceToPhysical
        base)

  physicalToApproximateBound :
    ∀ refinement →
    absℝ
      (HaarSource.physicalHaarExpectation haar
        -ℝ approximateValue refinement)
    ≤ℝ combinedError refinement
  physicalToApproximateBound refinement =
    let
      physical = HaarSource.physicalHaarExpectation haar
      approximate = approximateValue refinement
      split :
        physical -ℝ approximate
        ≡
        (physical -ℝ sourceValue) +ℝ (sourceValue -ℝ approximate)
      split = subAddCancelMiddle physical sourceValue approximate
    in
    subst
      (λ difference → absℝ difference ≤ℝ combinedError refinement)
      (sym split)
      (≤ℝ-trans
        (absAddSubadditive
          (physical -ℝ sourceValue)
          (sourceValue -ℝ approximate))
        (+-mono-≤
          (physicalToSelectedSourceBound refinement)
          (Expect.finiteExpectationDifferenceBound
            approximation states refinement scale observable)))

  combinedErrorVanishes :
    Seq.Vanishes sequenceLimit combinedError
  combinedErrorVanishes =
    Vanishing.vanishesAdd vanishing
      (λ refinement →
        Quad.totalErrorBudget (HaarSource.quadratureAt haar refinement))
      (λ refinement →
        Expect.expectationErrorBudget
          approximation states refinement scale observable)
      (HaarSource.quadratureErrorVanishes haar)
      (Expect.finiteExpectationBudgetVanishes
        convergence vanishing states scale observable)

  compileApproximateExpectationPhysicalHaar :
    HaarLimit.RealHaarExpectationRepresentation sequenceLimit
  compileApproximateExpectationPhysicalHaar = record
    { HaarLimit.RealHaarExpectationRepresentation.finiteCMP119Expectation =
        approximateValue
    ; HaarLimit.RealHaarExpectationRepresentation.physicalHaarExpectation =
        HaarSource.physicalHaarExpectation haar
    ; HaarLimit.RealHaarExpectationRepresentation.representationError =
        combinedError
    ; HaarLimit.RealHaarExpectationRepresentation.finiteApproximatesPhysical =
        physicalToApproximateBound
    ; HaarLimit.RealHaarExpectationRepresentation.representationErrorVanishes =
        combinedErrorVanishes
    }

  localTransport :
    LocalLimit.FiniteCMP119ToLocalCAnomalyLimitTransport
      sequenceLimit readout
  localTransport =
    Observable.compileFiniteObservableAnomalyLimitTransport
      convergence vanishing identification

  compileCommonFiniteF2Limit :
    Common.LocalCF2PhysicalHaarCommonLimit
      readout localTransport compileApproximateExpectationPhysicalHaar
  compileCommonFiniteF2Limit = record
    { Common.LocalCF2PhysicalHaarCommonLimit.sameFiniteF2Sequence =
        Observable.literalFiniteF2IsApproximateExpectation identification
    }

compiledHaarUsesSameApproximateF2Sequence : Bool
compiledHaarUsesSameApproximateF2Sequence = true

physicalHaarApproximateExpectationUsesCombinedVanishingError : Bool
physicalHaarApproximateExpectationUsesCombinedVanishingError = true

compiledCommonLimitNeedsNoPointwiseSourceWeld : Bool
compiledCommonLimitNeedsNoPointwiseSourceWeld = true
