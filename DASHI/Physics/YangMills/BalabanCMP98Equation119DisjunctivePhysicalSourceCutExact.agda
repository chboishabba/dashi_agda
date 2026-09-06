{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119DisjunctivePhysicalSourceCutExact where

------------------------------------------------------------------------
-- CMP98 EQ. (119): DISJUNCTIVE PHYSICAL SOURCE CUT
--
-- Primary sources:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I. Generation of Effective Actions in a Small Field Approximation
-- and a Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- There are now three theorem-level downstream routes:
--
--   A0. historical selected-background + global selected-cut threshold
--       (R175/R184); sufficient but not least-privilege;
--
--   A1. preferred selected-background + pointwise ACTUAL-relative cut admission
--       + existing Federbush family; this carries the semantic theorem
--       exp(principalLog(relative)) = relative and avoids the global
--       `1/24 <= selected cut radius` premise;
--
--   B. concrete dyadic CMP109 physical-input package + same-object relative
--      weld + existing Federbush convention family.
--
-- R156's historical derivative constructor uses the chart but does not inspect
-- the relative-contour image proof.  That syntactic fact is NOT used to claim
-- physical closure: A1 keeps actual-relative admission as a public input and
-- exports the exp/log same-object theorem beside the derivative constructor.
--
-- Round187/R189 independently close periodic realization and raw/unit path
-- algebra.  They do not inhabit the complete A1 or B physical packages.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedBackgroundBondWeldRound170Exact as R170
import DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedExistingCutRound175Exact as R175
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushCalculusReuseRound177Exact as R177
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushSelectedCutProducerRound178Exact as R178
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveCoarseBondSourceRound182Exact as R182
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveDyadicStrongestProducerRound183Exact as R183
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveBondSelectedCutFederbushRound184Exact as R184
import DASHI.Physics.YangMills.BalabanCMP98SelectedPhysicalUnitCarrierRound187Exact as R187
import DASHI.Physics.YangMills.BalabanCMP98RawUnitPathHomomorphismRound189Exact as R189
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicPrintedPhysicalInstantiationExact as Dyadic
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalP4CutRadiusFirewallExact as RadiusFirewall
import DASHI.Physics.YangMills.BalabanCMP98Equation119PointwiseSemanticSelectedCutExact as PointwiseSemantic

------------------------------------------------------------------------
-- Branch A0: historical global selected-cut threshold adapter.
------------------------------------------------------------------------

record SelectedCutEq119Inputs
    {n coarseSide Value group CoarseField FineField}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier n coarseSide Value group) : Set₁ where
  field
    selectedWeld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField}
      {FineField = FineField}
      {Lie = Lie.SU2LieAlgebra}
      (R182.asCanonicalL13Equation119Source source)

    selectedCutInputs : R175.SelectedExistingCutInputs
      (R182.asCanonicalL13Equation119Source source) selectedWeld

    selectedFederbushFamily : R177.ExistingFederbushConventionFamily

open SelectedCutEq119Inputs public

selectedCutEq119OneStep :
  ∀ {n coarseSide Value group CoarseField FineField}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier n coarseSide Value group) →
  SelectedCutEq119Inputs
    {CoarseField = CoarseField} {FineField = FineField} source →
  R126.OneStepAveragingDerivative R178.su2AdditiveCarrier
selectedCutEq119OneStep source inputs =
  R184.positiveBondSelectedCutFederbushOneStepDerivative
    source
    (selectedWeld inputs)
    (selectedCutInputs inputs)
    (selectedFederbushFamily inputs)

selectedCutEq119Multiscale :
  ∀ {n coarseSide Value group CoarseField FineField}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier n coarseSide Value group) →
  SelectedCutEq119Inputs
    {CoarseField = CoarseField} {FineField = FineField} source →
  Nat → R126.Operator R178.su2AdditiveCarrier
selectedCutEq119Multiscale source inputs =
  R184.positiveBondSelectedCutFederbushMultiscaleDerivative
    source
    (selectedWeld inputs)
    (selectedCutInputs inputs)
    (selectedFederbushFamily inputs)

selectedCutCanonicalP4RadiusFirewallLevel : ProofLevel
selectedCutCanonicalP4RadiusFirewallLevel =
  RadiusFirewall.cmp98Equation119CanonicalP4CutRadiusFirewallLevel

------------------------------------------------------------------------
-- Branch A1: preferred pointwise semantic selected-cut route.
------------------------------------------------------------------------

record PointwiseSemanticEq119Inputs
    {n coarseSide Value group CoarseField FineField}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier n coarseSide Value group) : Set₁ where
  field
    pointwiseSelectedWeld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField}
      {FineField = FineField}
      {Lie = Lie.SU2LieAlgebra}
      (R182.asCanonicalL13Equation119Source source)

    pointwiseActualRelativeCutFamily :
      PointwiseSemantic.PointwiseSelectedCutFamily
        source pointwiseSelectedWeld

    pointwiseFederbushFamily : R177.ExistingFederbushConventionFamily

open PointwiseSemanticEq119Inputs public

pointwiseSemanticEq119OneStep :
  ∀ {n coarseSide Value group CoarseField FineField}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier n coarseSide Value group) →
  PointwiseSemanticEq119Inputs
    {CoarseField = CoarseField} {FineField = FineField} source →
  R126.OneStepAveragingDerivative R178.su2AdditiveCarrier
pointwiseSemanticEq119OneStep source inputs =
  PointwiseSemantic.pointwiseSemanticSelectedCutOneStepDerivative
    source
    (pointwiseSelectedWeld inputs)
    (pointwiseActualRelativeCutFamily inputs)
    (pointwiseFederbushFamily inputs)

pointwiseSemanticEq119Multiscale :
  ∀ {n coarseSide Value group CoarseField FineField}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier n coarseSide Value group) →
  PointwiseSemanticEq119Inputs
    {CoarseField = CoarseField} {FineField = FineField} source →
  Nat → R126.Operator R178.su2AdditiveCarrier
pointwiseSemanticEq119Multiscale source inputs =
  PointwiseSemantic.pointwiseSemanticSelectedCutMultiscaleDerivative
    source
    (pointwiseSelectedWeld inputs)
    (pointwiseActualRelativeCutFamily inputs)
    (pointwiseFederbushFamily inputs)

------------------------------------------------------------------------
-- Branch B: dyadic CMP109 physical-input package / same-object relative weld.
------------------------------------------------------------------------

record DyadicEq119Inputs
    {n coarseN Group group Field Scalar Radius Entry}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier n (suc coarseN) Group group)
    (inputs : Dyadic.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry) : Set₁ where
  field
    dyadicRelativeWeld : R183.PositiveDyadicRelativeWeld source inputs
    dyadicFederbushFamily : R177.ExistingFederbushConventionFamily

open DyadicEq119Inputs public

dyadicEq119OneStep :
  ∀ {n coarseN Group group Field Scalar Radius Entry}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier n (suc coarseN) Group group)
    (inputs : Dyadic.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry) →
  DyadicEq119Inputs source inputs →
  R126.OneStepAveragingDerivative R178.su2AdditiveCarrier
dyadicEq119OneStep source inputs eqInputs =
  R183.positiveDyadicOneStepDerivative
    source inputs
    (dyadicRelativeWeld eqInputs)
    (dyadicFederbushFamily eqInputs)

dyadicEq119Multiscale :
  ∀ {n coarseN Group group Field Scalar Radius Entry}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier n (suc coarseN) Group group)
    (inputs : Dyadic.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry) →
  DyadicEq119Inputs source inputs →
  Nat → R126.Operator R178.su2AdditiveCarrier
dyadicEq119Multiscale source inputs eqInputs =
  R183.positiveDyadicMultiscaleDerivative
    source inputs
    (dyadicRelativeWeld eqInputs)
    (dyadicFederbushFamily eqInputs)

------------------------------------------------------------------------
-- Theorem-level support already closed independently of full physical inputs.
------------------------------------------------------------------------

physicalPeriodicRealizationRound187Level : ProofLevel
physicalPeriodicRealizationRound187Level =
  R187.cmp98SelectedPhysicalPeriodicRealizationRound187Level

rawUnitPathHomomorphismRound189Level : ProofLevel
rawUnitPathHomomorphismRound189Level =
  R189.cmp98RawUnitPathHolomorphismRound189Level

pointwiseSemanticSelectedCutCompilerLevel : ProofLevel
pointwiseSemanticSelectedCutCompilerLevel =
  PointwiseSemantic.cmp98Equation119PointwiseSemanticSelectedCutCompilerLevel

------------------------------------------------------------------------
-- Canonical status: compiler closure versus physical source inhabitation.
------------------------------------------------------------------------

record Eq119DisjunctivePhysicalSourceStatus : Set where
  field
    historicalGlobalSelectedCutCompilerClosed : Bool
    pointwiseSemanticSelectedCutCompilerClosed : Bool
    dyadicCompilerClosed : Bool
    physicalPeriodicRealizationRound187Closed : Bool
    rawUnitPathHomomorphismRound189Closed : Bool

    chartOnlyDerivativeSyntaxDoesNotClosePrincipalSemantics : Bool
    selectedBackgroundWeldConstructed : Bool
    pointwiseActualRelativeCutFamilyConstructed : Bool
    historicalGlobalSelectedCutPhysicalPackageConstructed : Bool
    dyadicCMP109PhysicalInputPackageConstructed : Bool
    dyadicTransportedRelativeSameObjectClosed : Bool
    unconditionalPhysicalEq119ProducerClosed : Bool

    historicalGlobalSelectedCutCompilerClosedIsTrue :
      historicalGlobalSelectedCutCompilerClosed ≡ true
    pointwiseSemanticSelectedCutCompilerClosedIsTrue :
      pointwiseSemanticSelectedCutCompilerClosed ≡ true
    dyadicCompilerClosedIsTrue : dyadicCompilerClosed ≡ true
    physicalPeriodicRealizationRound187ClosedIsTrue :
      physicalPeriodicRealizationRound187Closed ≡ true
    rawUnitPathHomomorphismRound189ClosedIsTrue :
      rawUnitPathHomomorphismRound189Closed ≡ true
    chartOnlyDerivativeSyntaxDoesNotClosePrincipalSemanticsIsTrue :
      chartOnlyDerivativeSyntaxDoesNotClosePrincipalSemantics ≡ true

    selectedBackgroundWeldConstructedIsFalse :
      selectedBackgroundWeldConstructed ≡ false
    pointwiseActualRelativeCutFamilyConstructedIsFalse :
      pointwiseActualRelativeCutFamilyConstructed ≡ false
    historicalGlobalSelectedCutPhysicalPackageConstructedIsFalse :
      historicalGlobalSelectedCutPhysicalPackageConstructed ≡ false
    dyadicCMP109PhysicalInputPackageConstructedIsFalse :
      dyadicCMP109PhysicalInputPackageConstructed ≡ false
    dyadicTransportedRelativeSameObjectClosedIsFalse :
      dyadicTransportedRelativeSameObjectClosed ≡ false
    unconditionalPhysicalEq119ProducerClosedIsFalse :
      unconditionalPhysicalEq119ProducerClosed ≡ false

open Eq119DisjunctivePhysicalSourceStatus public

canonicalEq119DisjunctivePhysicalSourceStatus :
  Eq119DisjunctivePhysicalSourceStatus
canonicalEq119DisjunctivePhysicalSourceStatus = record
  { historicalGlobalSelectedCutCompilerClosed = true
  ; pointwiseSemanticSelectedCutCompilerClosed = true
  ; dyadicCompilerClosed = true
  ; physicalPeriodicRealizationRound187Closed = true
  ; rawUnitPathHomomorphismRound189Closed = true
  ; chartOnlyDerivativeSyntaxDoesNotClosePrincipalSemantics = true
  ; selectedBackgroundWeldConstructed = false
  ; pointwiseActualRelativeCutFamilyConstructed = false
  ; historicalGlobalSelectedCutPhysicalPackageConstructed = false
  ; dyadicCMP109PhysicalInputPackageConstructed = false
  ; dyadicTransportedRelativeSameObjectClosed = false
  ; unconditionalPhysicalEq119ProducerClosed = false
  ; historicalGlobalSelectedCutCompilerClosedIsTrue = refl
  ; pointwiseSemanticSelectedCutCompilerClosedIsTrue = refl
  ; dyadicCompilerClosedIsTrue = refl
  ; physicalPeriodicRealizationRound187ClosedIsTrue = refl
  ; rawUnitPathHomomorphismRound189ClosedIsTrue = refl
  ; chartOnlyDerivativeSyntaxDoesNotClosePrincipalSemanticsIsTrue = refl
  ; selectedBackgroundWeldConstructedIsFalse = refl
  ; pointwiseActualRelativeCutFamilyConstructedIsFalse = refl
  ; historicalGlobalSelectedCutPhysicalPackageConstructedIsFalse = refl
  ; dyadicCMP109PhysicalInputPackageConstructedIsFalse = refl
  ; dyadicTransportedRelativeSameObjectClosedIsFalse = refl
  ; unconditionalPhysicalEq119ProducerClosedIsFalse = refl
  }

cmp98Equation119DisjunctiveSourceCompilerLevel : ProofLevel
cmp98Equation119DisjunctiveSourceCompilerLevel = machineChecked

cmp98Equation119PhysicalSourceInstantiationLevel : ProofLevel
cmp98Equation119PhysicalSourceInstantiationLevel = conditional
