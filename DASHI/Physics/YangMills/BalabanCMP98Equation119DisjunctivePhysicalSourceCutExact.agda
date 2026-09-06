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
-- This owner corrects an over-compressed frontier statement.  The repository
-- has two theorem-level downstream compilers for CMP98 equation (119):
--
--   A. selected variational background + selected principal cut + existing
--      Federbush convention family;
--
--   B. concrete dyadic CMP109 physical-input package + same-object relative
--      weld + existing Federbush convention family.
--
-- Round187 and Round189 genuinely close physical periodic-realization existence
-- and the raw/unit-quaternion path homomorphism.  They do NOT by themselves
-- inhabit `DyadicCMP109PrintedPhysicalInputs`, whose fields still include local
-- dependence, a physical principal-log meaning, the crossing-bond convention,
-- differentiated entries and support vanishing.  Likewise the selected-cut
-- branch still requires the selected-background weld and the source-threshold
-- inclusion in the chosen cut.
--
-- Therefore the theorem-strength source cut is disjunctive.  The CMP109
-- transported-relative equality is one leaf on branch B, not the sole
-- source-side payment for equation (119).
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

------------------------------------------------------------------------
-- Branch A: selected background / selected cut.
------------------------------------------------------------------------

record SelectedCutEq119Inputs
    {n coarseSide Value group CoarseField FineField}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier n coarseSide Value group) : Set₁ where
  field
    weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField}
      {FineField = FineField}
      {Lie = Lie.SU2LieAlgebra}
      (R182.asCanonicalL13Equation119Source source)

    cutInputs : R175.SelectedExistingCutInputs
      (R182.asCanonicalL13Equation119Source source) weld

    federbushFamily : R177.ExistingFederbushConventionFamily

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
    source (weld inputs) (cutInputs inputs) (federbushFamily inputs)

selectedCutEq119Multiscale :
  ∀ {n coarseSide Value group CoarseField FineField}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier n coarseSide Value group) →
  SelectedCutEq119Inputs
    {CoarseField = CoarseField} {FineField = FineField} source →
  Nat → R126.Operator R178.su2AdditiveCarrier
selectedCutEq119Multiscale source inputs =
  R184.positiveBondSelectedCutFederbushMultiscaleDerivative
    source (weld inputs) (cutInputs inputs) (federbushFamily inputs)

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
    relativeWeld : R183.PositiveDyadicRelativeWeld source inputs
    federbushFamily : R177.ExistingFederbushConventionFamily

open DyadicEq119Inputs public

-- The caller supplies the CMP109 physical-input package itself separately from
-- this smaller Eq119-specific bundle.  This makes it impossible to mistake the
-- same-object equality for construction of that larger physical package.
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
    source inputs (relativeWeld eqInputs) (federbushFamily eqInputs)

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
    source inputs (relativeWeld eqInputs) (federbushFamily eqInputs)

------------------------------------------------------------------------
-- Canonical status: theorem compilers versus physical inhabitants.
------------------------------------------------------------------------

record Eq119DisjunctivePhysicalSourceStatus : Set where
  field
    selectedCutCompilerClosed : Bool
    dyadicCompilerClosed : Bool
    physicalPeriodicRealizationRound187Closed : Bool
    rawUnitPathHomomorphismRound189Closed : Bool

    selectedCutPhysicalInputPackageConstructed : Bool
    dyadicCMP109PhysicalInputPackageConstructed : Bool
    dyadicTransportedRelativeSameObjectClosed : Bool
    unconditionalPhysicalEq119ProducerClosed : Bool

    selectedCutCompilerClosedIsTrue : selectedCutCompilerClosed ≡ true
    dyadicCompilerClosedIsTrue : dyadicCompilerClosed ≡ true
    physicalPeriodicRealizationRound187ClosedIsTrue :
      physicalPeriodicRealizationRound187Closed ≡ true
    rawUnitPathHomomorphismRound189ClosedIsTrue :
      rawUnitPathHomomorphismRound189Closed ≡ true

    selectedCutPhysicalInputPackageConstructedIsFalse :
      selectedCutPhysicalInputPackageConstructed ≡ false
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
  { selectedCutCompilerClosed = true
  ; dyadicCompilerClosed = true
  ; physicalPeriodicRealizationRound187Closed = true
  ; rawUnitPathHomomorphismRound189Closed = true
  ; selectedCutPhysicalInputPackageConstructed = false
  ; dyadicCMP109PhysicalInputPackageConstructed = false
  ; dyadicTransportedRelativeSameObjectClosed = false
  ; unconditionalPhysicalEq119ProducerClosed = false
  ; selectedCutCompilerClosedIsTrue = refl
  ; dyadicCompilerClosedIsTrue = refl
  ; physicalPeriodicRealizationRound187ClosedIsTrue = refl
  ; rawUnitPathHomomorphismRound189ClosedIsTrue = refl
  ; selectedCutPhysicalInputPackageConstructedIsFalse = refl
  ; dyadicCMP109PhysicalInputPackageConstructedIsFalse = refl
  ; dyadicTransportedRelativeSameObjectClosedIsFalse = refl
  ; unconditionalPhysicalEq119ProducerClosedIsFalse = refl
  }

cmp98Equation119DisjunctiveSourceCompilerLevel : ProofLevel
cmp98Equation119DisjunctiveSourceCompilerLevel = machineChecked

cmp98Equation119PhysicalSourceInstantiationLevel : ProofLevel
cmp98Equation119PhysicalSourceInstantiationLevel = conditional
