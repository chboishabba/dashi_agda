{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNExternalWaleffeResidualMembershipCompilerRound616Exact where

------------------------------------------------------------------------
-- ROUND616 / R112 MEMBERSHIP COMPILER
--
-- R112's ThreeLegResidualMembership historically asks for nine fields:
--
--   kMember, kSwapMember, kSwapDifferent,
--   pMember, pSwapMember, pSwapDifferent,
--   qMember, qSwapMember, qSwapDifferent.
--
-- The six list-membership fields are not independent physical inputs.
--
-- Audit.concreteTriadsAt is definitionally the literal physical output fibre.
-- From one selected
--
--   tau ∈ concreteTriadsAt system (k tau)
--
-- we recover global physical-enumeration membership, apply the exact R38
-- pEnergyLeg/qEnergyLeg enumeration closure, put those transformed incidences
-- back into their literal p/q output fibres, and use R224 for swap closure in
-- each output fibre.
--
-- Therefore the only irreducible R112 inputs are the three nonfixedness
-- witnesses required by the self-swap-orbit removal construction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≢_)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberConjugationRound35Exact as Fibre35
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberPermutationRound35Exact as KFree
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeResidualCarrierRound112Exact as R112

------------------------------------------------------------------------
-- Fibre membership -> global enumeration membership.
------------------------------------------------------------------------

selectedFibreMemberIsGlobalEnumerationMember :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  tau ∈ Audit.concreteTriadsAt system (Physical.k tau) →
  tau ∈ Physical.physicalTriadEnumeration (Audit.cutoff system)
selectedFibreMemberIsGlobalEnumerationMember member =
  KFree.cubeMemberToStd
    (Fibre35.physicalOutputFiberMemberEnumeration
      (KFree.stdMemberToCube member))

------------------------------------------------------------------------
-- Cyclic energy-leg members in their own literal output fibres.
------------------------------------------------------------------------

pEnergyLegConcreteMember :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  tau ∈ Audit.concreteTriadsAt system (Physical.k tau) →
  Orbit.pEnergyLeg tau ∈
    Audit.concreteTriadsAt system (Physical.p tau)
pEnergyLegConcreteMember {system = system} {tau = tau} member =
  KFree.cubeMemberToStd
    (Output.physicalOutputFiberComplete
      (KFree.stdMemberToCube
        (R38.pEnergyLegMember
          (selectedFibreMemberIsGlobalEnumerationMember member)))
      (Orbit.pEnergyLegOutput tau))

qEnergyLegConcreteMember :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  tau ∈ Audit.concreteTriadsAt system (Physical.k tau) →
  Orbit.qEnergyLeg tau ∈
    Audit.concreteTriadsAt system (Physical.q tau)
qEnergyLegConcreteMember {system = system} {tau = tau} member =
  KFree.cubeMemberToStd
    (Output.physicalOutputFiberComplete
      (KFree.stdMemberToCube
        (R38.qEnergyLegMember
          (selectedFibreMemberIsGlobalEnumerationMember member)))
      (Orbit.qEnergyLegOutput tau))

------------------------------------------------------------------------
-- Swap members are compiler-owned once each leg member is known.
------------------------------------------------------------------------

selectedSwapConcreteMember :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  tau ∈ Audit.concreteTriadsAt system (Physical.k tau) →
  Symmetry.swapTriad tau ∈
    Audit.concreteTriadsAt system (Physical.k tau)
selectedSwapConcreteMember = R224.swapOutputFibreMember

pEnergyLegSwapConcreteMember :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  tau ∈ Audit.concreteTriadsAt system (Physical.k tau) →
  Symmetry.swapTriad (Orbit.pEnergyLeg tau) ∈
    Audit.concreteTriadsAt system (Physical.p tau)
pEnergyLegSwapConcreteMember member =
  R224.swapOutputFibreMember (pEnergyLegConcreteMember member)

qEnergyLegSwapConcreteMember :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  tau ∈ Audit.concreteTriadsAt system (Physical.k tau) →
  Symmetry.swapTriad (Orbit.qEnergyLeg tau) ∈
    Audit.concreteTriadsAt system (Physical.q tau)
qEnergyLegSwapConcreteMember member =
  R224.swapOutputFibreMember (qEnergyLegConcreteMember member)

------------------------------------------------------------------------
-- Only genuine geometric residue: three swap-nonfixedness witnesses.
------------------------------------------------------------------------

record ThreeLegSwapNonfixed
    (tau : Physical.PhysicalTriadIncidence) : Set where
  field
    kSwapDifferent :
      Symmetry.swapTriad tau ≢ tau

    pSwapDifferent :
      Symmetry.swapTriad (Orbit.pEnergyLeg tau)
      ≢ Orbit.pEnergyLeg tau

    qSwapDifferent :
      Symmetry.swapTriad (Orbit.qEnergyLeg tau)
      ≢ Orbit.qEnergyLeg tau

open ThreeLegSwapNonfixed public

compileThreeLegResidualMembership :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  tau ∈ Audit.concreteTriadsAt system (Physical.k tau) →
  ThreeLegSwapNonfixed tau →
  R112.ThreeLegResidualMembership system tau
compileThreeLegResidualMembership system tau member nonfixed = record
  { R112.ThreeLegResidualMembership.kMember =
      member
  ; R112.ThreeLegResidualMembership.kSwapMember =
      selectedSwapConcreteMember member
  ; R112.ThreeLegResidualMembership.kSwapDifferent =
      kSwapDifferent nonfixed

  ; R112.ThreeLegResidualMembership.pMember =
      pEnergyLegConcreteMember member
  ; R112.ThreeLegResidualMembership.pSwapMember =
      pEnergyLegSwapConcreteMember member
  ; R112.ThreeLegResidualMembership.pSwapDifferent =
      pSwapDifferent nonfixed

  ; R112.ThreeLegResidualMembership.qMember =
      qEnergyLegConcreteMember member
  ; R112.ThreeLegResidualMembership.qSwapMember =
      qEnergyLegSwapConcreteMember member
  ; R112.ThreeLegResidualMembership.qSwapDifferent =
      qSwapDifferent nonfixed
  }

------------------------------------------------------------------------
-- Frontier status.
------------------------------------------------------------------------

r112SixMembershipFieldsCompilerClosed : Bool
r112SixMembershipFieldsCompilerClosed = true

r112OnlyThreeSwapNonfixednessInputsRemain : Bool
r112OnlyThreeSwapNonfixednessInputsRemain = true

r112MembershipIsIndependentPhysicalDebt : Bool
r112MembershipIsIndependentPhysicalDebt = false

r112SwapNonfixednessAutomaticallyTrueOnWholeFibre : Bool
r112SwapNonfixednessAutomaticallyTrueOnWholeFibre = false

r112SixMembershipFieldsCompilerClosedIsTrue :
  r112SixMembershipFieldsCompilerClosed ≡ true
r112SixMembershipFieldsCompilerClosedIsTrue = refl

r112OnlyThreeSwapNonfixednessInputsRemainIsTrue :
  r112OnlyThreeSwapNonfixednessInputsRemain ≡ true
r112OnlyThreeSwapNonfixednessInputsRemainIsTrue = refl

r112MembershipIsIndependentPhysicalDebtIsFalse :
  r112MembershipIsIndependentPhysicalDebt ≡ false
r112MembershipIsIndependentPhysicalDebtIsFalse = refl

r112SwapNonfixednessAutomaticallyTrueOnWholeFibreIsFalse :
  r112SwapNonfixednessAutomaticallyTrueOnWholeFibre ≡ false
r112SwapNonfixednessAutomaticallyTrueOnWholeFibreIsFalse = refl
