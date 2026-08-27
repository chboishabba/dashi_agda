module DASHI.Physics.Closure.NSTriadKNExternalResidualCommutatorRound111Exact where

------------------------------------------------------------------------
-- ROUND111 / EXTERNAL RESIDUAL INHERITS THE LITERAL COMMUTATOR
--
-- The companion Round111 carrier theorem identifies the k-slot external
-- forcing with the original physical output fibre after deleting exactly the
-- selected self swap-orbit.  Round62's odd-pq/projector-commutator identity is
-- pointwise on an arbitrary list of physical incidences, not only on the full
-- output fibre.  Therefore it restricts immediately to the self-orbit-removed
-- external carrier.
--
-- This is the decisive structural permission for the old compact-Gamma
-- far-low mechanism: the external residue may be estimated *after* exposing
-- the divergence-free/projector commutator, rather than by taking absolute
-- values of the opaque residual vector first.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≢_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComLiteralOddPQKernelRound57Exact as Odd
import DASHI.Physics.Closure.NSTriadKNComLiteralOddPQOutputFibreCommutatorRound62Exact as Com
import DASHI.Physics.Closure.NSTriadKNExternalOutputFibreSelfOrbitRemovalRound111Exact as External

externalOddPQCoefficients :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    {rF} {F : C3.RealField rF}
    {EF : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F EF}
    (system : Audit.FiniteComplex3GalerkinSystem F EF I)
    (tau : Physical.PhysicalTriadIncidence)
    (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau))
    (swapMember : Symmetry.swapTriad tau ∈
      Audit.concreteTriadsAt system (Physical.k tau))
    (swapDifferent : Symmetry.swapTriad tau ≢ tau) →
  List (C3.Complex (LP.realField model))
externalOddPQCoefficients model projectorCutoff E velocity
    system tau tauMember swapMember swapDifferent =
  map
    (Odd.literalOddPQTriadCoefficient model projectorCutoff E velocity)
    (External.externalResidualCarrier
      system tau tauMember swapMember swapDifferent)

externalProjectorCommutatorCoefficients :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    {rF} {F : C3.RealField rF}
    {EF : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F EF}
    (system : Audit.FiniteComplex3GalerkinSystem F EF I)
    (tau : Physical.PhysicalTriadIncidence)
    (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau))
    (swapMember : Symmetry.swapTriad tau ∈
      Audit.concreteTriadsAt system (Physical.k tau))
    (swapDifferent : Symmetry.swapTriad tau ≢ tau) →
  List (C3.Complex (LP.realField model))
externalProjectorCommutatorCoefficients model projectorCutoff E velocity
    system tau tauMember swapMember swapDifferent =
  map
    (Com.literalProjectorCommutatorTriadCoefficient
      model projectorCutoff E velocity)
    (External.externalResidualCarrier
      system tau tauMember swapMember swapDifferent)

externalResidualOddPQIsProjectorCommutator :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    {rF} {F : C3.RealField rF}
    {EF : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F EF}
    (system : Audit.FiniteComplex3GalerkinSystem F EF I)
    (tau : Physical.PhysicalTriadIncidence)
    (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau))
    (swapMember : Symmetry.swapTriad tau ∈
      Audit.concreteTriadsAt system (Physical.k tau))
    (swapDifferent : Symmetry.swapTriad tau ≢ tau) →
  externalOddPQCoefficients
    model projectorCutoff E velocity
    system tau tauMember swapMember swapDifferent
  ≡
  externalProjectorCommutatorCoefficients
    model projectorCutoff E velocity
    system tau tauMember swapMember swapDifferent
externalResidualOddPQIsProjectorCommutator
    model projectorCutoff E velocity
    system tau tauMember swapMember swapDifferent =
  Com.mapPointwiseOddPQIsCommutator
    model projectorCutoff E velocity
    (External.externalResidualCarrier
      system tau tauMember swapMember swapDifferent)

round111ExternalResidualCommutesBeforeAbsoluteValues : Bool
round111ExternalResidualCommutesBeforeAbsoluteValues = true

round111ExternalResidualCommutesBeforeAbsoluteValuesIsTrue :
  round111ExternalResidualCommutesBeforeAbsoluteValues ≡ true
round111ExternalResidualCommutesBeforeAbsoluteValuesIsTrue = refl
