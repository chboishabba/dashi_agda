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
-- SAME-OBJECT REQUIREMENT
--
-- The commutator is evaluated on `Audit.velocity system` over the SAME real
-- field and integer embedding as the physical Galerkin system.  There is no
-- parallel model/velocity carrier silently compared by incidence labels alone.
--
-- This is the structural permission needed by the compact-Gamma far-low
-- mechanism: expose the divergence-free/projector commutator on the actual
-- external carrier before taking absolute values.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≢_)

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
    {I : C3.ModeInverseSquare (LP.realField model) E}
    (system : Audit.FiniteComplex3GalerkinSystem (LP.realField model) E I)
    (tau : Physical.PhysicalTriadIncidence)
    (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau))
    (swapMember : Symmetry.swapTriad tau ∈
      Audit.concreteTriadsAt system (Physical.k tau))
    (swapDifferent : Symmetry.swapTriad tau ≢ tau) →
  List (C3.Complex (LP.realField model))
externalOddPQCoefficients model projectorCutoff E
    system tau tauMember swapMember swapDifferent =
  map
    (Odd.literalOddPQTriadCoefficient
      model projectorCutoff E (Audit.velocity system))
    (External.externalResidualCarrier
      system tau tauMember swapMember swapDifferent)

externalProjectorCommutatorCoefficients :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    {I : C3.ModeInverseSquare (LP.realField model) E}
    (system : Audit.FiniteComplex3GalerkinSystem (LP.realField model) E I)
    (tau : Physical.PhysicalTriadIncidence)
    (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau))
    (swapMember : Symmetry.swapTriad tau ∈
      Audit.concreteTriadsAt system (Physical.k tau))
    (swapDifferent : Symmetry.swapTriad tau ≢ tau) →
  List (C3.Complex (LP.realField model))
externalProjectorCommutatorCoefficients model projectorCutoff E
    system tau tauMember swapMember swapDifferent =
  map
    (Com.literalProjectorCommutatorTriadCoefficient
      model projectorCutoff E (Audit.velocity system))
    (External.externalResidualCarrier
      system tau tauMember swapMember swapDifferent)

externalResidualOddPQIsProjectorCommutator :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    {I : C3.ModeInverseSquare (LP.realField model) E}
    (system : Audit.FiniteComplex3GalerkinSystem (LP.realField model) E I)
    (tau : Physical.PhysicalTriadIncidence)
    (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau))
    (swapMember : Symmetry.swapTriad tau ∈
      Audit.concreteTriadsAt system (Physical.k tau))
    (swapDifferent : Symmetry.swapTriad tau ≢ tau) →
  externalOddPQCoefficients
    model projectorCutoff E
    system tau tauMember swapMember swapDifferent
  ≡
  externalProjectorCommutatorCoefficients
    model projectorCutoff E
    system tau tauMember swapMember swapDifferent
externalResidualOddPQIsProjectorCommutator
    model projectorCutoff E
    system tau tauMember swapMember swapDifferent =
  Com.mapPointwiseOddPQIsCommutator
    model projectorCutoff E (Audit.velocity system)
    (External.externalResidualCarrier
      system tau tauMember swapMember swapDifferent)

round111ExternalResidualCommutesBeforeAbsoluteValues : Bool
round111ExternalResidualCommutesBeforeAbsoluteValues = true

round111ExternalResidualUsesSameGalerkinVelocity : Bool
round111ExternalResidualUsesSameGalerkinVelocity = true

round111ExternalResidualCommutesBeforeAbsoluteValuesIsTrue :
  round111ExternalResidualCommutesBeforeAbsoluteValues ≡ true
round111ExternalResidualCommutesBeforeAbsoluteValuesIsTrue = refl

round111ExternalResidualUsesSameGalerkinVelocityIsTrue :
  round111ExternalResidualUsesSameGalerkinVelocity ≡ true
round111ExternalResidualUsesSameGalerkinVelocityIsTrue = refl
