{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteOS3SystemExact where

------------------------------------------------------------------------
-- LITERAL A / FINITE PERMUTATION SYMMETRY -> CONTINUUM OS3
--
-- Preferred OS3 route mirrors the concrete OS1 compiler:
-- if every normalized finite CMP119 cylinder expectation is invariant under
-- the selected bosonic/permutation action, scalar-limit uniqueness gives the
-- SAME equality for the constructed continuum expectation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanCylinderLimitActionInvariantExact as ActionLimit
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteOS1SystemExact as OS1

record PinnedCMP119ConcreteOS3Inputs
    {CompactSimpleGroup Spacetime Configuration Position
     CurvaturePolynomial LocalOperator OPECoefficient StressTensor
     HilbertSpace Hamiltonian VacuumState EuclideanAction Permutation
     sequenceLimit limitLaws quotient division S}
    (os1 :
      OS1.PinnedCMP119ConcreteOS1Inputs
        CompactSimpleGroup Spacetime Configuration Position
        CurvaturePolynomial LocalOperator OPECoefficient StressTensor
        HilbertSpace Hamiltonian VacuumState EuclideanAction
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S) : Set₁ where
  field
    permute :
      Permutation → (Configuration → ℝ) → (Configuration → ℝ)

    finitePermutationInvariant :
      ∀ group cutoff permutation observable →
      Limit.finiteExpectation (OS1.family os1 group) cutoff
        (permute permutation observable)
      ≡
      Limit.finiteExpectation (OS1.family os1 group) cutoff observable

open PinnedCMP119ConcreteOS3Inputs public

permutationActionInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S}
    {os1 :
      OS1.PinnedCMP119ConcreteOS1Inputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum EuclideanAction
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S}
    (inputs : PinnedCMP119ConcreteOS3Inputs
      {Permutation = Permutation} os1)
    group →
  ActionLimit.CylinderActionInvariantInputs
    (Limit.asCylinderLimitData (OS1.family os1 group))
    Permutation
permutationActionInputs inputs group = record
  { ActionLimit.CylinderActionInvariantInputs.act =
      permute inputs
  ; ActionLimit.CylinderActionInvariantInputs.finiteActionInvariant =
      finitePermutationInvariant inputs group
  }

continuumPermutationInvariant :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S}
    {os1 :
      OS1.PinnedCMP119ConcreteOS1Inputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum EuclideanAction
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S}
    (inputs : PinnedCMP119ConcreteOS3Inputs
      {Permutation = Permutation} os1)
    group permutation observable →
  Limit.limitExpectation (OS1.family os1 group)
    (permute inputs permutation observable)
  ≡
  Limit.limitExpectation (OS1.family os1 group) observable
continuumPermutationInvariant inputs group =
  ActionLimit.continuumActionInvariant
    (permutationActionInputs inputs group)

pinnedConcreteOS3LimitCompilerLevel : ProofLevel
pinnedConcreteOS3LimitCompilerLevel = machineChecked

-- Physical A/OS3 residue: define the literal bosonic/permutation action on the
-- selected CMP119 cylinder class and prove finite normalized invariance.
literalFiniteCMP119PermutationInvarianceLevel : ProofLevel
literalFiniteCMP119PermutationInvarianceLevel = conditional
