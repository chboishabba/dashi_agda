{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCTriangleExact where

------------------------------------------------------------------------
-- C / EXACT AF-STRESS-HAMILTONIAN TRIANGLE
--
-- The preferred concrete C package already fixes:
--
--   literal OPE coefficient = selected AF coefficient
--   stress charge            = pinned reconstructed OS Hamiltonian
--   local package Hamiltonian = pinned reconstructed OS Hamiltonian
--
-- This file closes the triangle explicitly, so no later C consumer can insert
-- a distinct Hamiltonian or a second stress generator.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans; sym)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as C
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119LocalCExact as LocalC
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119StressCommonCoreExact as Common
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local

stressChargeEqualsCompiledLocalHamiltonian :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division S osInputs reconstruction group}
    (inputs :
      C.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction group) →
  Common.stressCharge (C.stressCommonCore inputs) (C.stressTensor inputs)
  ≡
  Local.reconstructedHamiltonian
    (C.compileConcretePinnedLocalPackage inputs)
stressChargeEqualsCompiledLocalHamiltonian inputs =
  trans
    (C.stressChargeGeneratesPinnedHamiltonian inputs)
    (sym
      (LocalC.pinnedLocalHamiltonianIsOSHamiltonian
        (C.asPinnedLocalCInputs inputs)))

literalCoefficientIsSelectedAFCoefficient :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division S osInputs reconstruction group}
    (inputs :
      C.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction group)
    left right output position →
  C.coefficient inputs left right output position
  ≡
  C.asymptoticallyFreeCoefficient inputs left right output position
literalCoefficientIsSelectedAFCoefficient inputs =
  C.coefficientMatchesAsymptoticFreedom inputs

pinnedConcreteLocalCStressHamiltonianTriangleLevel : ProofLevel
pinnedConcreteLocalCStressHamiltonianTriangleLevel = machineChecked

pinnedConcreteLocalCAFCoefficientEqualityLevel : ProofLevel
pinnedConcreteLocalCAFCoefficientEqualityLevel = machineChecked
