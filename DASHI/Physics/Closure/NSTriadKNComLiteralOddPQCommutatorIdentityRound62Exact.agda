module DASHI.Physics.Closure.NSTriadKNComLiteralOddPQCommutatorIdentityRound62Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- Author: Piero D'Ancona.
-- Title: "A Short Proof of Commutator Estimates".
-- DOI: 10.1007/s00041-018-9612-8.
-- Correction DOI: 10.1007/s00041-019-09724-7.
--
-- ROUND 62 CONCRETE B WELD
--
-- Round36 proved on a scalar finite model that the coarse/fine naturality
-- defect is an increment.  Round57 later constructed the ACTUAL odd P/Q
-- coefficient on the physical transport entry, but did not state the literal
-- commutator identity connecting the two viewpoints.
--
-- This file closes that algebraic seam in the exact Fourier `realField`.
-- Embed the Boolean low-projector grade as the complex scalar
--
--   chi_P(mode) = 1 when lowSelect=true, 0 otherwise.
--
-- Then for every physical transport entry T_{out,in}, exactly
--
--   oddPQ(out,in)
--     = (chi_P(out) - chi_P(in)) * T_{out,in}.
--
-- The proof is exhaustive on the four projector-grade blocks and uses only the
-- already-proved complex ring laws.  No norm, Schur, angular, or analytic
-- estimate is assumed.
--
-- This explains the concrete Round62 -i witness correctly: raw transport may
-- be O(1), while the SMALL physical B coefficient must arise only after this
-- centered commutator is factorized/normalized and estimated by the existing
-- same/adjacent Schur/Gram machinery.  The missing B theorem is therefore no
-- longer the commutator identity itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNPhysicalTransportMatrixSkewRound40Exact as Matrix
import DASHI.Physics.Closure.NSTriadKNComLiteralOddPQKernelRound57Exact as Odd

projectorGrade :
  ∀ {r} (F : C3.RealField r) → Bool → C3.Complex F
projectorGrade F true = C3.complexOne F
projectorGrade F false = C3.complexZero F

literalProjectorCommutatorCoefficient :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (cutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model)) →
  ∀ {input output} →
  Matrix.PhysicalTransportMatrixEntry input output →
  C3.Complex (LP.realField model)
literalProjectorCommutatorCoefficient
    model cutoff E velocity {input} {output} entry =
  C3.complexMultiply
    (C3.complexSubtract
      (projectorGrade (LP.realField model)
        (LP.lowSelect model cutoff output))
      (projectorGrade (LP.realField model)
        (LP.lowSelect model cutoff input)))
    (Matrix.transportEntryCoefficient E velocity entry)

oneMinusZero :
  ∀ {r} {F : C3.RealField r} →
  C3.complexSubtract (C3.complexOne F) (C3.complexZero F)
  ≡ C3.complexOne F
oneMinusZero {F = F}
  rewrite Hermitian.complexNegateZero F
        | Algebra.complexAddZeroRight (C3.complexOne F) = refl

oneMinusOne :
  ∀ {r} {F : C3.RealField r} →
  C3.complexSubtract (C3.complexOne F) (C3.complexOne F)
  ≡ C3.complexZero F
oneMinusOne {F = F} =
  Ring.complexAddInverseRight (C3.complexOne F)

zeroMinusOne :
  ∀ {r} {F : C3.RealField r} →
  C3.complexSubtract (C3.complexZero F) (C3.complexOne F)
  ≡ C3.complexNegate (C3.complexOne F)
zeroMinusOne {F = F} =
  Algebra.complexAddZeroLeft (C3.complexNegate (C3.complexOne F))

zeroMinusZero :
  ∀ {r} {F : C3.RealField r} →
  C3.complexSubtract (C3.complexZero F) (C3.complexZero F)
  ≡ C3.complexZero F
zeroMinusZero {F = F} =
  Ring.complexAddInverseRight (C3.complexZero F)

negativeOneTimes :
  ∀ {r} {F : C3.RealField r} (value : C3.Complex F) →
  C3.complexMultiply
    (C3.complexNegate (C3.complexOne F)) value
  ≡ C3.complexNegate value
negativeOneTimes {F = F} value =
  trans
    (Algebra.complexNegateMultiplyLeft (C3.complexOne F) value)
    (cong C3.complexNegate (Algebra.complexOneMultiply value))

literalOddPQIsProjectorCommutatorCoefficient :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (cutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model)) →
  ∀ {input output}
    (entry : Matrix.PhysicalTransportMatrixEntry input output) →
  Odd.literalOddPQEntryCoefficient model cutoff E velocity entry
  ≡ literalProjectorCommutatorCoefficient
      model cutoff E velocity entry
literalOddPQIsProjectorCommutatorCoefficient
    model cutoff E velocity {input} {output} entry
  with LP.lowSelect model cutoff output
     | LP.lowSelect model cutoff input
... | true | false =
  sym
    (trans
      (cong
        (λ grade →
          C3.complexMultiply grade
            (Matrix.transportEntryCoefficient E velocity entry))
        oneMinusZero)
      (Algebra.complexOneMultiply
        (Matrix.transportEntryCoefficient E velocity entry)))
... | true | true =
  sym
    (trans
      (cong
        (λ grade →
          C3.complexMultiply grade
            (Matrix.transportEntryCoefficient E velocity entry))
        oneMinusOne)
      (Algebra.complexMultiplyZeroLeft
        (Matrix.transportEntryCoefficient E velocity entry)))
... | false | true =
  sym
    (trans
      (cong
        (λ grade →
          C3.complexMultiply grade
            (Matrix.transportEntryCoefficient E velocity entry))
        zeroMinusOne)
      (negativeOneTimes
        (Matrix.transportEntryCoefficient E velocity entry)))
... | false | false =
  sym
    (trans
      (cong
        (λ grade →
          C3.complexMultiply grade
            (Matrix.transportEntryCoefficient E velocity entry))
        zeroMinusZero)
      (Algebra.complexMultiplyZeroLeft
        (Matrix.transportEntryCoefficient E velocity entry)))

literalOddPQCommutatorIdentityClosed : Bool
literalOddPQCommutatorIdentityClosed = true

literalOddPQCommutatorIdentityClosedIsTrue :
  literalOddPQCommutatorIdentityClosed ≡ true
literalOddPQCommutatorIdentityClosedIsTrue = refl
