module DASHI.Physics.YangMills.BalabanCMP109ConstraintKernelLineFrechetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Wojciech Dybalski, Alexander Stottmeister, Yoh Tanimoto,
-- "The Balaban variational problem in the non-linear sigma model",
-- arXiv:2403.09800 (2024). No DOI recorded in the manuscript.
--
-- DASHI CONTRIBUTION
--
-- Isolate the genuinely sufficient tangent input.  If C has an exact first
-- order expansion at A,
--
--   C(A+v) = C(A) + DC(A)[v] + r_A(v),
--
-- C(A)=0, and h is in ker DC(A), then scalar-line linearity gives
--
--   C(A+t h) = r_A(t h).
--
-- Hence the ordinary Frechet little-o remainder, not a two-background
-- Lipschitz theorem for DC, is the exact analytic input needed by the normal
-- correction argument.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4FiniteDimensionalFrechetChainProductExact as Frechet

record ConstraintFrechetKernelLine
    (State Constraint : Set)
    (state : Frechet.AdditiveCarrier State)
    (constraint : Frechet.AdditiveCarrier Constraint) : Set₁ where
  field
    expansion : Frechet.ExactFirstOrderExpansion state constraint

    base direction : State
    scalarAction : ℚ → State → State

    constraintAtBaseZero :
      Frechet.function expansion base ≡ Frechet.zero constraint

    kernelDirection :
      Frechet.derivative expansion base direction ≡ Frechet.zero constraint

    derivativeScalesOnKernelLine : ∀ scalar →
      Frechet.derivative expansion base (scalarAction scalar direction)
      ≡ scalarActionOnConstraint scalar
          (Frechet.derivative expansion base direction)

    scalarActionOnConstraint : ℚ → Constraint → Constraint

    scalarZeroConstraint : ∀ scalar →
      scalarActionOnConstraint scalar (Frechet.zero constraint)
      ≡ Frechet.zero constraint

    addZeroCollapse : ∀ value →
      Frechet.add constraint (Frechet.zero constraint)
        (Frechet.add constraint (Frechet.zero constraint) value)
      ≡ value

open ConstraintFrechetKernelLine public

kernelLineDerivativeZero :
  ∀ {State Constraint state constraint}
    (line : ConstraintFrechetKernelLine State Constraint state constraint)
    scalar →
  Frechet.derivative (expansion line) (base line)
    (scalarAction line scalar (direction line))
  ≡ Frechet.zero constraint
kernelLineDerivativeZero line scalar =
  trans
    (derivativeScalesOnKernelLine line scalar)
    (trans
      (cong (scalarActionOnConstraint line scalar)
        (kernelDirection line))
      (scalarZeroConstraint line scalar))

selectedConstraintKernelLineResidualIsFrechetRemainder :
  ∀ {State Constraint state constraint}
    (line : ConstraintFrechetKernelLine State Constraint state constraint)
    scalar →
  Frechet.function (expansion line)
    (Frechet.add state (base line)
      (scalarAction line scalar (direction line)))
  ≡ Frechet.remainder (expansion line) (base line)
      (scalarAction line scalar (direction line))
selectedConstraintKernelLineResidualIsFrechetRemainder
    {constraint = constraint} line scalar =
  let
    increment = scalarAction line scalar (direction line)
    selectedRemainder = Frechet.remainder (expansion line) (base line) increment
    expanded = Frechet.incrementExpansion (expansion line) (base line) increment
  in
  trans expanded
    (trans
      (cong
        (λ baseValue →
          Frechet.add constraint baseValue
            (Frechet.add constraint
              (Frechet.derivative (expansion line) (base line) increment)
              selectedRemainder))
        (constraintAtBaseZero line))
      (trans
        (cong
          (λ derivativeValue →
            Frechet.add constraint (Frechet.zero constraint)
              (Frechet.add constraint derivativeValue selectedRemainder))
          (kernelLineDerivativeZero line scalar))
        (addZeroCollapse line selectedRemainder)))

cmp109ConstraintKernelLineFirstOrderCancellationLevel : ProofLevel
cmp109ConstraintKernelLineFirstOrderCancellationLevel = machineChecked

cmp109ConstraintKernelLineNeedsOnlyFrechetRemainderLevel : ProofLevel
cmp109ConstraintKernelLineNeedsOnlyFrechetRemainderLevel = machineChecked
