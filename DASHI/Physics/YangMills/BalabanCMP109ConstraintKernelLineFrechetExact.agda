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
-- C(A)=0, and h is in ker DC(A), then linearity on the scalar line gives
--
--   C(A+t h) = r_A(t h).
--
-- Hence the ordinary Frechet little-o remainder, not a two-background
-- Lipschitz theorem for DC, is the exact analytic input needed by the normal
-- correction argument.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4FiniteDimensionalFrechetChainProductExact as Frechet
import DASHI.Physics.YangMills.BalabanFiniteStrictContractionReopeningExact as Reopen

vectorAdd : ∀ {Index : Set} → Reopen.Vector Index → Reopen.Vector Index → Reopen.Vector Index
vectorAdd left right index = left index + right index

vectorScale : ∀ {Index : Set} → ℚ → Reopen.Vector Index → Reopen.Vector Index
vectorScale scalar vector index = scalar * vector index

vectorAddAssociative :
  ∀ {Index : Set} (left middle right : Reopen.Vector Index) →
  vectorAdd (vectorAdd left middle) right ≡ vectorAdd left (vectorAdd middle right)
vectorAddAssociative left middle right =
  refl

vectorAdditiveCarrier : ∀ {Index : Set} → Frechet.AdditiveCarrier (Reopen.Vector Index)
vectorAdditiveCarrier = record
  { Frechet.AdditiveCarrier.zero = Reopen.zeroVector
  ; Frechet.AdditiveCarrier.add = vectorAdd
  ; Frechet.AdditiveCarrier.addAssociative = vectorAddAssociative
  }

record ConstraintFrechetKernelLine
    (StateIndex ConstraintIndex : Set) : Set₁ where
  field
    expansion : Frechet.ExactFirstOrderExpansion
      (vectorAdditiveCarrier {StateIndex})
      (vectorAdditiveCarrier {ConstraintIndex})

    base : Reopen.Vector StateIndex
    direction : Reopen.Vector StateIndex

    constraintAtBaseZero : ∀ row →
      Frechet.function expansion base row ≡ 0ℚ

    kernelDirection : ∀ row →
      Frechet.derivative expansion base direction row ≡ 0ℚ

    derivativeScalesOnKernelLine : ∀ scalar row →
      Frechet.derivative expansion base (vectorScale scalar direction) row
      ≡ scalar * Frechet.derivative expansion base direction row

open ConstraintFrechetKernelLine public

kernelLineDerivativeZero :
  ∀ {StateIndex ConstraintIndex}
    (line : ConstraintFrechetKernelLine StateIndex ConstraintIndex)
    scalar row →
  Frechet.derivative (expansion line) (base line)
    (vectorScale scalar (direction line)) row
  ≡ 0ℚ
kernelLineDerivativeZero line scalar row =
  trans
    (derivativeScalesOnKernelLine line scalar row)
    (trans
      (cong (scalar *_) (kernelDirection line row))
      (ℚRing.solve []))

selectedConstraintKernelLineResidualIsFrechetRemainder :
  ∀ {StateIndex ConstraintIndex}
    (line : ConstraintFrechetKernelLine StateIndex ConstraintIndex)
    scalar row →
  Frechet.function (expansion line)
    (vectorAdd (base line) (vectorScale scalar (direction line))) row
  ≡ Frechet.remainder (expansion line) (base line)
      (vectorScale scalar (direction line)) row
selectedConstraintKernelLineResidualIsFrechetRemainder line scalar row =
  let
    increment = vectorScale scalar (direction line)
    expanded = Frechet.incrementExpansion (expansion line) (base line) increment
  in
  trans
    (cong (λ vector → vector row) expanded)
    (trans
      (cong
        (λ baseValue →
          vectorAdd baseValue
            (vectorAdd
              (Frechet.derivative (expansion line) (base line) increment)
              (Frechet.remainder (expansion line) (base line) increment)) row)
        (constraintAtBaseZero line row))
      (trans
        (cong
          (λ derivativeValue →
            0ℚ + (derivativeValue
              + Frechet.remainder (expansion line) (base line) increment row))
          (kernelLineDerivativeZero line scalar row))
        (ℚRing.solve-∀
          (Frechet.remainder (expansion line) (base line) increment row))))

cmp109ConstraintKernelLineFirstOrderCancellationLevel : ProofLevel
cmp109ConstraintKernelLineFirstOrderCancellationLevel = machineChecked

-- The only analytic datum after this theorem is the little-o property of the
-- remainder of the literal constraint expansion at the selected background.
cmp109ConstraintKernelLineNeedsOnlyFrechetRemainderLevel : ProofLevel
cmp109ConstraintKernelLineNeedsOnlyFrechetRemainderLevel = machineChecked
