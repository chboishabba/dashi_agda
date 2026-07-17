module DASHI.Physics.YangMills.BalabanProjectedEndpointDifference where

-- Endpoint form of the projected block determinant identity.
--
-- The projected vacuum-subtracted conditional shell logs sum exactly to the
-- projected endpoint determinant difference.  This is the algebraic formula
-- that the source-specific identification must instantiate with the Gaussian
-- beta contribution.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; suc; _+_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; 0ℝ
  ; _+ℝ_
  ; _-ℝ_
  ; cong
  ; trans
  )
open import DASHI.Physics.YangMills.BalabanInverseSquareCouplingBudget using
  ( InverseSquareBudgetArithmetic )
open import DASHI.Physics.YangMills.BalabanIntervalDeterminantAlgebra using
  ( intervalSum )
open import DASHI.Physics.YangMills.BalabanBlockDeterminantLogAdditivity using
  ( conditionalLogShell )
open import DASHI.Physics.YangMills.BalabanVacuumSubtractionAlgebra using
  ( vacuumDifference )
open import DASHI.Physics.YangMills.BalabanCumulativeBlockCorrection using
  ( cancelLeadingAdd )
open import DASHI.Physics.YangMills.BalabanProjectionIntervalLinearity using
  ( projectedVacuumSubtractedBlockDeterminantInterval )

sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

projectedConditionalShell :
  {Background Scalar : Set} →
  (Scalar → ℝ) →
  (Background → ℕ → Scalar) →
  (ℝ → ℝ) →
  Background → Background →
  ℕ → ℝ
projectedConditionalShell
  logDet conditional projection background vacuum shell =
  projection
    (conditionalLogShell logDet (conditional background) shell
      -ℝ conditionalLogShell logDet (conditional vacuum) shell)

projectedConditionalShellsEqualEndpointDifference :
  {Background Scalar : Set} →
  (arith : InverseSquareBudgetArithmetic) →
  (one : Scalar) →
  (_*_ : Scalar → Scalar → Scalar) →
  (assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)) →
  (rightIdentity : ∀ a → a * one ≡ a) →
  (determinant conditional : Background → ℕ → Scalar) →
  (step :
    ∀ B j →
    determinant B (suc j)
      ≡ determinant B j * conditional B j) →
  (logDet : Scalar → ℝ) →
  logDet one ≡ 0ℝ →
  (logMul : ∀ a b → logDet (a * b) ≡ logDet a +ℝ logDet b) →
  (projection : ℝ → ℝ) →
  projection 0ℝ ≡ 0ℝ →
  (projectionAdd :
    ∀ a b →
    projection (a +ℝ b)
      ≡ projection a +ℝ projection b) →
  (background vacuum : Background) →
  ∀ k n →
  intervalSum
    (projectedConditionalShell
      logDet conditional projection background vacuum)
    k n
  ≡ projection
      (vacuumDifference
        (λ B → logDet (determinant B (n + k)))
        background vacuum)
      -ℝ projection
        (vacuumDifference
          (λ B → logDet (determinant B k))
          background vacuum)
projectedConditionalShellsEqualEndpointDifference
  arith one _*_ assoc rightIdentity
  determinant conditional step
  logDet logOne logMul
  projection projectionZero projectionAdd
  background vacuum k n =
  let
    start = projection
      (vacuumDifference
        (λ B → logDet (determinant B k))
        background vacuum)
    finish = projection
      (vacuumDifference
        (λ B → logDet (determinant B (n + k)))
        background vacuum)
    shells = intervalSum
      (projectedConditionalShell
        logDet conditional projection background vacuum)
      k n

    endpointEvolution = projectedVacuumSubtractedBlockDeterminantInterval
      one _*_ assoc rightIdentity
      determinant conditional step
      logDet logOne logMul
      projection projectionZero projectionAdd
      background vacuum k n
    p1 = cong (λ endpoint → endpoint -ℝ start) endpointEvolution
    p2 = cancelLeadingAdd arith start shells
  in
    sym (trans p1 p2)
