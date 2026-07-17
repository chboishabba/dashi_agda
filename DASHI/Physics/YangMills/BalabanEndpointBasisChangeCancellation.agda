module DASHI.Physics.YangMills.BalabanEndpointBasisChangeCancellation where

-- Background-independent basis/rescaling determinants may depend on the RG
-- scale, but still cancel separately at each endpoint under vacuum subtraction.
-- This is the exact algebra needed for fixed rescaling maps R_j in a cumulative
-- determinant comparison.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (ℕ)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _+ℝ_
  ; _-ℝ_
  ; cong
  ; trans
  )
open import DASHI.Physics.YangMills.BalabanVacuumSubtractionAlgebra using
  ( vacuumDifference
  ; backgroundIndependentTermCancels
  )

scaleVacuumDifferenceIgnoresBasisConstant :
  {Background : Set} →
  (transformed original : ℕ → Background → ℝ) →
  (basisConstant : ℕ → ℝ) →
  (basisChange :
    ∀ scale B →
    transformed scale B
      ≡ original scale B +ℝ basisConstant scale) →
  (background vacuum : Background) →
  ∀ scale →
  vacuumDifference (transformed scale) background vacuum
    ≡ vacuumDifference (original scale) background vacuum
scaleVacuumDifferenceIgnoresBasisConstant
  transformed original basisConstant basisChange
  background vacuum scale =
  backgroundIndependentTermCancels
    (transformed scale)
    (original scale)
    (basisConstant scale)
    (basisChange scale)
    background vacuum

endpointBasisChangeCancels :
  {Background : Set} →
  (transformed original : ℕ → Background → ℝ) →
  (basisConstant : ℕ → ℝ) →
  (basisChange :
    ∀ scale B →
    transformed scale B
      ≡ original scale B +ℝ basisConstant scale) →
  (background vacuum : Background) →
  ∀ start finish →
  vacuumDifference (transformed finish) background vacuum
    -ℝ vacuumDifference (transformed start) background vacuum
  ≡ vacuumDifference (original finish) background vacuum
      -ℝ vacuumDifference (original start) background vacuum
endpointBasisChangeCancels
  transformed original basisConstant basisChange
  background vacuum start finish =
  let
    finishEquality = scaleVacuumDifferenceIgnoresBasisConstant
      transformed original basisConstant basisChange
      background vacuum finish
    startEquality = scaleVacuumDifferenceIgnoresBasisConstant
      transformed original basisConstant basisChange
      background vacuum start
    p1 = cong
      (λ finishValue →
        finishValue
          -ℝ vacuumDifference (transformed start) background vacuum)
      finishEquality
    p2 = cong
      (λ startValue →
        vacuumDifference (original finish) background vacuum
          -ℝ startValue)
      startEquality
  in
    trans p1 p2

projectedEndpointBasisChangeCancels :
  {Background : Set} →
  (transformed original : ℕ → Background → ℝ) →
  (basisConstant : ℕ → ℝ) →
  (basisChange :
    ∀ scale B →
    transformed scale B
      ≡ original scale B +ℝ basisConstant scale) →
  (projection : ℝ → ℝ) →
  (background vacuum : Background) →
  ∀ start finish →
  projection
    (vacuumDifference (transformed finish) background vacuum
      -ℝ vacuumDifference (transformed start) background vacuum)
  ≡ projection
    (vacuumDifference (original finish) background vacuum
      -ℝ vacuumDifference (original start) background vacuum)
projectedEndpointBasisChangeCancels
  transformed original basisConstant basisChange
  projection background vacuum start finish =
  cong projection
    (endpointBasisChangeCancels
      transformed original basisConstant basisChange
      background vacuum start finish)
