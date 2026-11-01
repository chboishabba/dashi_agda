{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityBishopMatchedRecursionResidualExact where

import Real as Bishop
import RealProperties as BishopP

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- MATCHED ADDITIVE RECURSIONS FORCE THE SAME RESIDUAL
--
-- If
--
--   next ~= base + (lead + residual)
--   next ~= base + (lead + targetResidual),
--
-- then constructive Bishop-real additive cancellation gives
--
--   residual ~= targetResidual.
--
-- This is the algebraic step needed to stop accepting the P3 remainder
-- same-object equation as an independent physical premise.
------------------------------------------------------------------------

subtractCongruentRight :
  ∀ {left right common : Bishop.ℝ} →
  Bishop._≃_ left right →
  Bishop._≃_
    (Bishop._-_ left common)
    (Bishop._-_ right common)
subtractCongruentRight equality =
  BishopP.+-cong equality (BishopP.-‿cong BishopP.≃-refl)

subtractAddedLeft :
  ∀ left right →
  Bishop._≃_
    (Bishop._-_ (Bishop._+_ left right) left)
    right
subtractAddedLeft left right =
  solve 2
    (λ x y → ((x ⊕ y) ⊖ x) ⊜ y)
    BishopP.≃-refl
    left right
  where
    open BishopP.ℝ-Solver

bishopAddLeftCancel :
  ∀ {common left right : Bishop.ℝ} →
  Bishop._≃_
    (Bishop._+_ common left)
    (Bishop._+_ common right) →
  Bishop._≃_ left right
bishopAddLeftCancel {common} {left} {right} equality =
  BishopP.≃-trans
    (BishopP.≃-symm (subtractAddedLeft common left))
    (BishopP.≃-trans
      (subtractCongruentRight equality)
      (subtractAddedLeft common right))

record MatchedAdditiveRecursions : Set₁ where
  field
    next base lead residual targetResidual : Bishop.ℝ

    firstRecursion :
      Bishop._≃_
        next
        (Bishop._+_ base (Bishop._+_ lead residual))

    secondRecursion :
      Bishop._≃_
        next
        (Bishop._+_ base (Bishop._+_ lead targetResidual))

open MatchedAdditiveRecursions public

matchedRecursionsForceResidual :
  (dataSet : MatchedAdditiveRecursions) →
  Bishop._≃_
    (residual dataSet)
    (targetResidual dataSet)
matchedRecursionsForceResidual dataSet =
  let
    outer :
      Bishop._≃_
        (Bishop._+_
          (base dataSet)
          (Bishop._+_ (lead dataSet) (residual dataSet)))
        (Bishop._+_
          (base dataSet)
          (Bishop._+_ (lead dataSet) (targetResidual dataSet)))
    outer =
      BishopP.≃-trans
        (BishopP.≃-symm (firstRecursion dataSet))
        (secondRecursion dataSet)

    inner :
      Bishop._≃_
        (Bishop._+_ (lead dataSet) (residual dataSet))
        (Bishop._+_ (lead dataSet) (targetResidual dataSet))
    inner = bishopAddLeftCancel outer
  in
  bishopAddLeftCancel inner

bishopMatchedRecursionResidualCompilerLevel : ProofLevel
bishopMatchedRecursionResidualCompilerLevel = machineChecked
