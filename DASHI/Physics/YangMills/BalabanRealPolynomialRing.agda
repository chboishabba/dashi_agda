module DASHI.Physics.YangMills.BalabanRealPolynomialRing where

------------------------------------------------------------------------
-- Exact reflective-ring socket for DASHI's axiomatic real operations.
--
-- The public operation names below are ordinary definitions, not projections
-- renamed from an `AlmostCommutativeRing` record.  The reflective ring solver
-- can therefore normalise the operators occurring in a goal to the same names
-- stored in `realSolverRing`.
--
-- This module adds one explicit foundational assumption only: the already
-- postulated real operations form a commutative ring.  It contains no
-- Yang--Mills theorem or analytic estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Structures using (IsCommutativeRing)
open import Data.Maybe.Base using (nothing)
open import Level using (0ℓ)

import Tactic.RingSolver.Core.AlmostCommutativeRing as ACR

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; 0ℝ
  ; 1ℝ
  ; _+ℝ_
  ; _*ℝ_
  ; -ℝ_
  )

infixl 20 _+R_
infixl 30 _*R_

zeroR : ℝ
zeroR = 0ℝ

oneR : ℝ
oneR = 1ℝ

_+R_ : ℝ → ℝ → ℝ
_+R_ = _+ℝ_

_*R_ : ℝ → ℝ → ℝ
_*R_ = _*ℝ_

-R_ : ℝ → ℝ
-R_ = -ℝ_

postulate
  realIsCommutativeRing :
    IsCommutativeRing _≡_ _+R_ _*R_ -R_ zeroR oneR

realCommutativeRing : CommutativeRing 0ℓ 0ℓ
realCommutativeRing = record
  { Carrier = ℝ
  ; _≈_ = _≡_
  ; _+_ = _+R_
  ; _*_ = _*R_
  ; -_ = -R_
  ; 0# = zeroR
  ; 1# = oneR
  ; isCommutativeRing = realIsCommutativeRing
  }

realSolverRing : ACR.AlmostCommutativeRing 0ℓ 0ℓ
realSolverRing =
  ACR.fromCommutativeRing realCommutativeRing (λ _ → nothing)
