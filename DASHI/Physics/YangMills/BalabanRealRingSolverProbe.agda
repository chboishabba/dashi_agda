module DASHI.Physics.YangMills.BalabanRealRingSolverProbe where

open import Agda.Builtin.Equality using (_≡_)
open import Algebra.Bundles using (CommutativeRing; RawRing)
open import Algebra.Structures using (IsCommutativeRing)
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (nothing)
open import Level using (0ℓ)

import Tactic.RingSolver as Solver
import Tactic.RingSolver.Core.AlmostCommutativeRing as ACR

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; 0ℝ
  ; 1ℝ
  ; _+ℝ_
  ; _*ℝ_
  ; -ℝ_
  )

postulate
  realIsCommutativeRing :
    IsCommutativeRing _≡_ _+ℝ_ _*ℝ_ -ℝ_ 0ℝ 1ℝ

realCommutativeRing : CommutativeRing 0ℓ 0ℓ
{-# INLINE realCommutativeRing #-}
realCommutativeRing = record
  { Carrier = ℝ
  ; _≈_ = _≡_
  ; _+_ = _+ℝ_
  ; _*_ = _*ℝ_
  ; -_ = -ℝ_
  ; 0# = 0ℝ
  ; 1# = 1ℝ
  ; isCommutativeRing = realIsCommutativeRing
  }

realSolverRing : ACR.AlmostCommutativeRing 0ℓ 0ℓ
{-# INLINE realSolverRing #-}
realSolverRing =
  ACR.fromCommutativeRing realCommutativeRing (λ _ → nothing)

solverRawRing : RawRing 0ℓ 0ℓ
{-# INLINE solverRawRing #-}
solverRawRing = ACR.AlmostCommutativeRing.rawRing realSolverRing

module R = RawRing solverRawRing
open R using ()
  renaming
    ( _+_ to _+R_
    ; _*_ to _*R_
    ; -_  to -R_
    ; 0#  to zeroR
    ; 1#  to oneR
    )

solverRawRingProbe :
  ∀ a b c →
  -R ((a +R b) *R c)
    ≡ ((-R (a *R c)) +R (-R (b *R c)))
solverRawRingProbe a b c =
  Solver.solve (a ∷ b ∷ c ∷ []) realSolverRing

solverRawRingConstantProbe :
  -R (oneR *R oneR)
    ≡ oneR *R (-R (oneR *R oneR))
solverRawRingConstantProbe =
  Solver.solve [] realSolverRing