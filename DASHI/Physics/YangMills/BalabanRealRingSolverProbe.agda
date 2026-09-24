module DASHI.Physics.YangMills.BalabanRealRingSolverProbe where

------------------------------------------------------------------------
-- Minimal regression probe for the exact solver socket used by the concrete
-- SU(2) lane.  This module deliberately does not import the quaternion carrier:
-- it must establish first that the reflective solver recognises the public
-- operation names definitionally.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (sym)

import Tactic.RingSolver as Solver

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanRealPolynomialRing using
  ( _+R_
  ; _*R_
  ; -R_
  ; oneR
  ; *-identityˡ
  ; realSolverRing
  )
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  ( module RealPolynomialSolver )
open RealPolynomialSolver using
  ( Polynomial; solve; _:=_; _:+_; _:*_; :-_ )

solverRawRingProbe :
  ∀ (a b c : ℝ) →
  -R ((a +R b) *R c)
    ≡ ((-R (a *R c)) +R (-R (b *R c)))
solverRawRingProbe a b c =
  Solver.solve (a ∷ b ∷ c ∷ []) realSolverRing

solverRawRingConstantProbe :
  -R (oneR *R oneR)
    ≡ oneR *R (-R (oneR *R oneR))
solverRawRingConstantProbe =
  sym (*-identityˡ (-R (oneR *R oneR)))

coefficientSolverCancellationProbe :
  ∀ (a b : ℝ) →
  (a *R (-R b)) +R (b *R a) ≡ a +R (-R a)
coefficientSolverCancellationProbe =
  solve 2
    (λ a b →
      (a :* (:- b)) :+ (b :* a)
      :=
      a :+ (:- a))
    refl
