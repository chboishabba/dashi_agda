module DASHI.Physics.YangMills.QuaternionConjugationProductExact where

-- Shared identity for Hopf principal-circle actions and SU2/YM
-- conjugation/adjoint transport: conjugate(xy)=conjugate(y)conjugate(x).
-- Explicit polynomial computation reuses the Balaban quaternion carrier.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using ([]; _∷_)
import Tactic.RingSolver as Solver
import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier as Q

conjugateProduct : (x y : Q.Quaternion) →
  Q.conjugateQ (Q._*q_ x y) ≡
  Q._*q_ (Q.conjugateQ y) (Q.conjugateQ x)
conjugateProduct (Q.quat a b c d) (Q.quat e f g h) =
  Q.quaternionExt
    (Solver.solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ [])
      Q.realSolverRing)
    (Solver.solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ [])
      Q.realSolverRing)
    (Solver.solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ [])
      Q.realSolverRing)
    (Solver.solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ [])
      Q.realSolverRing)
