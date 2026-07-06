module DASHI.Physics.Closure.NSTriadKNForcedTailBoundInterpretation where

----------------------------------------------------------------------
-- Forced-tail ℕ-scaled to abstract Bound interpretation (Lemma 4).
--
-- The concrete ℕ arithmetic (ConcreteNatBounds) proves:
--
--   N² · M_FT(N,c) ≤ B_FT,c · D(N,c)      (ℕ)
--
-- The abstract CountingMagnitudeTheoremModel expects:
--
--   N² · M_FT(N,c) · μ_FT(N,c) ≤ B_FT,c    (Bound)
--
-- where μ_FT(N,c) = D(N,c)^{-1} is the classwise magnitude bound.
--
-- Interpretation:
--   In ℝ, substitute μ_FT(N,c) = D(N,c)^{-1}:
--     N² · M_FT(N,c) · D(N,c)^{-1} ≤ B_FT,c
--     ⇔  N² · M_FT(N,c) ≤ B_FT,c · D(N,c)
--   This is exactly the ℕ inequality proved in ConcreteNatBounds.
--
-- So the abstract Bound product formula is discharged by the ℕ
-- arithmetic once we interpret the Bound layer as covering ℝ
-- (or a semiring with division by D(N,c)).
--
-- This module names that interpretation theorem.  The actual
-- inhabitation of the abstract model's product-formula field
-- requires a full ℕ → (ℝ or rational) instantiation of the
-- CountingMagnitudeTheoremModel, which is done at that level.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.Nat.Base using (_≤_)

open import DASHI.Physics.Closure.NSTriadKNForcedTailPrimitiveEstimates
  using ( ForcedTailClass )
open import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteNatBounds
  using ( forcedTailN2ScaledArithmetic; forcedTailN2ScaledLHS; forcedTailN2ScaledRHS )

------------------------------------------------------------------------
-- § 1.  Interpretation theorem surface
--
-- The ℕ arithmetic forcedTailN2ScaledArithmetic proves:
--
--   N² · M_FT(N,c)  ≤  B_FT,c · D(N,c)
--
-- Dividing both sides by D(N,c) (in ℝ) gives the abstract Bound
-- product formula:
--
--   N² · M_FT(N,c) · μ_FT(N,c)  ≤  B_FT,c
--
-- This surface names that interpretation as a theorem type.

natScaledArithmeticInterpretsBoundProduct :
  (c : ForcedTailClass) (N : ℕ) →
  forcedTailN2ScaledLHS c N ≤ forcedTailN2ScaledRHS c N
natScaledArithmeticInterpretsBoundProduct c N =
  forcedTailN2ScaledArithmetic c N

-- Status marker: the interpretation theorem surface exists.
boundInterpretationAvailable : Bool
boundInterpretationAvailable = true
