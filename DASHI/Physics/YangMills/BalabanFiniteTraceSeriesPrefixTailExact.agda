module DASHI.Physics.YangMills.BalabanFiniteTraceSeriesPrefixTailExact where

------------------------------------------------------------------------
-- ROUND84: FINITE SERIES PREFIX/TAIL SPLITTING IS PURE ALGEBRA
--
-- This is the finite same-object identity consumed by the reduced ghost
-- trace-log sequence.  No convergence theorem, determinant theorem, or
-- Yang--Mills estimate is involved.
--
-- For an arbitrary scalar term sequence a_n define
--
--   S_0 = 0,
--   S_{n+1} = S_n + a_n.
--
-- For a start m and a finite count k define the appended tail
--
--   T(m,0) = 0,
--   T(m,k+1) = T(m,k) + a_{m+k}.
--
-- Then exactly
--
--   S_{m+k} = S_m + T(m,k),
--
-- hence
--
--   S_{m+k} - S_m = T(m,k).
--
-- The custom `advance` below recurses on the tail count so the proof does not
-- depend on a library normalization convention for Nat addition.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel

advance : Nat → Nat → Nat
advance start zero = start
advance start (suc count) = suc (advance start count)

partialTrace : (Nat → ℚ) → Nat → ℚ
partialTrace term zero = 0ℚ
partialTrace term (suc n) = partialTrace term n + term n

appendedTail : (Nat → ℚ) → Nat → Nat → ℚ
appendedTail term start zero = 0ℚ
appendedTail term start (suc count) =
  appendedTail term start count + term (advance start count)

partialAtAdvanceSplits :
  (term : Nat → ℚ) → ∀ start count →
  partialTrace term (advance start count)
  ≡ partialTrace term start + appendedTail term start count
partialAtAdvanceSplits term start zero = ℚRing.solve-∀ (partialTrace term start)
partialAtAdvanceSplits term start (suc count)
  rewrite partialAtAdvanceSplits term start count =
  ℚRing.solve-∀
    (partialTrace term start)
    (appendedTail term start count)
    (term (advance start count))

partialDifferenceIsAppendedTail :
  (term : Nat → ℚ) → ∀ start count →
  partialTrace term (advance start count) - partialTrace term start
  ≡ appendedTail term start count
partialDifferenceIsAppendedTail term start count
  rewrite partialAtAdvanceSplits term start count =
  ℚRing.solve-∀
    (partialTrace term start)
    (appendedTail term start count)

finiteTraceSeriesPrefixTailLevel : ProofLevel
finiteTraceSeriesPrefixTailLevel = machineChecked

-- Applying this identity to the literal reduced-ghost trace-log sequence only
-- requires defining `term n` to be the actual signed trace coefficient.  The
-- finite prefix/tail equality itself is not a remaining physical theorem.
