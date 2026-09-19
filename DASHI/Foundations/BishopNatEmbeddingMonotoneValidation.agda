module DASHI.Foundations.BishopNatEmbeddingMonotoneValidation where

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)

import Real as BishopReal
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NatReal
import DASHI.Foundations.BishopNatEmbeddingMonotoneExact as P

natRealMonotoneRegression :
  ∀ {m n : Nat} →
  m ≤ n →
  BishopReal._≤_ (NatReal.natReal m) (NatReal.natReal n)
natRealMonotoneRegression = P.natRealMonotone
