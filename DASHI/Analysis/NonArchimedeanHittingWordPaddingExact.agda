module DASHI.Analysis.NonArchimedeanHittingWordPaddingExact where

------------------------------------------------------------------------
-- EXACT HITTING-WORD PADDING
--
-- Convert an arbitrary forward-generator word into the indexed binary-word
-- carrier used by complete branch enumeration.  If its length k is bounded by
-- a uniform block length m, pad with branch-0 symbols after the original word
-- and transport along m-k+k=m to obtain a BinaryWord m.
--
-- The stopping semantics remain separate: this module does not assert that a
-- padded word is killed.  That follows only when the original prefix has
-- already hit an absorbing target.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_; _∸_; _+_)
open import Data.Nat.Properties using (m∸n+n≡m)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Analysis.NonArchimedeanForwardTranslationIrreducibilityCompilerExact as Forward
import DASHI.Analysis.NonArchimedeanFiniteUniformHittingBlockCompilerExact as Uniform
import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary

forwardToBinary :
  {data : Forward.ForwardTranslationData} →
  (word : Forward.ForwardWord data) →
  Binary.BinaryWord (Uniform.wordLength word)
forwardToBinary Forward.done = Binary.end
forwardToBinary (Forward.useA word) = Binary.bit0 (forwardToBinary word)
forwardToBinary (Forward.useB word) = Binary.bit1 (forwardToBinary word)

padFrontZero :
  {n : Nat} →
  (extra : Nat) →
  Binary.BinaryWord n →
  Binary.BinaryWord (extra + n)
padFrontZero zero word = word
padFrontZero (suc extra) word = Binary.bit0 (padFrontZero extra word)

padForwardWordToBound :
  {data : Forward.ForwardTranslationData} →
  (word : Forward.ForwardWord data) →
  (bound : Nat) →
  Uniform.wordLength word ≤ bound →
  Binary.BinaryWord bound
padForwardWordToBound word bound length≤bound =
  let
    k = Uniform.wordLength word
    raw = padFrontZero (bound ∸ k) (forwardToBinary word)
    exactLength = m∸n+n≡m length≤bound
  in
  subst Binary.BinaryWord exactLength raw
