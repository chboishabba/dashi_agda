{-# OPTIONS --safe #-}
module DASHI.Reasoning.LeechSignedHistoryExpertBidiExact where

------------------------------------------------------------------------
-- FINITE EXACT CORE FOR HISTORY-CONSTITUTED SIGNED EXPERTS
--
-- Historical motivation: Anatolii Kornienko, Leech-LILA E8/Leech
-- training observations (GitHub issue #3, March 2026). The developer
-- proposed a geometric suppression hypothesis, not a proven safety
-- classifier. Do not equate ± orientation with moral labels.
--
-- In-repository mathematical owners:
-- DASHI.Foundations.BalancedTernaryAntipodalOrbitExact
-- DASHI.Biology.TriadicKernelLiftQuotientExact
-- DASHI.Reasoning.HistoryTimeIndexedConsumerFibreExact
--
-- This module constructs a finite signed-history conjugation theorem;
-- NOT a proof of a neural-network Leech automorphism, GELU oddness,
-- safety or a learned empirical routing advantage.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

data Trit : Set where
  negative : Trit
  centre : Trit
  positive : Trit

negate : Trit → Trit
negate negative = positive
negate centre = centre
negate positive = negative

negateInvolutive : (x : Trit) → negate (negate x) ≡ x
negateInvolutive negative = refl
negateInvolutive centre = refl
negateInvolutive positive = refl

data Sign : Set where
  direct : Sign
  inverse : Sign

record HistoryState : Set where
  constructor historyState
  field
    activation : Trit
    memory : Trit

open HistoryState public

invertHistory : HistoryState → HistoryState
invertHistory (historyState x h) = historyState (negate x) (negate h)

invertHistoryInvolutive :
  (state : HistoryState) → invertHistory (invertHistory state) ≡ state
invertHistoryInvolutive (historyState x h)
  rewrite negateInvolutive x | negateInvolutive h = refl

orientHistory : Sign → HistoryState → HistoryState
orientHistory direct state = state
orientHistory inverse state = invertHistory state

restoreOrientation : Sign → HistoryState → HistoryState
restoreOrientation = orientHistory

restoreOrientedHistory :
  (sign : Sign) (state : HistoryState) →
  restoreOrientation sign (orientHistory sign state) ≡ state
restoreOrientedHistory direct state = refl
restoreOrientedHistory inverse state = invertHistoryInvolutive state

-- An abstract expert transition F receives current input and its history
-- *together* and returns output with updated history. The same F serves
-- both conjugate orientations without requiring F itself to be odd.
conjugate : (HistoryState → HistoryState) → Sign →
            HistoryState → HistoryState
conjugate F direct state = F state
conjugate F inverse state = invertHistory (F (invertHistory state))

negativeChart :
  (F : HistoryState → HistoryState) (state : HistoryState) →
  conjugate F inverse state ≡ invertHistory (F (invertHistory state))
negativeChart F state = refl

-- Conjugating the same transition twice restores the original transition.
conjugateTwice :
  (F : HistoryState → HistoryState) (state : HistoryState) →
  conjugate (conjugate F inverse) inverse state ≡ F state
conjugateTwice F state
  rewrite invertHistoryInvolutive state
        | invertHistoryInvolutive (F state) = refl

-- BIDI: the decoder receives the same signed orientation witness as the
-- producer; after reorientation no information about activation or memory
-- was discarded.
producerConsumerRoundtrip :
  (sign : Sign) (state : HistoryState) →
  restoreOrientation sign (orientHistory sign state) ≡ state
producerConsumerRoundtrip = restoreOrientedHistory

-- No Boolean "good"/"evil" polarity, no Co_0 lattice action, and no
-- measured compression ratio are introduced by this finite theorem.
