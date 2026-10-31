{-# OPTIONS --safe #-}
module DASHI.Reasoning.LeechLearnedOrbitMixtureBidiExact where

------------------------------------------------------------------------
-- SYNC WITH LeechTransformer/models/history_orbit_moe.py
-- Model is a finite skeleton of distinct learned expert families, not
-- a kernel proof of PyTorch floating tensors, top-k or gradient descent.
-- Original Leech-LILA architectural attribution: Anatolii Kornienko.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Reasoning.LeechSignedHistoryExpertBidiExact as Sign

data ExpertId : Set where
  expertZero : ExpertId
  expertOne : ExpertId

-- Distinct *slots* permit independently learned functions.
-- No false assumption of sharing parameters across distinct experts.
ExpertFamily : Set
ExpertFamily = ExpertId → Sign.HistoryState → Sign.HistoryState

record Router : Set where
  constructor router
  field
    choose : Sign.HistoryState → ExpertId

open Router public

dispatch : ExpertFamily → Router → Sign.HistoryState → Sign.HistoryState
dispatch family routing state = family (choose routing state) state

-- A fixed orientation witness acts by conjugation inside the *selected*
-- learned expert. It does not substitute for learning a selected family.
orientedDispatch :
  ExpertFamily → Router → Sign.Sign →
  Sign.HistoryState → Sign.HistoryState
orientedDispatch family routing orientation state =
  Sign.conjugate (family (choose routing state)) orientation state

selectedDirectIsLearnedFamily :
  (family : ExpertFamily) (routing : Router) (state : Sign.HistoryState) →
  orientedDispatch family routing Sign.direct state ≡ dispatch family routing state
selectedDirectIsLearnedFamily family routing state = refl

-- A router must itself respect the joint history involution for a
-- global orientation commuting square. The implementation's separate
-- routing logits do NOT establish this automatically.
record EquivariantRouter (routing : Router) : Set where
  field
    chooseInversionInvariant :
      (state : Sign.HistoryState) →
      choose routing (Sign.invertHistory state) ≡ choose routing state

open EquivariantRouter public

selectedConjugationSquare :
  (family : ExpertFamily) (routing : Router) →
  EquivariantRouter routing →
  (state : Sign.HistoryState) →
  orientedDispatch family routing Sign.inverse (Sign.invertHistory state)
  ≡ Sign.invertHistory (dispatch family routing state)
selectedConjugationSquare family routing receipt state
  rewrite chooseInversionInvariant receipt state =
    Sign.conjugateIntertwinesInverse
      (family (choose routing state)) state

-- Mixture weights, shared outputs, separate histories and true top-k
-- are executable-level obligations, not hidden in this two-expert finite
-- dispatch skeleton. In particular, sign must not be conflated with
-- benevolence/harmfulness or with a proved Leech automorphism.
