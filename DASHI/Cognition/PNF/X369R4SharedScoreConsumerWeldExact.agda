module DASHI.Cognition.PNF.X369R4SharedScoreConsumerWeldExact where

------------------------------------------------------------------------
-- R4 SOURCE SCORE CONSUMER WELD (integer exact arithmetic)
--
-- R4 baseline source router = shared unary abs(x), expert-dependent
-- C2 history abs(h_e), common nn.Linear bias, and expert_bias[e].
-- In coherent/mixed C3 residual arms, the learned R4 residual head
-- = unary C3 invariant(phase_x) + directed T(phase_x,h_e).
-- ALL unary x portions are identical across candidate experts.
--
-- This module formalizes the conditional *score consumer* factorization
-- through the existing X369SharedHeadFusedScoreExact owner, preserving
-- one common unary term and one exact expert C2-history term per expert.
-- It does not reimplement absolute values, source torch float arithmetic,
-- original q-mask threshold, softmax, the native topk tie policy,
-- or the physical recurrent transition.
--
-- Source references:
-- LeechTransformer/models/history_orbit_moe.py select_source_experts
-- LeechTransformer/models/trialectic_wave_prior.py
--     directed_trialectic_invariants, trialectic_router_invariants
-- Original Leech-LILA attribution: Anatolii Kornienko.
--
-- Proposed Agda formalism. Kernel check deliberately not claimed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer using (ℤ; _+_; _-_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:-_; _:*_; _:=_)

import DASHI.Cognition.PNF.X369SharedHeadFusedScoreExact as Fused

record R4Shared : Set where
  constructor r4Shared
  field
    directedSource : Fused.SourceAndHead
    sourceUnaryIncludingRouterBias : ℤ
open R4Shared public

record R4Expert : Set where
  constructor r4Expert
  field
    originalHistory : Fused.ExpertHistoryTriad
    originalC2AbsHistoryHeadScore : ℤ
    originalExpertBias : ℤ
open R4Expert public

originalR4Score : R4Shared → R4Expert → ℤ
originalR4Score source expert =
  ((sourceUnaryIncludingRouterBias source
    + originalC2AbsHistoryHeadScore expert)
    + Fused.originalExpertDirectedScore
        (directedSource source) (originalHistory expert))
    + originalExpertBias expert

fusedR4Score : R4Shared → R4Expert → ℤ
fusedR4Score source expert =
  ((sourceUnaryIncludingRouterBias source
    + originalC2AbsHistoryHeadScore expert)
    + Fused.fusedExpertDot
        (Fused.precomputeSharedSource (directedSource source))
        (originalHistory expert))
    + originalExpertBias expert

originalR4ScoreFactorsThroughFusedHead :
  (source : R4Shared) (expert : R4Expert) →
  originalR4Score source expert ≡ fusedR4Score source expert
originalR4ScoreFactorsThroughFusedHead source expert
  rewrite Fused.sourceScoreEqualsFusedConsumer
    (directedSource source) (originalHistory expert) = refl

originalR4ScoreList : R4Shared → List R4Expert → List ℤ
originalR4ScoreList source [] = []
originalR4ScoreList source (expert ∷ rest) =
  originalR4Score source expert ∷ originalR4ScoreList source rest

fusedR4ScoreList : R4Shared → List R4Expert → List ℤ
fusedR4ScoreList source [] = []
fusedR4ScoreList source (expert ∷ rest) =
  fusedR4Score source expert ∷ fusedR4ScoreList source rest

everyExpertScorePreserved :
  (source : R4Shared) (experts : List R4Expert) →
  originalR4ScoreList source experts
  ≡ fusedR4ScoreList source experts
everyExpertScorePreserved source [] = refl
everyExpertScorePreserved source (expert ∷ rest)
  rewrite originalR4ScoreFactorsThroughFusedHead source expert
        | everyExpertScorePreserved source rest = refl

everyOrderedScoreListConsumerPreserved :
  ∀ {Outcome : Set}
  (consume : List ℤ → Outcome)
  (source : R4Shared) (experts : List R4Expert) →
  consume (originalR4ScoreList source experts)
  ≡ consume (fusedR4ScoreList source experts)
everyOrderedScoreListConsumerPreserved consume source experts =
  cong consume (everyExpertScorePreserved source experts)
  where
    cong : ∀ {X Y : Set}{a b : X} →
      (f : X → Y) → a ≡ b → f a ≡ f b
    cong f refl = refl

------------------------------------------------------------------------
-- A shared unary x-only score and shared nn.Linear bias are exact
-- gauge directions for ideal expert-pair score DIFFERENCES. This
-- does not remove expert-specific C2 history, directed T or bias.
------------------------------------------------------------------------

commonUnaryCancelsRelativeScores :
  (common hi hj bi bj : ℤ) →
  (((common + hi) + bi) - ((common + hj) + bj))
    ≡ ((hi + bi) - (hj + bj))
commonUnaryCancelsRelativeScores common hi hj bi bj =
  solve 5
    (λ common hi hj bi bj →
      ((((common :+ hi) :+ bi)
        :- ((common :+ hj) :+ bj))
       := ((hi :+ bi) :- (hj :+ bj))))
    refl common hi hj bi bj
-- The original baseline history contribution must be sourced from
-- the actual v_h * abs(h) computation, not inferred from the
-- directed score; this record treats that observed contribution
-- as its own input. The q-gated mixed arm additionally needs a
-- certified unchanged branch before fused-source perturbation
-- bounds apply, while coherent C3 has a fixed rotation.
--
-- If exact ordered per-expert source logits are supplied, any
-- deterministic consumer of the entire ordered score list
-- (including a fixed tie policy) is identical in exact ℤ.
-- Quantized logits, floating point and future histories have
-- distinct proof obligations in the existing DASHI owners.
