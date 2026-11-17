module DASHI.Cognition.PNF.X369SharedHeadFusedScoreExact where

------------------------------------------------------------------------
-- ORIGINAL HISTORY-ORBIT ROUTER: SHARED-HEAD SCORE FUSION
--
-- For the original directed channel triple
--   T(x,h) = (x.h, x.Rh, x.R^-1 h)
-- and ONE SHARED learned directed head (ws,wf,wr),
-- the scalar consumer is exactly
--
--   ws*self + wf*forward + wr*reverse = <K_w x,h>,
--
--   K_w x = (ws*a+wf*c+wr*b,
--            ws*b+wf*a+wr*c,
--            ws*c+wf*b+wr*a).
--
-- This factorization holds for ALL ORIGINAL integer triad inputs and
-- histories, WITHOUT centering, equal DC, quantization or phase labels.
-- K_w x can be reused across any number of expert histories sharing
-- the same x and original learned head. This is a score-consumer
-- fusion, not an invertible encoding of the original T nor a
-- claim of actual GPU speed/energy gain or trained semantic action.
--
-- Original T and weighted head are imported: do not duplicate their
-- mathematical provenance or silently change Leech source semantics.
-- Agda source proposed for pinned kernel verification.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer using (ℤ; +_; _+_; _*_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:-_; _:*_; con; _:=_)
open import Data.Product using (_×_; _,_)

import DASHI.Cognition.PNF.X369DirectedRouterConditionalCodecExact as Original

record SourceAndHead : Set where
  constructor sourceAndHead
  field
    x0 x1 x2 : ℤ
    ws wf wr : ℤ
open SourceAndHead public

record ExpertHistoryTriad : Set where
  constructor expertHistoryTriad
  field
    h0 h1 h2 : ℤ
open ExpertHistoryTriad public

record FusedSource : Set where
  constructor fusedSource
  field
    coefficientH0 coefficientH1 coefficientH2 : ℤ
open FusedSource public

precomputeSharedSource : SourceAndHead → FusedSource
precomputeSharedSource (sourceAndHead a b c ws wf wr) =
  fusedSource
    ((ws * a + wf * c) + wr * b)
    ((ws * b + wf * a) + wr * c)
    ((ws * c + wf * b) + wr * a)

fusedExpertDot : FusedSource → ExpertHistoryTriad → ℤ
fusedExpertDot (fusedSource u v w)
  (expertHistoryTriad A B C) =
  ((u * A + v * B) + w * C)

originalExpertDirectedScore :
  SourceAndHead → ExpertHistoryTriad → ℤ
originalExpertDirectedScore
  (sourceAndHead a b c ws wf wr)
  (expertHistoryTriad A B C) =
  Original.directedWeightedScore ws wf wr
    (Original.originalDirected a b c A B C)

rawOriginalScoreFuses :
  (a b c A B C ws wf wr : ℤ) →
  (((ws * (a * A + b * B + c * C))
    + (wf * (a * B + b * C + c * A)))
    + (wr * (a * C + b * A + c * B)))
  ≡ (((((ws * a + wf * c) + wr * b) * A)
      + (((ws * b + wf * a) + wr * c) * B))
      + (((ws * c + wf * b) + wr * a) * C))
rawOriginalScoreFuses a b c A B C ws wf wr =
  solve 9
    (λ a b c A B C ws wf wr →
      ((((ws :* (((a :* A) :+ (b :* B)) :+ (c :* C)))
         :+ (wf :* (((a :* B) :+ (b :* C)) :+ (c :* A))))
         :+ (wr :* (((a :* C) :+ (b :* A)) :+ (c :* B))))
       :=
       ((((((ws :* a) :+ (wf :* c)) :+ (wr :* b)) :* A)
        :+ (((((ws :* b) :+ (wf :* a)) :+ (wr :* c)) :* B))
        :+ (((((ws :* c) :+ (wf :* b)) :+ (wr :* a)) :* C))))
    refl a b c A B C ws wf wr

sourceScoreEqualsFusedConsumer :
  (source : SourceAndHead) (history : ExpertHistoryTriad) →
  originalExpertDirectedScore source history
  ≡ fusedExpertDot (precomputeSharedSource source) history
sourceScoreEqualsFusedConsumer
  (sourceAndHead a b c ws wf wr)
  (expertHistoryTriad A B C) =
  rawOriginalScoreFuses a b c A B C ws wf wr

-- Reuse ONE precomputed K_w x across ARBITRARILY MANY independently
-- maintained expert histories, as in the original shared-head MoE.
originalExpertScores :
  SourceAndHead → List ExpertHistoryTriad → List ℤ
originalExpertScores source [] = []
originalExpertScores source (history ∷ histories) =
  originalExpertDirectedScore source history
  ∷ originalExpertScores source histories

fusedExpertScores :
  FusedSource → List ExpertHistoryTriad → List ℤ
fusedExpertScores shared [] = []
fusedExpertScores shared (history ∷ histories) =
  fusedExpertDot shared history
  ∷ fusedExpertScores shared histories

allExpertScoresExactlyPreserved :
  (source : SourceAndHead)
  (histories : List ExpertHistoryTriad) →
  originalExpertScores source histories
  ≡ fusedExpertScores (precomputeSharedSource source) histories
allExpertScoresExactlyPreserved source [] = refl
allExpertScoresExactlyPreserved source (history ∷ histories)
  rewrite sourceScoreEqualsFusedConsumer source history
        | allExpertScoresExactlyPreserved source histories = refl

-- For a whole hidden layer of triads (x_j,h_ej,w_j),
-- the source score is a sum of blocks. Each block factors exactly,
-- so the full source score is equal without any finite length bound.
record OriginalTriadScoringBlock : Set where
  constructor originalTriadScoringBlock
  field
    shared : SourceAndHead
    history : ExpertHistoryTriad
open OriginalTriadScoringBlock public

sourceBlockSum : List OriginalTriadScoringBlock → ℤ
sourceBlockSum [] = (+ 0)
sourceBlockSum (block ∷ rest) =
  originalExpertDirectedScore (shared block) (history block)
  + sourceBlockSum rest

fusedBlockSum : List OriginalTriadScoringBlock → ℤ
fusedBlockSum [] = (+ 0)
fusedBlockSum (block ∷ rest) =
  fusedExpertDot (precomputeSharedSource (shared block))
    (history block)
  + fusedBlockSum rest

allSourceTriadBlocksExactlyPreserved :
  (blocks : List OriginalTriadScoringBlock) →
  sourceBlockSum blocks ≡ fusedBlockSum blocks
allSourceTriadBlocksExactlyPreserved [] = refl
allSourceTriadBlocksExactlyPreserved (block ∷ rest)
  rewrite
    sourceScoreEqualsFusedConsumer (shared block) (history block)
  | allSourceTriadBlocksExactlyPreserved rest = refl

-- If all source logits are identical, ALL deterministic consumers
-- of those logits (including the same TopK sorting and softmax)
-- receive identical scores. This proof is exact ℤ arithmetic.
-- It does not assert bitwise floating-point reassociation parity,
-- equal runtime, equal GPU kernel, identical optimizer gradients,
-- or reconstruction of the original three-channel feature tensor.
