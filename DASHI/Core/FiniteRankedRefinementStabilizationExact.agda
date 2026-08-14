module DASHI.Core.FiniteRankedRefinementStabilizationExact where

open import DASHI.Core.Prelude
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)

record RankedRefinementProcess : Set₁ where
  constructor rankedRefinementProcess
  field
    Code : Set
    advance : Code → Code
    stable? : (code : Code) → Dec (code ≡ advance code)
    rank : Code → Nat
    rankBound : Nat
    rankBounded : (code : Code) → rank code ≤ rankBound
    unstableRaisesRank :
      (code : Code) →
      (code ≡ advance code → ⊥) →
      rank code < rank (advance code)

open RankedRefinementProcess public

iterate : (process : RankedRefinementProcess) → Nat → Code process → Code process
iterate process zero code = code
iterate process (suc n) code = iterate process n (advance process code)

data StrictChain
    (process : RankedRefinementProcess) :
    Nat → Code process → Set where
  chainZero : ∀ {code} → StrictChain process zero code
  chainStep :
    ∀ {length code} →
    rank process code < rank process (advance process code) →
    StrictChain process length (advance process code) →
    StrictChain process (suc length) code

strictChainRankGrowth :
  (process : RankedRefinementProcess) →
  ∀ {length code} →
  StrictChain process length code →
  rank process code + length
  ≤ rank process (iterate process length code)
strictChainRankGrowth process {code = code} chainZero =
  ≤-reflexive (+-identityʳ (rank process code))
strictChainRankGrowth process
  (chainStep {length = length} {code = code} firstStrict rest)
  rewrite +-suc (rank process code) length =
  ≤-trans
    (+-mono-≤ firstStrict ≤-refl)
    (strictChainRankGrowth process rest)

data SearchResult
    (process : RankedRefinementProcess)
    (fuel : Nat)
    (start : Code process) : Set where
  foundStable :
    (depth : Nat) →
    depth ≤ fuel →
    iterate process depth start
      ≡ advance process (iterate process depth start) →
    SearchResult process fuel start
  exhaustedStrict :
    StrictChain process (suc fuel) start →
    SearchResult process fuel start

searchStable :
  (process : RankedRefinementProcess) →
  (fuel : Nat) →
  (start : Code process) →
  SearchResult process fuel start
searchStable process fuel start with stable? process start
... | yes stable = foundStable zero z≤n stable
... | no unstable with fuel
...   | zero =
  exhaustedStrict
    (chainStep (unstableRaisesRank process start unstable) chainZero)
...   | suc remaining with searchStable process remaining (advance process start)
...     | foundStable depth depth≤remaining stableLater =
  foundStable (suc depth) (s≤s depth≤remaining) stableLater
...     | exhaustedStrict tail =
  exhaustedStrict
    (chainStep (unstableRaisesRank process start unstable) tail)

sucNotLeSelf : (n : Nat) → suc n ≤ n → ⊥
sucNotLeSelf zero ()
sucNotLeSelf (suc n) (s≤s impossible) = sucNotLeSelf n impossible

record StabilizationWitness
    (process : RankedRefinementProcess)
    (start : Code process) : Set where
  constructor stabilizationWitness
  field
    depth : Nat
    depthBound : depth ≤ rankBound process
    stable :
      iterate process depth start
      ≡ advance process (iterate process depth start)

open StabilizationWitness public

rankedRefinementStabilizes :
  (process : RankedRefinementProcess) →
  (start : Code process) →
  StabilizationWitness process start
rankedRefinementStabilizes process start
  with searchStable process (rankBound process) start
... | foundStable depth depth≤bound stable =
  stabilizationWitness depth depth≤bound stable
... | exhaustedStrict chain =
  ⊥-elim contradiction
  where
    growth :
      rank process start + suc (rankBound process)
      ≤ rank process
          (iterate process (suc (rankBound process)) start)
    growth = strictChainRankGrowth process chain

    lower :
      suc (rankBound process)
      ≤ rank process start + suc (rankBound process)
    lower = m≤n+m (suc (rankBound process)) (rank process start)

    upper :
      rank process
        (iterate process (suc (rankBound process)) start)
      ≤ rankBound process
    upper = rankBounded process _

    impossible : suc (rankBound process) ≤ rankBound process
    impossible = ≤-trans lower (≤-trans growth upper)

    contradiction : ⊥
    contradiction = sucNotLeSelf (rankBound process) impossible

------------------------------------------------------------------------
-- For a finite state partition with at most |X| blocks, instantiate rankBound
-- by |X|.  If the initial observation partition is nonempty, the sharper
-- |X|-1 strict-split bound follows after accounting for its initial rank.
------------------------------------------------------------------------
