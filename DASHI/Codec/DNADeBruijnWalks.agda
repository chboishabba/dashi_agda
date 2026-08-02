module DASHI.Codec.DNADeBruijnWalks where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import DASHI.Codec.DNAFirstFormalism using
  ( Base; Trace; emptyTrace; emitTrace; Generable )
open import DASHI.Codec.DNAProductionConstraints using
  ( ProductionState; initialState; productionMachine; step )
open import DASHI.Codec.DNAProductionChoices using
  ( Completion; horizon0; extend )
open import DASHI.Codec.DNAProductionDeBruijn using
  ( Edge; canonicalEdge; LabelledWalk; done; _∷ʷ_ )

------------------------------------------------------------------------
-- Constraint-machine traces and labelled graph walks are two presentations of
-- the same sequential object. The graph presentation additionally exposes the
-- terminal state.

traceToWalk :
  ∀ {s word} →
  Trace productionMachine s word →
  Σ ProductionState (λ t → LabelledWalk s word t)
traceToWalk emptyTrace = _ , done
traceToWalk (emitTrace legal rest) with traceToWalk rest
... | t , walk = t , (canonicalEdge legal ∷ʷ walk)

walkToTrace :
  ∀ {s word t} →
  LabelledWalk s word t →
  Trace productionMachine s word
walkToTrace done = emptyTrace
walkToTrace (e ∷ʷ rest) = emitTrace (Edge.legal e) (walkToTrace rest)

GenerableWalk : List Base → Set
GenerableWalk word = Σ ProductionState (λ t → LabelledWalk initialState word t)

generableToWalk :
  ∀ {word} → Generable productionMachine word → GenerableWalk word
generableToWalk = traceToWalk

walkToGenerable :
  ∀ {word} → GenerableWalk word → Generable productionMachine word
walkToGenerable (t , walk) = walkToTrace walk

record GenerableWalkEquivalence (word : List Base) : Set where
  constructor generableWalkEquivalence
  field
    forward : Generable productionMachine word → GenerableWalk word
    backward : GenerableWalk word → Generable productionMachine word

generable-walk-equivalence :
  ∀ word → GenerableWalkEquivalence word
generable-walk-equivalence word =
  generableWalkEquivalence generableToWalk walkToGenerable

------------------------------------------------------------------------
-- Horizon completion is likewise an endpoint-hidden labelled walk. The Nat
-- index and word shape remain synchronized by the constructors.

completionToWalk :
  ∀ {h s word} →
  Completion h s word →
  Σ ProductionState (λ t → LabelledWalk s word t)
completionToWalk horizon0 = _ , done
completionToWalk (extend legal rest) with completionToWalk rest
... | t , walk = t , (canonicalEdge legal ∷ʷ walk)

walkToCompletion :
  ∀ {s word t} →
  LabelledWalk s word t →
  Σ Nat (λ h → Completion h s word)
walkToCompletion done = zero , horizon0
walkToCompletion (e ∷ʷ rest) with walkToCompletion rest
... | h , completion = suc h , extend (Edge.legal e) completion

------------------------------------------------------------------------
-- Concatenation is the graph-level composition law used by serialized blocks.

append : ∀ {X : Set} → List X → List X → List X
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

appendWalk :
  ∀ {s xs u ys t} →
  LabelledWalk s xs u →
  LabelledWalk u ys t →
  LabelledWalk s (append xs ys) t
appendWalk done right = right
appendWalk (e ∷ʷ left) right = e ∷ʷ appendWalk left right
