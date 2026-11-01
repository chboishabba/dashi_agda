module DASHI.Philosophy.ProcessCompositionLaws where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Philosophy.ProcessOntology as Process

------------------------------------------------------------------------
-- Paths retain ordered history.  Composition is list concatenation, so
-- associativity is proved while reversibility/residual properties stay typed.

data ProcessStep : Process.ProcessStage → Process.ProcessStage → Set where
  cutStep : ProcessStep Process.undifferentiatedPossibility Process.determinationCut
  encounterStep : ProcessStep Process.determinationCut Process.relationalEncounter
  worldStep : ProcessStep Process.relationalEncounter Process.provisionalWorld
  markStep : ProcessStep Process.provisionalWorld Process.markedExtension
  relationStep : ProcessStep Process.markedExtension Process.relationalExtension

record StepReceipt {A B : Process.ProcessStage} (step : ProcessStep A B) : Set where
  field
    historyPreserved : Bool
    reversible : Bool
    residualIntroduced : Bool
    receiptVisible : Bool

open StepReceipt public

append : ∀ {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

appendRightIdentity : ∀ {A : Set} (xs : List A) → append xs [] ≡ xs
appendRightIdentity [] = refl
appendRightIdentity (x ∷ xs) = cong (x ∷_) (appendRightIdentity xs)

appendAssociative :
  ∀ {A : Set} (xs ys zs : List A) →
  append (append xs ys) zs ≡ append xs (append ys zs)
appendAssociative [] ys zs = refl
appendAssociative (x ∷ xs) ys zs = cong (x ∷_) (appendAssociative xs ys zs)

record ProcessPath : Set where
  field
    stages : List Process.ProcessStage
    history : List Process.ProcessStage
    equivalentEndpointNotIdenticalHistory : Bool

open ProcessPath public

composePath : ProcessPath → ProcessPath → ProcessPath
composePath first second =
  record
    { stages = append (stages first) (stages second)
    ; history = append (history first) (history second)
    ; equivalentEndpointNotIdenticalHistory = true
    }
