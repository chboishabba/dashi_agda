module DASHI.Execution.DeltaConeMDLContract where

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_)

-- A runtime delta is kept relational: source and target are both retained.
-- This avoids pretending that an arbitrary state carrier has subtraction.
Delta : Set → Set
Delta X = X × X

record ExecutionGeometry (X : Set) : Set₁ where
  field
    step  : X → X
    arrow : X → Nat
    mdl   : X → Nat
    cone  : Delta X → Set
    basin : X → Set

open ExecutionGeometry public

record AdmissibleStep {X : Set} (G : ExecutionGeometry X) (x : X) : Set where
  field
    arrow-monotone : arrow G x ≤ arrow G (step G x)
    delta-in-cone  : cone G (x , step G x)
    mdl-descent    : mdl G (step G x) ≤ mdl G x
    basin-preserved : basin G x → basin G (step G x)

open AdmissibleStep public

record ExecutionAdmissible {X : Set} (G : ExecutionGeometry X) : Set where
  field
    admissible : ∀ x → AdmissibleStep G x

open ExecutionAdmissible public

-- The contract exposes its useful consequences without strengthening them.
execution-preserves-basin :
  ∀ {X} {G : ExecutionGeometry X} →
  ExecutionAdmissible G →
  ∀ x → basin G x → basin G (step G x)
execution-preserves-basin C x bx =
  basin-preserved (admissible C x) bx

execution-descends-mdl :
  ∀ {X} {G : ExecutionGeometry X} →
  ExecutionAdmissible G →
  ∀ x → mdl G (step G x) ≤ mdl G x
execution-descends-mdl C x = mdl-descent (admissible C x)

execution-delta-in-cone :
  ∀ {X} {G : ExecutionGeometry X} →
  ExecutionAdmissible G →
  ∀ x → cone G (x , step G x)
execution-delta-in-cone C x = delta-in-cone (admissible C x)
