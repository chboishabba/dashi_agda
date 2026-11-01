module DASHI.HME.Path where

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (_≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import MDL.Core using (CodeLength)

open import DASHI.Geometry.TimeOrientation using (TimeOrientation)
open import DASHI.Geometry.ConeArrowIsotropyOrbitProfile using (AbstractOrbitProfile)
open import DASHI.Physics.ClosureGlue using (ClosureAxioms)
open ClosureAxioms public

------------------------------------------------------------------------
-- Path traces: the proof object is a concrete step-following trace.
------------------------------------------------------------------------

data Follows {S : Set} (step : S → S) : S → List S → Set where
  []  : ∀ {s} → Follows step s []
  _∷_ :
    ∀ {s next rest} →
    step s ≡ next →
    Follows step next rest →
    Follows step s (next ∷ rest)

lastStateFrom : ∀ {S : Set} → S → List S → S
lastStateFrom s [] = s
lastStateFrom _ (next ∷ rest) = lastStateFrom next rest

record Path {S : Set} (step : S → S) : Set₁ where
  field
    start : S
    rest : List S
    follows : Follows step start rest

open Path public

states : ∀ {S : Set} {step : S → S} → Path step → List S
states path = start path ∷ rest path

end : ∀ {S : Set} {step : S → S} → Path step → S
end path = lastStateFrom (start path) (rest path)

idPath : ∀ {S : Set} {step : S → S} → S → Path step
idPath s =
  record
    { start = s
    ; rest = []
    ; follows = []
    }

record Composable {S : Set} {step : S → S}
                  (p q : Path step) : Set where
  field
    glue : end p ≡ start q

open Composable public

follows-append :
  ∀ {S : Set} {step : S → S} {s : S} {xs ys : List S} →
  Follows step s xs →
  Follows step (lastStateFrom s xs) ys →
  Follows step s (xs ++ ys)
follows-append [] qf = qf
follows-append (eq ∷ pf) qf = eq ∷ follows-append pf qf

all-append :
  ∀ {A : Set} {P : A → Set} {xs ys : List A} →
  All P xs → All P ys → All P (xs ++ ys)
all-append [] ys = ys
all-append (p ∷ pxs) pys = p ∷ all-append pxs pys

tailAll :
  ∀ {A : Set} {P : A → Set} {x : A} {xs : List A} →
  All P (x ∷ xs) → All P xs
tailAll (_ ∷ ps) = ps

_⨟_ :
  ∀ {S : Set} {step : S → S} →
  (p q : Path step) →
  Composable p q →
  Path step
_⨟_ {step = step} p q comp =
  record
    { start = start p
    ; rest = rest p ++ rest q
    ; follows =
        follows-append
          (follows p)
          (subst (λ s → Follows step s (rest q))
                 (sym (glue comp))
                 (follows q))
    }

------------------------------------------------------------------------
-- Downstream canonical context: HME consumes closure + orientation.
------------------------------------------------------------------------

record CanonicalContext (A : ClosureAxioms) : Set₁ where
  field
    orientation : TimeOrientation (T A)
    cone : S A → Set

open CanonicalContext public

record Admissible (A : ClosureAxioms) (ctx : CanonicalContext A) : Set₁ where
  field
    path : Path (T A)
    cone-ok : All (cone ctx) (states path)
    mdl-ok :
      All
        (λ s → TimeOrientation.Lyap (orientation ctx) (T A s)
             ≤ TimeOrientation.Lyap (orientation ctx) s)
        (states path)

open Admissible public

record PathWitness (A : ClosureAxioms) : Set₁ where
  field
    path : Path (T A)
    profile : AbstractOrbitProfile

record Proof (A : ClosureAxioms) (ctx : CanonicalContext A) : Set₁ where
  field
    admissible : Admissible A ctx
    witness : AbstractOrbitProfile

open Proof public

------------------------------------------------------------------------
-- Admissibility is closed under path composition.
------------------------------------------------------------------------

compose-admissible :
  ∀ {A : ClosureAxioms} {ctx : CanonicalContext A}
    (ap : Admissible A ctx)
    (aq : Admissible A ctx)
    (c : Composable (Admissible.path ap) (Admissible.path aq))
    → Admissible A ctx
compose-admissible {A = A} {ctx = ctx} ap aq c =
  record
    { path = _⨟_
        {step = T A}
        (Admissible.path ap)
        (Admissible.path aq)
        c
    ; cone-ok =
        all-append
          (Admissible.cone-ok ap)
          (tailAll (Admissible.cone-ok aq))
    ; mdl-ok =
        all-append
          (Admissible.mdl-ok ap)
          (tailAll (Admissible.mdl-ok aq))
    }
