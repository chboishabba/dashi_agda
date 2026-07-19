module DASHI.HME.CanonicalPath where

open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Narrow downstream HME seam.
--
-- The canonical closure carrier, step relation, admissibility law, and
-- closure-relevant output are supplied by the already-fixed closure spine.
-- This module does not reconstruct projection defect, quadraticity,
-- signature lock, Clifford structure, or the strong contraction bridge.
------------------------------------------------------------------------

data Path {State : Set}
          (Step : State → State → Set) :
          State → State → Set where
  idPath :
    {x : State} →
    Path Step x x

  _▷_ :
    {x y z : State} →
    Step x y →
    Path Step y z →
    Path Step x z

infixr 6 _▷_
infixr 5 _⨟_

_⨟_ :
  {State : Set} →
  {Step : State → State → Set} →
  {x y z : State} →
  Path Step x y →
  Path Step y z →
  Path Step x z
idPath ⨟ q = q
(step ▷ p) ⨟ q = step ▷ (p ⨟ q)

path-left-identity :
  {State : Set} →
  {Step : State → State → Set} →
  {x y : State} →
  (p : Path Step x y) →
  idPath ⨟ p ≡ p
path-left-identity p = refl

path-right-identity :
  {State : Set} →
  {Step : State → State → Set} →
  {x y : State} →
  (p : Path Step x y) →
  p ⨟ idPath ≡ p
path-right-identity idPath = refl
path-right-identity (step ▷ p) =
  cong (step ▷_) (path-right-identity p)

path-associative :
  {State : Set} →
  {Step : State → State → Set} →
  {w x y z : State} →
  (p : Path Step w x) →
  (q : Path Step x y) →
  (r : Path Step y z) →
  (p ⨟ q) ⨟ r ≡ p ⨟ (q ⨟ r)
path-associative idPath q r = refl
path-associative (step ▷ p) q r =
  cong (step ▷_) (path-associative p q r)

------------------------------------------------------------------------
-- Path-local admissibility.
------------------------------------------------------------------------

record Admissibility
       {State : Set}
       (Step : State → State → Set) : Set₁ where
  field
    admissibleStep :
      {x y : State} →
      Step x y →
      Set

open Admissibility public

data AdmissiblePath
     {State : Set}
     {Step : State → State → Set}
     (admissibility : Admissibility Step) :
     {x y : State} →
     Path Step x y →
     Set where
  admissible-id :
    {x : State} →
    AdmissiblePath admissibility (idPath {x = x})

  admissible-step :
    {x y z : State} →
    {step : Step x y} →
    {path : Path Step y z} →
    admissibleStep admissibility step →
    AdmissiblePath admissibility path →
    AdmissiblePath admissibility (step ▷ path)

compose-admissible :
  {State : Set} →
  {Step : State → State → Set} →
  {admissibility : Admissibility Step} →
  {x y z : State} →
  {p : Path Step x y} →
  {q : Path Step y z} →
  AdmissiblePath admissibility p →
  AdmissiblePath admissibility q →
  AdmissiblePath admissibility (p ⨟ q)
compose-admissible admissible-id q-ok = q-ok
compose-admissible
  (admissible-step step-ok p-ok)
  q-ok =
  admissible-step step-ok (compose-admissible p-ok q-ok)

------------------------------------------------------------------------
-- The existing closure spine supplies this surface.
------------------------------------------------------------------------

record CanonicalClosureSurface : Set₁ where
  field
    State : Set
    Step : State → State → Set
    admissibility : Admissibility Step
    ClosureOutput : State → Set

open CanonicalClosureSurface public

data PathStatus
     (surface : CanonicalClosureSurface)
     {x y : State surface}
     (path : Path (Step surface) x y) : Set₁ where
  candidate :
    PathStatus surface path

  admitted :
    AdmissiblePath (admissibility surface) path →
    ClosureOutput surface y →
    PathStatus surface path

  blocked :
    Set →
    PathStatus surface path

record PathProof
       (surface : CanonicalClosureSurface)
       (x y : State surface) : Set₁ where
  field
    proofPath :
      Path (Step surface) x y

    proofStatus :
      PathStatus surface proofPath

open PathProof public

-- The proof/status object is path-indexed.  There is no detached theorem
-- payload that can be admitted independently of the path that produced it.
