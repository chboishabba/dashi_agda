module DASHI.Physics.ClosureGlue where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

open import Ultrametric as UMetric
open import Contraction as Contraction
open import DASHI.Geometry.Isotropy as Iso
open import DASHI.Geometry.FiniteSpeed as FS
open import DASHI.Combinatorics.Entropy using (Involution)

------------------------------------------------------------------------
-- 0) One record to carry the whole “physics closure” interface
------------------------------------------------------------------------

record ClosureAxioms : Set₁ where
  field
    S   : Set
    U   : UMetric.Ultrametric S
    T   : S → S
    sc  : Contraction.StrictContraction U T
    inv : Involution S
    iso : Iso.Isotropy U T
    fs  : FS.FiniteSpeed T

open ClosureAxioms public

------------------------------------------------------------------------
-- 1) Useful derived facts (no postulates; all come from record fields)
------------------------------------------------------------------------

fp : ∀ (A : ClosureAxioms) → S A
fp A = Contraction.StrictContraction.fp (sc A)

T-fixes-fp : ∀ (A : ClosureAxioms) → T A (fp A) ≡ fp A
T-fixes-fp A = Contraction.StrictContraction.fixed (sc A)

fixed→fp :
  ∀ (A : ClosureAxioms) → (x : S A) → T A x ≡ x → x ≡ fp A
fixed→fp A x hx = Contraction.StrictContraction.unique (sc A) x hx

contractive≢ : ∀ (A : ClosureAxioms) → Contraction.Contractive≢ (U A) (T A)
contractive≢ A = Contraction.StrictContraction.contractive≢ (sc A)

iso-commutes :
  ∀ (A : ClosureAxioms)
  → (g : Iso.Isotropy.G (iso A))
  → (x : S A)
  → T A (Iso.Isotropy.act (iso A) g x)
    ≡ Iso.Isotropy.act (iso A) g (T A x)
iso-commutes A g x = Iso.Isotropy.commutesWithT (iso A) g x

preserves-locality :
  ∀ (A : ClosureAxioms) → (x y : S A)
  → FS.FiniteSpeed.local (fs A) x y
  → FS.FiniteSpeed.local (fs A) (T A x) (T A y)
preserves-locality A x y h =
  FS.FiniteSpeed.preservesLocality (fs A) x y h

------------------------------------------------------------------------
-- 2) “Compile-today” defaults: trivial isotropy + trivial finite speed
------------------------------------------------------------------------

defaultIso : ∀ {S : Set} (U : UMetric.Ultrametric S) (T : S → S) → Iso.Isotropy U T
defaultIso U T = Iso.trivialIsotropy U T

defaultFS : ∀ {S : Set} (T : S → S) → FS.FiniteSpeed T
defaultFS T = FS.trivialFiniteSpeed T

mkDefaultClosure :
  ∀ {S : Set}
  → (U : UMetric.Ultrametric S)
  → (T : S → S)
  → (sc : Contraction.StrictContraction U T)
  → (inv : Involution S)
  → ClosureAxioms
mkDefaultClosure {S} U T sc inv =
  record
    { S   = S
    ; U   = U
    ; T   = T
    ; sc  = sc
    ; inv = inv
    ; iso = defaultIso U T
    ; fs  = defaultFS T
    }
