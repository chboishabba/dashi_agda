module DASHI.Foundations.BidirectionalAdmissibilityGalois where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; Σ)

------------------------------------------------------------------------
-- Bidirectional admissibility over a scale relation.
--
-- The forward map is existential: a macrostate is supported when at least
-- one admitted microstate realizes it.
--
-- The reverse map is universal/safe: a microstate survives a macro predicate
-- when every macrostate related to it satisfies that predicate.
--
-- These two maps form a constructive Galois connection.  The file is purely
-- structural: it does not identify string vacua, quantum states, or biological
-- observables with any concrete carrier.

Pred : Set → Set₁
Pred A = A → Set

infix 4 _⊆_

_⊆_ : ∀ {A : Set} → Pred A → Pred A → Set
P ⊆ Q = ∀ {x} → P x → Q x

Rel : Set → Set → Set₁
Rel A B = A → B → Set

Forward :
  ∀ {Micro Macro : Set} →
  Rel Micro Macro →
  Pred Micro →
  Pred Macro
Forward {Micro} R X y = Σ Micro (λ x → X x × R x y)

SafePullback :
  ∀ {Micro Macro : Set} →
  Rel Micro Macro →
  Pred Macro →
  Pred Micro
SafePullback R Y x = ∀ {y} → R x y → Y y

------------------------------------------------------------------------
-- Galois law.

galois-forward-safe :
  ∀ {Micro Macro : Set}
    {R : Rel Micro Macro}
    {X : Pred Micro}
    {Y : Pred Macro} →
  Forward R X ⊆ Y →
  X ⊆ SafePullback R Y
galois-forward-safe forward⊆ {x} x∈X {y} rxy =
  forward⊆ (x , (x∈X , rxy))

galois-safe-forward :
  ∀ {Micro Macro : Set}
    {R : Rel Micro Macro}
    {X : Pred Micro}
    {Y : Pred Macro} →
  X ⊆ SafePullback R Y →
  Forward R X ⊆ Y
galois-safe-forward safe⊇ (x , (x∈X , rxy)) =
  safe⊇ x∈X rxy

record GaloisLaw
    {Micro Macro : Set}
    (R : Rel Micro Macro)
    (X : Pred Micro)
    (Y : Pred Macro) : Set₁ where
  field
    forward-to-safe : Forward R X ⊆ Y → X ⊆ SafePullback R Y
    safe-to-forward : X ⊆ SafePullback R Y → Forward R X ⊆ Y

canonicalGaloisLaw :
  ∀ {Micro Macro : Set}
    (R : Rel Micro Macro)
    (X : Pred Micro)
    (Y : Pred Macro) →
  GaloisLaw R X Y
canonicalGaloisLaw R X Y =
  record
    { forward-to-safe = galois-forward-safe
    ; safe-to-forward = galois-safe-forward
    }

------------------------------------------------------------------------
-- The induced closure/interior pair.

MicroClosure :
  ∀ {Micro Macro : Set} →
  Rel Micro Macro →
  Pred Micro →
  Pred Micro
MicroClosure R X = SafePullback R (Forward R X)

MacroKernel :
  ∀ {Micro Macro : Set} →
  Rel Micro Macro →
  Pred Macro →
  Pred Macro
MacroKernel R Y = Forward R (SafePullback R Y)

microClosure-extensive :
  ∀ {Micro Macro : Set}
    {R : Rel Micro Macro}
    {X : Pred Micro} →
  X ⊆ MicroClosure R X
microClosure-extensive {X = X} {x} x∈X {y} rxy =
  x , (x∈X , rxy)

macroKernel-reductive :
  ∀ {Micro Macro : Set}
    {R : Rel Micro Macro}
    {Y : Pred Macro} →
  MacroKernel R Y ⊆ Y
macroKernel-reductive (x , (safe , rxy)) = safe rxy

forward-monotone :
  ∀ {Micro Macro : Set}
    {R : Rel Micro Macro}
    {X X′ : Pred Micro} →
  X ⊆ X′ →
  Forward R X ⊆ Forward R X′
forward-monotone X⊆X′ (x , (x∈X , rxy)) =
  x , (X⊆X′ x∈X , rxy)

safePullback-monotone :
  ∀ {Micro Macro : Set}
    {R : Rel Micro Macro}
    {Y Y′ : Pred Macro} →
  Y ⊆ Y′ →
  SafePullback R Y ⊆ SafePullback R Y′
safePullback-monotone Y⊆Y′ safe rxy = Y⊆Y′ (safe rxy)

------------------------------------------------------------------------
-- Bidirectional scale compatibility is the micro predicate that satisfies
-- both a micro admissibility predicate and the macro predicate pulled back
-- along the scale relation.

BidirectionallyCompatible :
  ∀ {Micro Macro : Set} →
  Rel Micro Macro →
  Pred Micro →
  Pred Macro →
  Pred Micro
BidirectionallyCompatible R MicroOK MacroOK x =
  MicroOK x × SafePullback R MacroOK x

bidirectional-micro :
  ∀ {Micro Macro : Set}
    {R : Rel Micro Macro}
    {MicroOK : Pred Micro}
    {MacroOK : Pred Macro} →
  BidirectionallyCompatible R MicroOK MacroOK ⊆ MicroOK
bidirectional-micro (microOK , _) = microOK

bidirectional-safe :
  ∀ {Micro Macro : Set}
    {R : Rel Micro Macro}
    {MicroOK : Pred Micro}
    {MacroOK : Pred Macro} →
  BidirectionallyCompatible R MicroOK MacroOK ⊆ SafePullback R MacroOK
bidirectional-safe (_ , safe) = safe
