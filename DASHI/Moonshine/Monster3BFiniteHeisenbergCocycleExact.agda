module DASHI.Moonshine.Monster3BFiniteHeisenbergCocycleExact where

------------------------------------------------------------------------
-- EXACT 2-COCYCLE IDENTITY FOR THE FINITE HEISENBERG CENTRAL EXTENSION
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import DASHI.Algebra.Trit using (Trit)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Moonshine.Monster3BFiniteHeisenbergDotBilinearityExact as Dot
import DASHI.Moonshine.Monster3BF3AlgebraExact as F3

infixl 6 _⊕_
_⊕_ : Trit → Trit → Trit
_⊕_ = G._+3_

addSymplectic : H.Symplectic12 → H.Symplectic12 → H.Symplectic12
addSymplectic u v =
  H.symplectic12
    (H.addX6 (H.translationPart u) (H.translationPart v))
    (H.addX6 (H.modulationPart u) (H.modulationPart v))

cocycle : H.Symplectic12 → H.Symplectic12 → Trit
cocycle u v = H.dot6 (H.modulationPart u) (H.translationPart v)

rotate3 : (a b c : Trit) → a ⊕ (b ⊕ c) ≡ c ⊕ (a ⊕ b)
rotate3 a b c =
  trans
    (sym (F3.plusAssoc a b c))
    (F3.plusComm (a ⊕ b) c)

addX6Assoc : (x y z : G.X6) →
  H.addX6 (H.addX6 x y) z ≡ H.addX6 x (H.addX6 y z)
addX6Assoc
  (G.x6 a0 a1 a2 a3 a4 a5)
  (G.x6 b0 b1 b2 b3 b4 b5)
  (G.x6 c0 c1 c2 c3 c4 c5)
  rewrite F3.plusAssoc a0 b0 c0
        | F3.plusAssoc a1 b1 c1
        | F3.plusAssoc a2 b2 c2
        | F3.plusAssoc a3 b3 c3
        | F3.plusAssoc a4 b4 c4
        | F3.plusAssoc a5 b5 c5 = refl

cocycleIdentity : (u v w : H.Symplectic12) →
  cocycle u v ⊕ cocycle (addSymplectic u v) w
  ≡ cocycle v w ⊕ cocycle u (addSymplectic v w)
cocycleIdentity
  (H.symplectic12 x ξ)
  (H.symplectic12 y η)
  (H.symplectic12 z θ)
  rewrite Dot.dotAddLeft ξ η z
        | Dot.dotAddRight ξ y z
  = rotate3 (H.dot6 ξ y) (H.dot6 ξ z) (H.dot6 η z)

record HeisenbergCocycleBoundary : Set where
  constructor heisenbergCocycleBoundary
  field
    quotientAdditionAssociative : Bool
    cocycleRightLinear : Bool
    cocycleLeftLinear : Bool
    cocycleIdentityProved : Bool
open HeisenbergCocycleBoundary public

canonicalHeisenbergCocycleBoundary : HeisenbergCocycleBoundary
canonicalHeisenbergCocycleBoundary =
  heisenbergCocycleBoundary true true true true
