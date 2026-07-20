module DASHI.Foundations.TernaryBlockRenormalisation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Algebra.Trit as T
import DASHI.Algebra.TernaryComposition as C

------------------------------------------------------------------------
-- A concrete 3 -> 1 block.
--
-- We use left-associated saturating cancellation.  This is a chosen local
-- coarse rule, not a claim that every DASHI scale map must use this rule.
-- Its non-associativity is therefore part of the specification rather than
-- silently identified with exact integer addition.

record Trit3 : Set where
  constructor tri
  field
    first : T.Trit
    second : T.Trit
    third : T.Trit

open Trit3 public

mirror3 : Trit3 → Trit3
mirror3 (tri a b c) = tri (T.inv a) (T.inv b) (T.inv c)

mirror3-involutive : ∀ x → mirror3 (mirror3 x) ≡ x
mirror3-involutive (tri T.neg T.neg T.neg) = refl
mirror3-involutive (tri T.neg T.neg T.zer) = refl
mirror3-involutive (tri T.neg T.neg T.pos) = refl
mirror3-involutive (tri T.neg T.zer T.neg) = refl
mirror3-involutive (tri T.neg T.zer T.zer) = refl
mirror3-involutive (tri T.neg T.zer T.pos) = refl
mirror3-involutive (tri T.neg T.pos T.neg) = refl
mirror3-involutive (tri T.neg T.pos T.zer) = refl
mirror3-involutive (tri T.neg T.pos T.pos) = refl
mirror3-involutive (tri T.zer T.neg T.neg) = refl
mirror3-involutive (tri T.zer T.neg T.zer) = refl
mirror3-involutive (tri T.zer T.neg T.pos) = refl
mirror3-involutive (tri T.zer T.zer T.neg) = refl
mirror3-involutive (tri T.zer T.zer T.zer) = refl
mirror3-involutive (tri T.zer T.zer T.pos) = refl
mirror3-involutive (tri T.zer T.pos T.neg) = refl
mirror3-involutive (tri T.zer T.pos T.zer) = refl
mirror3-involutive (tri T.zer T.pos T.pos) = refl
mirror3-involutive (tri T.pos T.neg T.neg) = refl
mirror3-involutive (tri T.pos T.neg T.zer) = refl
mirror3-involutive (tri T.pos T.neg T.pos) = refl
mirror3-involutive (tri T.pos T.zer T.neg) = refl
mirror3-involutive (tri T.pos T.zer T.zer) = refl
mirror3-involutive (tri T.pos T.zer T.pos) = refl
mirror3-involutive (tri T.pos T.pos T.neg) = refl
mirror3-involutive (tri T.pos T.pos T.zer) = refl
mirror3-involutive (tri T.pos T.pos T.pos) = refl

coarse3 : Trit3 → T.Trit
coarse3 (tri a b c) = (a C.⊕ b) C.⊕ c

coarse3-equivariant : ∀ x →
  coarse3 (mirror3 x) ≡ T.inv (coarse3 x)
coarse3-equivariant (tri T.neg T.neg T.neg) = refl
coarse3-equivariant (tri T.neg T.neg T.zer) = refl
coarse3-equivariant (tri T.neg T.neg T.pos) = refl
coarse3-equivariant (tri T.neg T.zer T.neg) = refl
coarse3-equivariant (tri T.neg T.zer T.zer) = refl
coarse3-equivariant (tri T.neg T.zer T.pos) = refl
coarse3-equivariant (tri T.neg T.pos T.neg) = refl
coarse3-equivariant (tri T.neg T.pos T.zer) = refl
coarse3-equivariant (tri T.neg T.pos T.pos) = refl
coarse3-equivariant (tri T.zer T.neg T.neg) = refl
coarse3-equivariant (tri T.zer T.neg T.zer) = refl
coarse3-equivariant (tri T.zer T.neg T.pos) = refl
coarse3-equivariant (tri T.zer T.zer T.neg) = refl
coarse3-equivariant (tri T.zer T.zer T.zer) = refl
coarse3-equivariant (tri T.zer T.zer T.pos) = refl
coarse3-equivariant (tri T.zer T.pos T.neg) = refl
coarse3-equivariant (tri T.zer T.pos T.zer) = refl
coarse3-equivariant (tri T.zer T.pos T.pos) = refl
coarse3-equivariant (tri T.pos T.neg T.neg) = refl
coarse3-equivariant (tri T.pos T.neg T.zer) = refl
coarse3-equivariant (tri T.pos T.neg T.pos) = refl
coarse3-equivariant (tri T.pos T.zer T.neg) = refl
coarse3-equivariant (tri T.pos T.zer T.zer) = refl
coarse3-equivariant (tri T.pos T.zer T.pos) = refl
coarse3-equivariant (tri T.pos T.pos T.neg) = refl
coarse3-equivariant (tri T.pos T.pos T.zer) = refl
coarse3-equivariant (tri T.pos T.pos T.pos) = refl

------------------------------------------------------------------------
-- A deterministic refinement section and explicit information loss.

refineDiagonal : T.Trit → Trit3
refineDiagonal T.neg = tri T.neg T.zer T.zer
refineDiagonal T.zer = tri T.zer T.zer T.zer
refineDiagonal T.pos = tri T.pos T.zer T.zer

coarse-refineDiagonal : ∀ t → coarse3 (refineDiagonal t) ≡ t
coarse-refineDiagonal T.neg = refl
coarse-refineDiagonal T.zer = refl
coarse-refineDiagonal T.pos = refl

-- Distinct microstates can have the same macrostate.  Recognisability here is
-- therefore a chosen section, not inversion of the whole fibre.
zeroFibreWitness₁ : coarse3 (tri T.neg T.pos T.zer) ≡ T.zer
zeroFibreWitness₁ = refl

zeroFibreWitness₂ : coarse3 (tri T.zer T.zer T.zer) ≡ T.zer
zeroFibreWitness₂ = refl

positiveFibreWitness₁ : coarse3 (tri T.pos T.zer T.zer) ≡ T.pos
positiveFibreWitness₁ = refl

positiveFibreWitness₂ : coarse3 (tri T.pos T.pos T.neg) ≡ T.zer
positiveFibreWitness₂ = refl

record TernaryBlockReceipt : Set where
  constructor receipt
  field
    mirrorLaw : ∀ x → coarse3 (mirror3 x) ≡ T.inv (coarse3 x)
    sectionLaw : ∀ t → coarse3 (refineDiagonal t) ≡ t
    coarseMapIsManyToOne :
      coarse3 (tri T.neg T.pos T.zer) ≡
      coarse3 (tri T.zer T.zer T.zer)

ternaryBlockReceipt : TernaryBlockReceipt
ternaryBlockReceipt = receipt coarse3-equivariant coarse-refineDiagonal refl
