module DASHI.Physics.Moonshine.FiniteShellAction where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.List.Base using (List; []; _∷_)

record FiniteShellAction (A G : Set) : Set₁ where
  field
    shell1States : List A
    shell2States : List A
    groupElements : List G
    act : G → A → A
    decEqA : (x y : A) → Dec (x ≡ y)

countFixedOn :
  ∀ {A G : Set} →
  FiniteShellAction A G →
  G →
  List A →
  Nat
countFixedOn shellAction g [] = zero
countFixedOn shellAction g (x ∷ xs)
  with FiniteShellAction.decEqA shellAction
         (FiniteShellAction.act shellAction g x) x
... | yes _ = suc (countFixedOn shellAction g xs)
... | no _ = countFixedOn shellAction g xs
