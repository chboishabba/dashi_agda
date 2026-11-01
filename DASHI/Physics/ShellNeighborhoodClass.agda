module DASHI.Physics.ShellNeighborhoodClass where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (_*_; _∸_)

data ShellNeighborhoodClass : Set where
  definiteShellNeighborhood : ShellNeighborhoodClass
  oneMinusShellNeighborhood : ShellNeighborhoodClass
  mixed21ShellNeighborhood : ShellNeighborhoodClass
  split22ShellNeighborhood : ShellNeighborhoodClass
  unknownShellNeighborhood : ShellNeighborhoodClass

natEq : Nat → Nat → Bool
natEq zero zero = true
natEq zero (suc n) = false
natEq (suc m) zero = false
natEq (suc m) (suc n) = natEq m n

natEq-self : ∀ n → natEq n n ≡ true
natEq-self zero = refl
natEq-self (suc n) = natEq-self n

isEven : Nat → Bool
isEven zero = true
isEven (suc zero) = false
isEven (suc (suc n)) = isEven n

listNatEq : List Nat → List Nat → Bool
listNatEq [] [] = true
listNatEq [] (_ ∷ _) = false
listNatEq (_ ∷ _) [] = false
listNatEq (x ∷ xs) (y ∷ ys) with natEq x y
... | true = listNatEq xs ys
... | false = false

isOneMinusTriple : Nat → Nat → Nat → Bool
isOneMinusTriple a b c with natEq c 2
... | false = false
... | true with natEq a (b * (b ∸ 2))
... | false = false
... | true = true

classifyTripleChecks : Bool → Bool → ShellNeighborhoodClass
classifyTripleChecks false _ = unknownShellNeighborhood
classifyTripleChecks true false = unknownShellNeighborhood
classifyTripleChecks true true = oneMinusShellNeighborhood

classifyTriple : Nat → Nat → Nat → ShellNeighborhoodClass
classifyTriple a b c =
  classifyTripleChecks (natEq c 2) (natEq a (b * (b ∸ 2)))

classifyTripleChecks-tt :
  classifyTripleChecks true true ≡ oneMinusShellNeighborhood
classifyTripleChecks-tt = refl

classifyTriple-oneMinus :
  ∀ b →
  classifyTriple (b * (b ∸ 2)) b 2 ≡ oneMinusShellNeighborhood
classifyTriple-oneMinus b
  rewrite natEq-self 2
        | natEq-self (b * (b ∸ 2)) = classifyTripleChecks-tt

classifyShell1Neighborhood : List Nat → ShellNeighborhoodClass
classifyShell1Neighborhood [] = unknownShellNeighborhood
classifyShell1Neighborhood (8 ∷ []) = definiteShellNeighborhood
classifyShell1Neighborhood (_ ∷ []) = unknownShellNeighborhood
classifyShell1Neighborhood (2 ∷ 2 ∷ []) = oneMinusShellNeighborhood
classifyShell1Neighborhood (_ ∷ _ ∷ []) = unknownShellNeighborhood
classifyShell1Neighborhood (a ∷ b ∷ c ∷ []) = classifyTriple a b c
classifyShell1Neighborhood (16 ∷ 16 ∷ 4 ∷ 4 ∷ []) = split22ShellNeighborhood
classifyShell1Neighborhood (_ ∷ _ ∷ _ ∷ _ ∷ _) = unknownShellNeighborhood
