module DASHI.Physics.Closure.NSPeriodicConcreteNearTriadDecomposition where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

------------------------------------------------------------------------
-- Exact finite decomposition of a literal near-triad list into LH, HL and HH.
--
-- The three component lists are the actual enumerated lists supplied by the
-- concrete Fourier carrier.  Their concatenation is definitionally the complete
-- near list; the theorem below proves the corresponding fold identity.
------------------------------------------------------------------------

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

record AdditiveFoldLaws (Scalar : Set) : Set₁ where
  field
    zero : Scalar
    add : Scalar → Scalar → Scalar
    leftIdentity : ∀ x → add zero x ≡ x
    associative : ∀ x y z →
      add (add x y) z ≡ add x (add y z)

open AdditiveFoldLaws public

fold : ∀ {Scalar} → AdditiveFoldLaws Scalar → List Scalar → Scalar
fold L [] = zero L
fold L (x ∷ xs) = add L x (fold L xs)

foldAppend :
  ∀ {Scalar} (L : AdditiveFoldLaws Scalar) (xs ys : List Scalar) →
  fold L (xs ++ ys) ≡ add L (fold L xs) (fold L ys)
foldAppend L [] ys = sym (leftIdentity L (fold L ys))
foldAppend L (x ∷ xs) ys =
  trans
    (cong (add L x) (foldAppend L xs ys))
    (sym (associative L x (fold L xs) (fold L ys)))

record NearTriadPartition
    (Scalar : Set)
    (L : AdditiveFoldLaws Scalar) : Set₁ where
  field
    lowHighTerms highLowTerms highHighTerms : List Scalar

open NearTriadPartition public

literalNearTriadTerms :
  ∀ {Scalar} {L : AdditiveFoldLaws Scalar} →
  NearTriadPartition Scalar L → List Scalar
literalNearTriadTerms P =
  lowHighTerms P ++ (highLowTerms P ++ highHighTerms P)

literalNearTriadMagnitude :
  ∀ {Scalar} {L : AdditiveFoldLaws Scalar} →
  NearTriadPartition Scalar L → Scalar
literalNearTriadMagnitude {L = L} P = fold L (literalNearTriadTerms P)

lowHighMagnitude highLowMagnitude highHighMagnitude :
  ∀ {Scalar} {L : AdditiveFoldLaws Scalar} →
  NearTriadPartition Scalar L → Scalar
lowHighMagnitude {L = L} P = fold L (lowHighTerms P)
highLowMagnitude {L = L} P = fold L (highLowTerms P)
highHighMagnitude {L = L} P = fold L (highHighTerms P)

nearTriadLiteralIdentity :
  ∀ {Scalar} {L : AdditiveFoldLaws Scalar} →
  (P : NearTriadPartition Scalar L) →
  literalNearTriadMagnitude P ≡
  add L
    (lowHighMagnitude P)
    (add L (highLowMagnitude P) (highHighMagnitude P))
nearTriadLiteralIdentity {L = L} P =
  trans
    (foldAppend L
      (lowHighTerms P)
      (highLowTerms P ++ highHighTerms P))
    (cong
      (add L (fold L (lowHighTerms P)))
      (foldAppend L (highLowTerms P) (highHighTerms P)))
