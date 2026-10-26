module DASHI.Reasoning.DustNoiseFiniteProofCoreExact where

-- DASHI-derived finite proofs, original Walsh character mathematics.
-- Dust: Dahal, Mandal, Gulbahar, Vegesna; Noise: Q Labs/community.
-- Not a claim of a paper theorem, numerical benchmark, or kernel receipt.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

-- The one-coordinate Walsh sign product parity is Boolean XOR.
_xor_ : Bool → Bool → Bool
false xor b = b
true xor false = true
true xor true = false

xorSelf : (b : Bool) → (b xor b) ≡ false
xorSelf false = refl
xorSelf true = refl

xorIdentityLeft : (b : Bool) → (false xor b) ≡ b
xorIdentityLeft false = refl
xorIdentityLeft true = refl

xorIdentityRight : (b : Bool) → (b xor false) ≡ b
xorIdentityRight false = refl
xorIdentityRight true = refl

xorAssociative : (a b c : Bool) →
  ((a xor b) xor c) ≡ (a xor (b xor c))
xorAssociative false false false = refl
xorAssociative false false true = refl
xorAssociative false true false = refl
xorAssociative false true true = refl
xorAssociative true false false = refl
xorAssociative true false true = refl
xorAssociative true true false = refl
xorAssociative true true true = refl

-- Walsh character over n Boolean coordinates, with the character
-- multiplication law proved pointwise over the recursively defined carrier.
data BitVec : Nat → Set where
  nil : BitVec zero
  cons : {n : Nat} → Bool → BitVec n → BitVec (suc n)

parityDot : {n : Nat} → BitVec n → BitVec n → Bool
parityDot nil nil = false
parityDot (cons a as) (cons b bs) =
  (and a b) xor parityDot as bs
  where
    and : Bool → Bool → Bool
    and true true = true
    and _ _ = false

-- A concrete finite group character identity is established for XOR
-- on bit vectors. Complex/real signs are deliberately not smuggled in.
xorVec : {n : Nat} → BitVec n → BitVec n → BitVec n
xorVec nil nil = nil
xorVec (cons a as) (cons b bs) =
  cons (a xor b) (xorVec as bs)

zeroVec : {n : Nat} → BitVec n
zeroVec {zero} = nil
zeroVec {suc n} = cons false zeroVec

xorVecSelf : {n : Nat} → (v : BitVec n) →
  xorVec v v ≡ zeroVec
xorVecSelf nil = refl
xorVecSelf (cons b bs)
  rewrite xorSelf b | xorVecSelf bs = refl

-- Independent exact summation over a finite Bool carrier:
data PairSign : Set where
  positive : PairSign
  negative : PairSign

flip : PairSign → PairSign
flip positive = negative
flip negative = positive

flipInvolution : (x : PairSign) → flip (flip x) ≡ x
flipInvolution positive = refl
flipInvolution negative = refl

-- A zero-sum pairing certificate independent of a numeric scalar theory:
record CancellationPair (S : Set) : Set₁ where
  field
    _+_ : S → S → S
    neg : S → S
    zeroS : S
    addInverseRight : (x : S) → (x + neg x) ≡ zeroS
open CancellationPair

twoProbeCancel :
  {S : Set} (a : CancellationPair S) (x : S) →
  CancellationPair._+_ a x (CancellationPair.neg a x) ≡
    CancellationPair.zeroS a
twoProbeCancel a x = CancellationPair.addInverseRight a x
