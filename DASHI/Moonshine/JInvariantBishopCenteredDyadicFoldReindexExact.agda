module DASHI.Moonshine.JInvariantBishopCenteredDyadicFoldReindexExact where

-- Source-written. Reuse actual binary words and square-shell finite
-- permutation owner. The canonical interval adds (+n,-(n+1)) together;
-- the zero coordinate is present exactly once, not doubled.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (ℤ; +_; -[1+_])
open import Data.Nat.Base using (_<_; _≤_; s≤s; z≤n)
import Data.Nat.Properties as NP
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻; ∈-++⁻)
import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Unary.AllPairs.Core as AP
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UP
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)
import Real as R
import RealProperties as P
import DASHI.Core.BinaryBranchOutcomeEnumerationExact as B
import DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact as Codec
import DASHI.Mathematics.NumberTheory.FiniteDependentPairEnumerationExact as Dep
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as W
import DASHI.Moonshine.JInvariantBishopCenteredDyadicAddressExact as Addr
import DASHI.Moonshine.JInvariantBishopCenteredDyadicRowExact as Chart
import DASHI.Moonshine.JInvariantBishopSquareShellReindexExact as S
import DASHI.Moonshine.JInvariantBishopSquareExhaustionExact as Ex
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
open R using (ℝ; _≃_; _+_)
open S using (sum; sumPerm; sumMap)

words : ∀ n → List (B.BinaryWord n)
words zero = B.end ∷ []
words (suc n) = map B.bit0 (words n) ++ map B.bit1 (words n)

wordComplete : ∀ {n} (w : B.BinaryWord n) → w ∈ words n
wordComplete B.end = Any.here refl
wordComplete (B.bit0 w) = B.memberAppendLeft (∈-map⁺ B.bit0 (wordComplete w))
wordComplete (B.bit1 w) = B.memberAppendRight (∈-map⁺ B.bit1 (wordComplete w))

bit0Inject : ∀ {n} {a b : B.BinaryWord n} → B.bit0 a ≡ B.bit0 b → a ≡ b
bit0Inject refl = refl
bit1Inject : ∀ {n} {a b : B.BinaryWord n} → B.bit1 a ≡ B.bit1 b → a ≡ b
bit1Inject refl = refl
bitDisjoint : ∀ {n} {a b : B.BinaryWord n} → B.bit0 a ≡ B.bit1 b → ⊥
bitDisjoint ()

wordUnique : ∀ n → Unique (words n)
wordUnique zero = AP._∷_ All.[] AP.[]
wordUnique (suc n) = Dep.uniqueAppendDisjoint
  (UP.map⁺ bit0Inject (wordUnique n)) (UP.map⁺ bit1Inject (wordUnique n)) cross
  where
  cross : ∀ {a b} → a ∈ map B.bit0 (words n) → b ∈ map B.bit1 (words n) → a ≡ b → ⊥
  cross am bm eq with ∈-map⁻ B.bit0 am | ∈-map⁻ B.bit1 bm
  ... | a , _ , ea | b , _ , eb = bitDisjoint (trans (sym ea) (trans eq eb))

index : ∀ {n} → B.BinaryWord (suc n) → ℤ
index w = Addr.integerRead (Addr.center w)

indexInject : ∀ {n} {a b : B.BinaryWord (suc n)} → index a ≡ index b → a ≡ b
indexInject {a = a} {b = b} eq = Addr.centerInjective (Addr.integerInjective (Addr.center a) (Addr.center b) eq)

In : Nat → ℤ → Set
In n (+ k) = k < n
In n (-[1+ k ]) = k < n

interval : Nat → List ℤ
interval zero = []
interval (suc n) = interval n ++ (+ n ∷ -[1+ n ] ∷ [])

inMono : ∀ {m n j} → m ≤ n → In m j → In n j
inMono {j = + k} le h = NP.<-≤-trans h le
inMono {j = -[1+ k ]} le h = NP.<-≤-trans h le

intervalSound : ∀ n {j} → j ∈ interval n → In n j
intervalSound zero ()
intervalSound (suc n) h with ∈-++⁻ (interval n) h
... | inj₁ inside = inMono (NP.n≤1+n n) (intervalSound n inside)
... | inj₂ (Any.here refl) = s≤s NP.≤-refl
... | inj₂ (Any.there (Any.here refl)) = s≤s NP.≤-refl
... | inj₂ (Any.there (Any.there ()))

positiveMember : ∀ n k → k < n → (+ k) ∈ interval n
positiveMember zero k ()
positiveMember (suc n) k (s≤s le) with NP.m≤n⇒m<n∨m≡n le
... | inj₁ lt = B.memberAppendLeft (positiveMember n k lt)
... | inj₂ refl = B.memberAppendRight (Any.here refl)

negativeMember : ∀ n k → k < n → -[1+ k ] ∈ interval n
negativeMember zero k ()
negativeMember (suc n) k (s≤s le) with NP.m≤n⇒m<n∨m≡n le
... | inj₁ lt = B.memberAppendLeft (negativeMember n k lt)
... | inj₂ refl = B.memberAppendRight (Any.there (Any.here refl))

intervalComplete : ∀ n j → In n j → j ∈ interval n
intervalComplete n (+ k) = positiveMember n k
intervalComplete n (-[1+ k ]) = negativeMember n k

intervalUnique : ∀ n → Unique (interval n)
intervalUnique zero = AP.[]
intervalUnique (suc n) = Dep.uniqueAppendDisjoint (intervalUnique n)
  (AP._∷_ (All._∷_ Addr.signDisjoint All.[])
    (AP._∷_ All.[] AP.[])) cross
  where
  cross : ∀ {a b} → a ∈ interval n → b ∈ (+ n ∷ -[1+ n ] ∷ []) → a ≡ b → ⊥
  cross am (Any.here refl) refl = NP.<-irrefl refl (intervalSound n am)
  cross am (Any.there (Any.here refl)) refl = NP.<-irrefl refl (intervalSound n am)
  cross am (Any.there (Any.there ())) eq

rangeIn : ∀ n j → Addr.InRange n j → In (Codec.bitCardinality n) j
rangeIn n (+ k) h = h
rangeIn n (-[1+ k ]) h = h

inRange : ∀ n j → In (Codec.bitCardinality n) j → Addr.InRange n j
inRange n (+ k) h = h
inRange n (-[1+ k ]) h = h

permutation : ∀ n → map index (words (suc n)) Perm.↭ interval (Codec.bitCardinality n)
permutation n = W.uniqueMembershipEquivalenceToPermutation
  (UP.map⁺ indexInject (wordUnique (suc n))) (intervalUnique (Codec.bitCardinality n))
  forward backward
  where
  forward : ∀ {j} → j ∈ map index (words (suc n)) → j ∈ interval (Codec.bitCardinality n)
  forward {j} h with ∈-map⁻ index h
  ... | w , _ , eq = subst (λ i → i ∈ interval (Codec.bitCardinality n)) (sym eq)
    (intervalComplete (Codec.bitCardinality n) (index w)
      (rangeIn n (index w) (Addr.readRange (Addr.center w))))

  backward : ∀ {j} → j ∈ interval (Codec.bitCardinality n) → j ∈ map index (words (suc n))
  backward {j} h =
    let r = Addr.encodeInteger j (inRange n j (intervalSound (Codec.bitCardinality n) h))
        w = Addr.uncenter r
        eq = trans (cong Addr.integerRead (Addr.centerUncenter r))
          (Addr.integerRoundtrip j (inRange n j (intervalSound (Codec.bitCardinality n) h)))
    in subst (λ i → i ∈ map index (words (suc n))) eq (∈-map⁺ index (wordComplete w))

foldReal : ∀ {n} (f : B.BinaryWord n → C.BishopComplex) →
  C.re (Chart.fold f) ≃ sum (λ w → C.re (f w)) (words n)
foldReal {zero} f = P.≃-symm (P.+-identityʳ (C.re (f B.end)))
foldReal {suc n} f =
  P.≃-trans (P.+-cong (foldReal (λ w → f (B.bit0 w))) (foldReal (λ w → f (B.bit1 w))))
    (P.≃-trans
      (P.+-cong (P.≃-symm (sumMap (λ w → C.re (f w)) B.bit0 (words n)))
        (P.≃-symm (sumMap (λ w → C.re (f w)) B.bit1 (words n))))
      (P.≃-symm (Ex.sumAppend (λ w → C.re (f w)) (map B.bit0 (words n)) (map B.bit1 (words n)))))

foldImag : ∀ {n} (f : B.BinaryWord n → C.BishopComplex) →
  C.im (Chart.fold f) ≃ sum (λ w → C.im (f w)) (words n)
foldImag {zero} f = P.≃-symm (P.+-identityʳ (C.im (f B.end)))
foldImag {suc n} f =
  P.≃-trans (P.+-cong (foldImag (λ w → f (B.bit0 w))) (foldImag (λ w → f (B.bit1 w))))
    (P.≃-trans
      (P.+-cong (P.≃-symm (sumMap (λ w → C.im (f w)) B.bit0 (words n)))
        (P.≃-symm (sumMap (λ w → C.im (f w)) B.bit1 (words n))))
      (P.≃-symm (Ex.sumAppend (λ w → C.im (f w)) (map B.bit0 (words n)) (map B.bit1 (words n)))))

intervalFold : ∀ n (f : ℤ → C.BishopComplex) →
  C._≈C_ (Chart.fold (λ w → f (index {n} w)))
    (C.complex (sum (λ j → C.re (f j)) (interval (Codec.bitCardinality n)))
               (sum (λ j → C.im (f j)) (interval (Codec.bitCardinality n))))
intervalFold n f =
  P.≃-trans (foldReal (λ w → f (index w)))
    (P.≃-trans (P.≃-symm (sumMap (λ j → C.re (f j)) index (words (suc n))))
      (sumPerm (λ j → C.re (f j)) (permutation n))) ,
  P.≃-trans (foldImag (λ w → f (index w)))
    (P.≃-trans (P.≃-symm (sumMap (λ j → C.im (f j)) index (words (suc n))))
      (sumPerm (λ j → C.im (f j)) (permutation n)))
