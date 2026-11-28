module DASHI.Moonshine.JInvariantThetaBoundedShellEnumerationExact where

-- Literal bounded integer/odd-coordinate labels, not an abstract
-- cardinality field. All finite products use the existing list machinery.
-- SOURCE-WRITTEN, kernel pending.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (ℤ; +_; -[1+_])
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NP
open import Data.List.Base using (List; []; _∷_; _++_; cartesianProductWith)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using
  (∈-++⁻; ∈-cartesianProductWith⁺; ∈-filter⁺; ∈-filter⁻)
import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs.Core as AP
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UP
open import Data.Product.Base using (Σ; _×_; _,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; _≢_)
import DASHI.Mathematics.NumberTheory.FiniteDependentPairEnumerationExact as Dep
import DASHI.Mathematics.NumberTheory.FiniteOneToEnumerationExact as One
import DASHI.Moonshine.JInvariantThetaBoundedScanReadoutExact as S
import DASHI.Moonshine.JInvariantThetaRawCoordinateGradeExact as R
import DASHI.Moonshine.JInvariantThetaLegendreSignedGeometryExact as T

-- Generic descending enumeration of f(0)..f(k).
prefix : (Nat → ℤ) → Nat → List ℤ
prefix f zero = f zero ∷ []
prefix f (suc k) = f (suc k) ∷ prefix f k

prefixSound : ∀ f k {z} → z ∈ prefix f k →
  Σ Nat (λ i → (i ≤ k) × (z ≡ f i))
prefixSound f zero (Any.here h) = zero , z≤n , h
prefixSound f zero (Any.there ())
prefixSound f (suc k) (Any.here h) = suc k , NP.≤-refl , h
prefixSound f (suc k) (Any.there m) with prefixSound f k m
... | i , hi , eq = i , NP.≤-step hi , eq

prefixComplete : ∀ f k i → i ≤ k → f i ∈ prefix f k
prefixComplete f zero zero hi = Any.here refl
prefixComplete f zero (suc i) ()
prefixComplete f (suc k) i hi with i NP.≟ suc k
... | yes eq = Any.here (cong f eq)
... | no ne = Any.there (prefixComplete f k i (One.≤-pred (One.strictFromLeDifferent hi ne)))

prefixUnique : ∀ f → (∀ {i j} → f i ≡ f j → i ≡ j) →
  ∀ k → Unique (prefix f k)
prefixUnique f inj zero = AP._∷_ All.[] AP.[]
prefixUnique f inj (suc k) =
  AP._∷_ (All.tabulate fresh) (prefixUnique f inj k)
  where
  fresh : ∀ {z} → z ∈ prefix f k → f (suc k) ≢ z
  fresh mem eq with prefixSound f k mem
  ... | i , hi , refl = NP.1+n≰n (subst (_≤ k) (sym (inj eq)) hi)

plusInject : ∀ {i j} → (+ i) ≡ (+ j) → i ≡ j
plusInject refl = refl

minusInject : ∀ {i j} → -[1+ i ] ≡ -[1+ j ] → i ≡ j
minusInject refl = refl

plusNotMinus : ∀ {i j} → (+ i) ≢ -[1+ j ]
plusNotMinus ()

posPrefix : ∀ k → R.posHalf k ≡ prefix +_ k
posPrefix zero = refl
posPrefix (suc k) = cong ((+ suc k) ∷_) (posPrefix k)

negPrefix : ∀ k → R.negHalf k ≡ prefix -[1+_] k
negPrefix zero = refl
negPrefix (suc k) = cong (-[1+ suc k ] ∷_) (negPrefix k)

posTail : ∀ k → R.pos k ++ ((+ 0) ∷ []) ≡ R.posHalf k
posTail zero = refl
posTail (suc k) = cong ((+ suc k) ∷_) (posTail k)

negTail : ∀ k → R.neg (suc k) ≡ R.negHalf k
negTail zero = refl
negTail (suc k) = cong (-[1+ suc k ] ∷_) (negTail k)

-- Positive and negative tails have no repeated coordinate.
posSound : ∀ k {z} → z ∈ R.pos k → Σ Nat (λ i → (suc i ≤ k) × (z ≡ (+ suc i)))
posSound zero ()
posSound (suc k) (Any.here h) = k , NP.≤-refl , h
posSound (suc k) (Any.there m) with posSound k m
... | i , hi , e = i , NP.≤-step hi , e

negSound : ∀ k {z} → z ∈ R.neg k → Σ Nat (λ i → (suc i ≤ k) × (z ≡ -[1+ i ]))
negSound zero ()
negSound (suc k) (Any.here h) = k , NP.≤-refl , h
negSound (suc k) (Any.there m) with negSound k m
... | i , hi , e = i , NP.≤-step hi , e

posComplete : ∀ k i → suc i ≤ k → (+ suc i) ∈ R.pos k
posComplete zero i ()
posComplete (suc k) i hi with suc i NP.≟ suc k
... | yes e = Any.here (cong +_ e)
... | no ne = Any.there (posComplete k i (One.≤-pred (One.strictFromLeDifferent hi ne)))

negComplete : ∀ k i → suc i ≤ k → -[1+ i ] ∈ R.neg k
negComplete zero i ()
negComplete (suc k) i hi with suc i NP.≟ suc k
... | yes refl = Any.here refl
... | no ne = Any.there (negComplete k i (One.≤-pred (One.strictFromLeDifferent hi ne)))

posUnique : ∀ k → Unique (R.pos k)
posUnique zero = AP.[]
posUnique (suc k) = AP._∷_ (All.tabulate fresh) (posUnique k)
  where
  fresh : ∀ {z} → z ∈ R.pos k → (+ suc k) ≢ z
  fresh mem eq with posSound k mem
  ... | i , hi , refl = NP.1+n≰n (subst (_≤ k) (sym (plusInject eq)) hi)

negUnique : ∀ k → Unique (R.neg k)
negUnique zero = AP.[]
negUnique (suc k) = AP._∷_ (All.tabulate fresh) (negUnique k)
  where
  fresh : ∀ {z} → z ∈ R.neg k → -[1+ k ] ≢ z
  fresh mem eq with negSound k mem
  ... | i , hi , refl = NP.1+n≰n (subst (λ j → suc j ≤ k) (sym (minusInject eq)) hi)

integerUnique : ∀ k → Unique (R.integerLabels k)
integerUnique k = AP._∷_ (All.tabulate fresh)
  (Dep.uniqueAppendDisjoint (posUnique k) (negUnique k) cross)
  where
  cross : ∀ {x y} → x ∈ R.pos k → y ∈ R.neg k → x ≢ y
  cross xm ym eq with posSound k xm | negSound k ym
  ... | i , hi , refl | j , hj , refl = plusNotMinus eq
  fresh : ∀ {z} → z ∈ R.pos k ++ R.neg k → (+ 0) ≢ z
  fresh mem with ∈-++⁻ (R.pos k) mem
  ... | inj₁ pm with posSound k pm
  ...   | i , hi , refl = λ ()
  fresh mem | inj₂ nm with negSound k nm
  ...   | i , hi , refl = plusNotMinus

oddUnique : ∀ k → Unique (R.oddLabels k)
oddUnique k = Dep.uniqueAppendDisjoint
  (subst Unique (sym (posPrefix k)) (prefixUnique +_ plusInject k))
  (subst Unique (sym (negPrefix k)) (prefixUnique -[1+_] minusInject k)) cross
  where
  cross : ∀ {x y} → x ∈ R.posHalf k → y ∈ R.negHalf k → x ≢ y
  cross xm ym eq with prefixSound +_ k (subst (_ ∈_) (posPrefix k) xm)
                     | prefixSound -[1+_] k (subst (_ ∈_) (negPrefix k) ym)
  ... | i , hi , refl | j , hj , refl = plusNotMinus eq

integerComplete : ∀ k z → R.squareGrade z ≤ k → z ∈ R.integerLabels k
integerComplete k (+ zero) hi = Any.here refl
integerComplete k (+ suc i) hi = Any.there (Dep.appendMemberLeft
  (posComplete k i (NP.≤-trans (S.squareBound (suc i)) hi)))
integerComplete k -[1+ i ] hi = Any.there (Dep.appendMemberRight (R.pos k)
  (negComplete k i (NP.≤-trans (S.squareBound (suc i)) hi)))

oddComplete : ∀ k z → R.halfGrade z ≤ k → z ∈ R.oddLabels k
oddComplete k (+ i) hi = Dep.appendMemberLeft
  (subst ((+ i) ∈_) (sym (posPrefix k))
    (prefixComplete +_ k i (NP.≤-trans (S.triBound i) hi)))
oddComplete k -[1+ i ] hi = Dep.appendMemberRight (R.posHalf k)
  (subst (-[1+ i ] ∈_) (sym (negPrefix k))
    (prefixComplete -[1+_] k i (NP.≤-trans (S.triBound i) hi)))

pairInject : ∀ {A B : Set} {a c : A} {b d : B} →
  (a , b) ≡ (c , d) → (a ≡ c) × (b ≡ d)
pairInject refl = refl , refl

fourUnique : ∀ {xs} → Unique xs → Unique (R.fourLabels xs)
fourUnique u = UP.cartesianProductWith⁺ _,_ pairInject
  (UP.cartesianProductWith⁺ _,_ pairInject u u)
  (UP.cartesianProductWith⁺ _,_ pairInject u u)

fourComplete : ∀ (g : ℤ → Nat) (xs : List ℤ) {cutoff : Nat} →
  (∀ z → g z ≤ cutoff → z ∈ xs) →
  (x : R.Pairs) → R.grade g x ≤ cutoff → x ∈ R.fourLabels xs
fourComplete g xs complete ((a , b) , (c , d)) h =
  let ab = g a + g b
      cd = g c + g d
      p = NP.≤-trans (NP.m≤m+n ab cd) h
      q = NP.≤-trans (NP.m≤n+m cd ab) h
  in ∈-cartesianProductWith⁺ _,_
    (∈-cartesianProductWith⁺ _,_
      (complete a (NP.≤-trans (NP.m≤m+n (g a) (g b)) p))
      (complete b (NP.≤-trans (NP.m≤n+m (g b) (g a)) p)))
    (∈-cartesianProductWith⁺ _,_
      (complete c (NP.≤-trans (NP.m≤m+n (g c) (g d)) q))
      (complete d (NP.≤-trans (NP.m≤n+m (g d) (g c)) q)))

integerShellUnique : ∀ cutoff n → Unique (R.integerList cutoff n)
integerShellUnique cutoff n = UP.filter⁺ (λ x → R.grade R.squareGrade x NP.≟ n)
  (fourUnique (integerUnique cutoff))

oddShellUnique : ∀ cutoff n → Unique (R.oddList cutoff n)
oddShellUnique cutoff n = UP.filter⁺ (λ x → R.grade R.halfGrade x NP.≟ n)
  (fourUnique (oddUnique cutoff))

integerShellComplete : ∀ cutoff n → n ≤ cutoff → ∀ x →
  R.grade R.squareGrade x ≡ n → x ∈ R.integerList cutoff n
integerShellComplete cutoff n h x e =
  ∈-filter⁺ (λ z → R.grade R.squareGrade z NP.≟ n)
    (fourComplete R.squareGrade (R.integerLabels cutoff) (integerComplete cutoff) x
      (subst (_≤ cutoff) (sym e) h)) e

oddShellComplete : ∀ cutoff n → n ≤ cutoff → ∀ x →
  R.grade R.halfGrade x ≡ n → x ∈ R.oddList cutoff n
oddShellComplete cutoff n h x e =
  ∈-filter⁺ (λ z → R.grade R.halfGrade z NP.≟ n)
    (fourComplete R.halfGrade (R.oddLabels cutoff) (oddComplete cutoff) x
      (subst (_≤ cutoff) (sym e) h)) e

integerShellSound : ∀ cutoff n {x} → x ∈ R.integerList cutoff n → R.grade R.squareGrade x ≡ n
integerShellSound cutoff n m with ∈-filter⁻ (λ z → R.grade R.squareGrade z NP.≟ n) m
... | _ , e = e

oddShellSound : ∀ cutoff n {x} → x ∈ R.oddList cutoff n → R.grade R.halfGrade x ≡ n
oddShellSound cutoff n m with ∈-filter⁻ (λ z → R.grade R.halfGrade z NP.≟ n) m
... | _ , e = e
