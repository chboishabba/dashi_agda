module DASHI.Moonshine.JInvariantThetaJacobiAllIndexExact where

-- SOURCE-WRITTEN, kernel pending. Original literal all-index Jacobi
-- coefficients from the actual signed Hadamard permutation, no cardinality
-- or analytic premise. Classical Jacobi identity; DASHI BIDI attachment.
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc) renaming (_+_ to _+N_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _*_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)
import Data.Nat.Properties as NP
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻; ∈-++⁻)
import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs.Core as AP
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UP
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans; subst; _≢_)
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as W
import DASHI.Mathematics.NumberTheory.FiniteDependentPairEnumerationExact as Dep
import DASHI.Moonshine.JInvariantThetaLegendreSignedGeometryExact as T
import DASHI.Moonshine.JInvariantThetaIntegerTwistExact as Tw
import DASHI.Moonshine.JInvariantThetaHadamardIntegralChartExact as H
import DASHI.Moonshine.JInvariantThetaIntegralParityExact as P
import DASHI.Moonshine.JInvariantThetaRawCoordinateGradeExact as R
import DASHI.Moonshine.JInvariantThetaBoundedShellEnumerationExact as E
import DASHI.Moonshine.JInvariantThetaRawHadamardTransportExact as F

-- Coordinate equality at the weighted degree follows from the actual
-- raw norm identity. All divisions by four are exact cancellation.
forwardGrade : ∀ side x → P.Odd (H.total (R.quadOf x)) →
  suc (R.grade R.halfGrade (F.forward (side , x))) ≡ R.grade R.squareGrade x
forwardGrade side x hx = P.plusInject
  (P.cancelScale 3 _ _
    (trans (sym (R.oddNormRead (F.forward (side , x))))
      (trans (F.forwardNorm side x hx)
        (cong ((+ 4) *_) (R.integerNormRead x)))))

sourceGrade : ∀ y → R.grade R.squareGrade (F.source (F.preimageAt y)) ≡ suc (R.grade R.halfGrade y)
sourceGrade y with F.preimageAt y
... | F.preimage e x hx h =
  trans (sym (forwardGrade e x hx)) (cong (λ z → suc (R.grade R.halfGrade z)) h)

sourceGradeOdd : ∀ y → P.Odd (+ suc (R.grade R.halfGrade y))
sourceGradeOdd y with F.preimageAt y | sourceGrade y
... | F.preimage e x hx h | g =
  subst P.Odd (trans (R.integerNormRead x) (cong +_ g))
    (P.normOddFromTotalOdd (R.quadOf x) hx)

-- Every square-shell point at an odd degree has odd total, including
-- negative coordinates. No finite parity table is used.
oddTotalAt : ∀ n → P.Odd (+ n) → ∀ x →
  R.grade R.squareGrade x ≡ n → P.Odd (H.total (R.quadOf x))
oddTotalAt n hn x g = P.totalOddFromNormOdd (R.quadOf x)
  (subst P.Odd (sym (trans (R.integerNormRead x) (cong +_ g))) hn)

tag : Bool → R.Pairs → Bool × R.Pairs
tag e x = e , x

tagInject : ∀ e {x y} → tag e x ≡ tag e y → x ≡ y
tagInject e refl = refl

tagged : List R.Pairs → List (Bool × R.Pairs)
tagged xs = map (tag false) xs ++ map (tag true) xs

taggedUnique : ∀ {xs} → Unique xs → Unique (tagged xs)
taggedUnique {xs} u = Dep.uniqueAppendDisjoint
  (UP.map⁺ (tagInject false) u) (UP.map⁺ (tagInject true) u) cross
  where
  cross : ∀ {x y} → x ∈ map (tag false) xs → y ∈ map (tag true) xs → x ≢ y
  cross xm ym eq with ∈-map⁻ (tag false) xm | ∈-map⁻ (tag true) ym
  ... | a , am , refl | b , bm , refl = impossible eq
    where
    impossible : (false , a) ≢ (true , b)
    impossible ()

taggedSound : ∀ xs {x} → x ∈ tagged xs → proj₂ x ∈ xs
taggedSound xs m with ∈-++⁻ (map (tag false) xs) m
... | inj₁ l with ∈-map⁻ (tag false) l
...   | a , am , refl = am
taggedSound xs m | inj₂ r with ∈-map⁻ (tag true) r
...   | a , am , refl = am

taggedComplete : ∀ xs e {x} → x ∈ xs → (e , x) ∈ tagged xs
taggedComplete xs false m = Dep.appendMemberLeft (∈-map⁺ (tag false) m)
taggedComplete xs true m = Dep.appendMemberRight (map (tag false) xs) (∈-map⁺ (tag true) m)

-- Only odd-total inputs are injected. This restricted theorem avoids
-- pretending the fallback branch of oddParam is injective off-domain.
mapUniqueOn : ∀ {A B : Set} (f : A → B) {xs : List A} →
  Unique xs →
  (∀ {a b} → a ∈ xs → b ∈ xs → f a ≡ f b → a ≡ b) →
  Unique (map f xs)
mapUniqueOn f {[]} u inject = AP.[]
mapUniqueOn f {x ∷ xs} (AP._∷_ fresh rest) inject =
  AP._∷_ (All.tabulate different) (mapUniqueOn f rest
    (λ a b h → inject (Any.there a) (Any.there b) h))
  where
  different : ∀ {y} → y ∈ map f xs → f x ≢ y
  different m eq with ∈-map⁻ f m
  ... | z , zm , refl = All.lookup fresh zm (inject (Any.here refl) (Any.there zm) eq)

lenMap : ∀ {A B : Set} (f : A → B) xs → W.listLength (map f xs) ≡ W.listLength xs
lenMap f [] = refl
lenMap f (x ∷ xs) = cong suc (lenMap f xs)

lenAppend : ∀ {A : Set} (xs ys : List A) → W.listLength (xs ++ ys) ≡ W.listLength xs +N W.listLength ys
lenAppend [] ys = refl
lenAppend (x ∷ xs) ys = cong suc (lenAppend xs ys)

lenTagged : ∀ xs → W.listLength (tagged xs) ≡ W.listLength xs +N W.listLength xs
lenTagged xs = trans (lenAppend (map (tag false) xs) (map (tag true) xs))
  (cong₂ _+N_ (lenMap (tag false) xs) (lenMap (tag true) xs))

module OddDegree (k : Nat) (hn : P.Odd (+ suc k)) where
  xs : List R.Pairs
  xs = R.integerList (suc k) (suc k)
  ys : List R.Pairs
  ys = R.oddList k k

  sourceOdd : ∀ {x} → x ∈ tagged xs → P.Odd (H.total (R.quadOf (proj₂ x)))
  sourceOdd m = oddTotalAt (suc k) hn _
    (E.integerShellSound (suc k) (suc k) (taggedSound xs m))

  sourceUnique : Unique (map F.forward (tagged xs))
  sourceUnique = mapUniqueOn F.forward (taggedUnique (E.integerShellUnique (suc k) (suc k)))
    (λ { (e , x) } { (f , y) } m n h → F.forwardInjectOn e f x y (sourceOdd m) (sourceOdd n) h)

  forwardMember : ∀ {y} → y ∈ map F.forward (tagged xs) → y ∈ ys
  forwardMember m with ∈-map⁻ F.forward m
  ... | (e , x) , xm , refl =
    E.oddShellComplete k k NP.≤-refl _
      (NP.suc-injective (trans (forwardGrade e x (sourceOdd xm))
        (E.integerShellSound (suc k) (suc k) (taggedSound xs xm))))

  backwardMember : ∀ {y} → y ∈ ys → y ∈ map F.forward (tagged xs)
  backwardMember {y} m with F.preimageAt y | sourceGrade y
  ... | F.preimage e x hx h | g =
    subst (_∈ map F.forward (tagged xs)) h
      (∈-map⁺ F.forward (taggedComplete xs e
        (E.integerShellComplete (suc k) (suc k) NP.≤-refl x
          (trans g (cong suc (E.oddShellSound k k m))))))

  shellPermutation : map F.forward (tagged xs) Perm.↭ ys
  shellPermutation = W.uniqueMembershipEquivalenceToPermutation sourceUnique
    (E.oddShellUnique k k) forwardMember backwardMember

  countTwice : W.listLength ys ≡ W.listLength xs +N W.listLength xs
  countTwice =
    trans (sym (W.permutationPreservesLength shellPermutation))
      (trans (lenMap F.forward (tagged xs)) (lenTagged xs))

  aTwiceB : T.A (suc k) ≡ T.B (suc k) + T.B (suc k)
  aTwiceB =
    trans (sym (R.oddCount k k NP.≤-refl))
      (trans (cong +_ countTwice)
        (cong₂ _+_ (R.integerCount (suc k) (suc k) NP.≤-refl)
          (R.integerCount (suc k) (suc k) NP.≤-refl)))

emptyIfNoMember : ∀ {A : Set} (xs : List A) → (∀ {x} → x ∈ xs → ⊥) → xs ≡ []
emptyIfNoMember [] h = refl
emptyIfNoMember (x ∷ xs) h = ⊥-elim (h (Any.here refl))

evenAZero : ∀ k → P.Even (+ suc k) → T.A (suc k) ≡ + 0
evenAZero k hn =
  trans (sym (R.oddCount k k NP.≤-refl))
    (cong (λ xs → + W.listLength xs)
      (emptyIfNoMember (R.oddList k k) λ {y} m →
        P.evenNotOdd (+ suc k) hn
          (subst P.Odd (cong (λ i → + suc i) (E.oddShellSound k k m))
            (sourceGradeOdd y))))

jacobiAll : ∀ n → T.B n ≡ T.add T.A T.C n
jacobiAll zero = T.jacobi0
jacobiAll (suc k) with P.signByParity (suc k)
... | inj₁ (he , hs) =
  let n = suc k
      hC = trans (Tw.negativeSheet n) (cong (_* T.B n) hs)
  in trans (solve 1 (λ b → b := con (+ 0) :+ con (+ 1) :* b) refl (T.B n))
    (cong₂ _+_ (sym (evenAZero k he)) (sym hC))
... | inj₂ (ho , hs) =
  let n = suc k
      module O = OddDegree k ho
      hC = trans (Tw.negativeSheet n) (cong (_* T.B n) hs)
  in trans (solve 1 (λ b → b := (b :+ b) :+ con (-[1+ 0 ]) :* b) refl (T.B n))
    (cong₂ _+_ (sym O.aTwiceB) (sym hC))
