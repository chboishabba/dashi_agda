module DASHI.Moonshine.JInvariantThetaGradedCauchyCountExact where

-- Exact finite graded counting on the ORIGINAL rowZ Cauchy history.
-- Classical product-fibre counting, DASHI native attachment.
-- No new analytic series, cardinality axiom or bounded-degree assumption.
-- SOURCE-WRITTEN, kernel pending.
open import Agda.Builtin.Nat using (Nat; zero; suc) renaming (_+_ to _+N_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; _++_; map; cartesianProductWith)
open import Data.Product.Base using (_,_)
open import Data.Integer using (ℤ; +_; _+_; _*_)
import Data.Integer.Properties as Z
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionIntegerRowExact as I
import DASHI.Moonshine.JInvariantThetaIntegerTwistExact as T
open I using (SeriesZ; rowZ; rowHead; rowZero)

delta : Nat → SeriesZ
delta zero zero = + 1
delta zero (suc n) = + 0
delta (suc k) zero = + 0
delta (suc k) (suc n) = delta k n

delay : Nat → SeriesZ → SeriesZ
delay zero f n = f n
delay (suc k) f zero = + 0
delay (suc k) f (suc n) = delay k f n

plus : SeriesZ → SeriesZ → SeriesZ
plus f g n = f n + g n

hist : List Nat → SeriesZ
hist [] n = + 0
hist (k ∷ ks) n = delta k n + hist ks n

rowAdd : ∀ f g h n → rowZ (plus f g) h n ≡ rowZ f h n + rowZ g h n
rowAdd f g h zero =
  trans (rowZero (plus f g) h)
    (trans (Z.*-distribʳ-+ (h zero) (f zero) (g zero))
      (cong₂ _+_ (sym (rowZero f h)) (sym (rowZero g h))))
rowAdd f g h (suc n) =
  trans (rowHead (plus f g) h n)
    (trans (cong₂ _+_ (Z.*-distribʳ-+ (h (suc n)) (f zero) (g zero))
        (rowAdd (T.shift f) (T.shift g) h n))
      (trans (solve 4 (λ a b c d → (a :+ b) :+ (c :+ d) := (a :+ c) :+ (b :+ d))
        refl (f zero * h (suc n)) (g zero * h (suc n))
        (rowZ (T.shift f) h n) (rowZ (T.shift g) h n))
        (cong₂ _+_ (sym (rowHead f h n)) (sym (rowHead g h n)))))

rowDelta : ∀ k f n → rowZ (delta k) f n ≡ delay k f n
rowDelta zero f n = T.rowUnitLeft f n
rowDelta (suc k) f zero = trans (rowZero (delta (suc k)) f) (Z.*-zeroˡ _)
rowDelta (suc k) f (suc n) =
  trans (rowHead (delta (suc k)) f n)
    (trans (cong₂ _+_ (Z.*-zeroˡ _) (rowDelta k f n))
      (Z.+-identityˡ _))

histAppend : ∀ xs ys n → hist (xs ++ ys) n ≡ hist xs n + hist ys n
histAppend [] ys n = sym (Z.+-identityˡ (hist ys n))
histAppend (k ∷ ks) ys n =
  trans (cong (delta k n +_) (histAppend ks ys n))
    (sym (Z.+-assoc (delta k n) (hist ks n) (hist ys n)))

histSucZero : ∀ xs → hist (map suc xs) zero ≡ + 0
histSucZero [] = refl
histSucZero (k ∷ ks) = trans (cong ((+ 0) +_) (histSucZero ks)) refl

histSuc : ∀ xs n → hist (map suc xs) (suc n) ≡ hist xs n
histSuc [] n = refl
histSuc (k ∷ ks) n = cong (delta k n +_) (histSuc ks n)

mapComp : ∀ {A B C : Set} (f : B → C) (g : A → B) xs →
  map f (map g xs) ≡ map (λ x → f (g x)) xs
mapComp f g [] = refl
mapComp f g (x ∷ xs) = cong (f (g x) ∷_) (mapComp f g xs)

histDelay : ∀ k xs n → hist (map (k +N_) xs) n ≡ delay k (hist xs) n
histDelay zero xs n = cong (λ ys → hist ys n) (mapId xs)
  where
  mapId : ∀ (ys : List Nat) → map (zero +N_) ys ≡ ys
  mapId [] = refl
  mapId (y ∷ ys) = cong (y ∷_) (mapId ys)
histDelay (suc k) xs zero =
  trans (cong (λ ys → hist ys zero) (sym (mapComp suc (k +N_) xs)))
    (histSucZero (map (k +N_) xs))
histDelay (suc k) xs (suc n) =
  trans (cong (λ ys → hist ys (suc n)) (sym (mapComp suc (k +N_) xs)))
    (trans (histSuc (map (k +N_) xs) n) (histDelay k xs n))

-- Pair sum multiset, preserving multiplicities of coordinate labels.
pairGrades : List Nat → List Nat → List Nat
pairGrades [] ys = []
pairGrades (x ∷ xs) ys = map (x +N_) ys ++ pairGrades xs ys

pairCount : ∀ xs ys n → hist (pairGrades xs ys) n ≡ rowZ (hist xs) (hist ys) n
pairCount [] ys n = sym (T.rowZeroLeft (hist ys) n)
pairCount (x ∷ xs) ys n =
  trans (histAppend (map (x +N_) ys) (pairGrades xs ys) n)
    (trans (cong₂ _+_ (histDelay x ys n) (pairCount xs ys n))
      (trans (cong (_+ rowZ (hist xs) (hist ys) n) (sym (rowDelta x (hist ys) n)))
        (sym (rowAdd (delta x) (hist xs) (hist ys) n))))

fourGrades : List Nat → List Nat
fourGrades xs = pairGrades (pairGrades xs xs) (pairGrades xs xs)

fourCount : ∀ xs n →
  hist (fourGrades xs) n ≡ rowZ (rowZ (hist xs) (hist xs)) (rowZ (hist xs) (hist xs)) n
fourCount xs n =
  trans (pairCount (pairGrades xs xs) (pairGrades xs xs) n)
    (T.rowCong (hist (pairGrades xs xs)) (hist (pairGrades xs xs))
      (rowZ (hist xs) (hist xs)) (rowZ (hist xs) (hist xs))
      (pairCount xs xs) (pairCount xs xs) n)

-- Literal graded product readout. It preserves labels up to the final
-- map to degree; equal-degree occurrences are counted, never deduplicated.
pairMap : ∀ {A B : Set} (g : A → Nat) (h : B → Nat) xs ys →
  map (λ { (x , y) → g x +N h y }) (cartesianProductWith _,_ xs ys) ≡
  pairGrades (map g xs) (map h ys)
pairMap g h [] ys = refl
pairMap g h (x ∷ xs) ys =
  trans (mapAppend (λ { (a , b) → g a +N h b })
      (map (x ,_) ys) (cartesianProductWith _,_ xs ys))
    (cong₂ _++_
      (trans (mapComp (λ { (a , b) → g a +N h b }) (x ,_) ys)
        (sym (mapComp (g x +N_) h ys)))
      (pairMap g h xs ys))
  where
  mapAppend : ∀ {A B : Set} (f : A → B) xs ys →
    map f (xs ++ ys) ≡ map f xs ++ map f ys
  mapAppend f [] ys = refl
  mapAppend f (x ∷ xs) ys = cong (f x ∷_) (mapAppend f xs ys)


-- Locality at a fixed output degree. Bounded coordinate lists may be
-- larger than a coefficient's own cutoff without changing that output.
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NP

rowCongThrough : ∀ f g u v n →
  (∀ i → i ≤ n → f i ≡ u i) →
  (∀ i → i ≤ n → g i ≡ v i) →
  rowZ f g n ≡ rowZ u v n
rowCongThrough f g u v zero hf hg =
  trans (rowZero f g)
    (trans (cong₂ _*_ (hf zero z≤n) (hg zero z≤n))
      (sym (rowZero u v)))
rowCongThrough f g u v (suc n) hf hg =
  trans (rowHead f g n)
    (trans (cong₂ _+_ (cong₂ _*_ (hf zero z≤n) (hg (suc n) NP.≤-refl))
      (rowCongThrough (T.shift f) g (T.shift u) v n
        (λ i hi → hf (suc i) (s≤s hi))
        (λ i hi → hg i (NP.≤-step hi))))
      (sym (rowHead u v n)))

fourCongThrough : ∀ f g n →
  (∀ i → i ≤ n → f i ≡ g i) →
  rowZ (rowZ f f) (rowZ f f) n ≡ rowZ (rowZ g g) (rowZ g g) n
fourCongThrough f g n h =
  rowCongThrough (rowZ f f) (rowZ f f) (rowZ g g) (rowZ g g) n
    (λ i hi → rowCongThrough f f g g i
      (λ j hj → h j (NP.≤-trans hj hi)) (λ j hj → h j (NP.≤-trans hj hi)))
    (λ i hi → rowCongThrough f f g g i
      (λ j hj → h j (NP.≤-trans hj hi)) (λ j hj → h j (NP.≤-trans hj hi)))

fourCountThrough : ∀ xs f n →
  (∀ i → i ≤ n → hist xs i ≡ f i) →
  hist (fourGrades xs) n ≡ rowZ (rowZ f f) (rowZ f f) n
fourCountThrough xs f n h =
  trans (fourCount xs n) (fourCongThrough (hist xs) f n h)
