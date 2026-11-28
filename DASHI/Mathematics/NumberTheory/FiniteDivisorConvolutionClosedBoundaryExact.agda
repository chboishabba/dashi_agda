module DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionClosedBoundaryExact where

-- Native source attempt. Close both actual equality-stratum folds using
-- the original factor scan and the four already-proved antidifferences.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; _<_; _∸_)
import Data.Nat.Properties as N
open import Data.List.Base using (List; []; _∷_; map; filter)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.Propositional.Properties as M
import Data.List.Relation.Unary.Any as Any
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Integer.Base using (ℤ; +_; _+_; _*_; -_)
import Data.Integer.Properties as Z
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as H
import DASHI.Mathematics.NumberTheory.FiniteOneToEnumerationExact as One
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionSignedBoundaryExact as B
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionBoundaryRegroupExact as R
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionEqualityPermutationExact as E
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionFactorChartExact as C
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionShearExact as S
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as P
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionShearPermutationExact as G
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionInteriorFoldExact as I

scaleFold : ∀ {A : Set} (m : ℤ) (f : A → ℤ) (xs : List A) →
  m * B.foldZ f xs ≡ B.foldZ (λ x → m * f x) xs
scaleFold m f [] = Z.*-zeroʳ m
scaleFold m f (x ∷ xs) =
  trans (Z.*-distribˡ-+ m (f x) (B.foldZ f xs))
    (cong (m * f x +_) (scaleFold m f xs))

splitInteger : (d t : Nat) → t < d →
  (+ (d ∸ t)) ≡ (+ d) + ((- (+ 1)) * (+ t))
splitInteger d t h =
  let x = + t
      y = + (d ∸ t)
      z = + d
      e = trans (sym (Z.pos-+ t (d ∸ t))) (cong +_ (C.splitSum d t h))
  in trans (solve 2 (λ x y → y := (x :+ y) :+ (con (- (+ 1)) :* x)) refl x y)
      (cong (λ v → v + ((- (+ 1)) * x)) e)

-- Per-factor strict split, on the same original XY observation.
xyTerm : (f : B.Weight) (m : ℤ) (n d k : Nat) →
  d ≤ n → (t : Nat) → t < d →
  m * B.Gplus f (E.xyQuad ((d , k) , t)) ≡
  m * f (+ d) ((+ d) + ((- (+ 1)) * (+ t)))
xyTerm f m n d k hd t ht =
  cong (m *_) (cong₂ f (cong +_ (C.splitSum d t ht)) (splitInteger d t ht))
  where
  cong₂ : ∀ {a b c d : ℤ} → (f : ℤ → ℤ → ℤ) → a ≡ b → c ≡ d → f a c ≡ f b d
  cong₂ f refl refl = refl

xyRow : (f : B.Weight) (m : ℤ) (boundary : ℤ → ℤ) →
  ((r : Nat) → S.scaledBoundaryPrefix f m (+ (suc r)) r ≡ boundary (+ (suc r))) →
  (n r k : Nat) → suc r ≤ suc n →
  B.foldZ (λ t → m * B.Gplus f (E.xyQuad ((suc r , k) , t)))
    (filter (λ t → t N.<? suc r) (H.oneTo (suc n))) ≡ boundary (+ (suc r))
xyRow f m boundary closed n r k hd =
  let xs = filter (λ t → t N.<? suc r) (H.oneTo (suc n))
      g = λ t → m * f (+ (suc r)) ((+ (suc r)) + ((- (+ 1)) * (+ t)))
  in trans (B.foldCongOn (λ t → m * B.Gplus f (E.xyQuad ((suc r , k) , t))) g xs
      (λ {t} h → xyTerm f m (suc n) (suc r) k hd t
        (proj₂ (M.∈-filter⁻ (λ t → t N.<? suc r) h))))
      (trans (cong (B.foldZ g) (R.strictPrefix (suc r) n hd))
        (trans (R.prefixObservation f m (+ (suc r)) r) (closed r)))

xyFactor : (f : B.Weight) (m : ℤ) (boundary : ℤ → ℤ) →
  ((r : Nat) → S.scaledBoundaryPrefix f m (+ (suc r)) r ≡ boundary (+ (suc r))) →
  (n : Nat) (p : P.PositiveFactorPair (suc n)) →
  B.foldZ (λ t → m * B.Gplus f (E.xyQuad (E.factorKey p , t)))
    (filter (λ t → t N.<? P.divisor p) (H.oneTo (suc n))) ≡ boundary (+ P.divisor p)
xyFactor f m boundary closed n (P.positiveFactorPair zero () hd k e)
xyFactor f m boundary closed n (P.positiveFactorPair (suc r) hp hd k e) =
  xyRow f m boundary closed n r (suc k) hd

xyClosed : (f : B.Weight) (m : ℤ) (boundary : ℤ → ℤ) →
  ((r : Nat) → S.scaledBoundaryPrefix f m (+ (suc r)) r ≡ boundary (+ (suc r))) →
  (n : Nat) (pn : zero < suc n) →
  m * B.foldZ (B.Gplus f) (B.eq S.x S.y (G.omega (suc n))) ≡
  B.foldZ (λ p → boundary (+ P.divisor p)) (P.positiveFactorPairs (suc n) pn)
xyClosed f m boundary closed n pn =
  let ps = P.positiveFactorPairs (suc n) pn
      obs = λ q → m * B.Gplus f q
      row = λ (d , k) → B.foldZ (λ t → obs (E.xyQuad ((d , k) , t)))
                    (filter (λ t → t N.<? d) (H.oneTo (suc n)))
  in trans (scaleFold m (B.Gplus f) (B.eq S.x S.y (G.omega (suc n))))
       (trans (R.xyRegroup obs (suc n) pn)
         (trans (B.foldMap row E.factorKey ps)
           (B.foldCongOn (λ p → row (E.factorKey p)) (λ p → boundary (+ P.divisor p)) ps
             (λ {p} _ → xyFactor f m boundary closed n p))))

-- AB observation is constant on the strict quotient split.
constantPrefix : (v : ℤ) (n : Nat) →
  B.foldZ (λ (_ : Nat) → v) (H.oneTo n) ≡ (+ n) * v
constantPrefix v zero = sym (Z.*-zeroˡ v)
constantPrefix v (suc n) =
  trans (R.foldAscending (λ _ → v) n)
    (trans (cong (_+ v) (constantPrefix v n))
      (trans (solve 2 (λ n v → n :* v :+ v := (n :+ con (+ 1)) :* v) refl (+ n) v)
        (cong (_* v) (S.nextInteger n))))

abFactor : (f : B.Weight) (m : ℤ) (n : Nat) (p : P.PositiveFactorPair (suc n)) →
  B.foldZ (λ t → m * B.F f (E.abQuad (E.factorKey p , t)))
    (filter (λ t → t N.<? suc (P.predecessor p)) (H.oneTo (suc n))) ≡
  (+ P.predecessor p) * (m * f (+ P.divisor p) (+ P.divisor p))
abFactor f m n p =
  let v = m * f (+ P.divisor p) (+ P.divisor p)
  in trans (cong (B.foldZ (λ _ → v)) (R.strictPrefix (suc (P.predecessor p)) n
      (P.copiesBoundByProduct p))) (constantPrefix v (P.predecessor p))

abClosed : (f : B.Weight) (m : ℤ) (n : Nat) (pn : zero < suc n) →
  m * B.foldZ (B.F f) (B.eq S.a S.b (G.omega (suc n))) ≡
  B.foldZ (λ p → (+ P.predecessor p) * (m * f (+ P.divisor p) (+ P.divisor p)))
    (P.positiveFactorPairs (suc n) pn)
abClosed f m n pn =
  let ps = P.positiveFactorPairs (suc n) pn
      obs = λ q → m * B.F f q
      row = λ (d , k) → B.foldZ (λ t → obs (E.abQuad ((d , k) , t)))
                      (filter (λ t → t N.<? k) (H.oneTo (suc n)))
  in trans (scaleFold m (B.F f) (B.eq S.a S.b (G.omega (suc n))))
       (trans (R.abRegroup obs (suc n) pn)
         (trans (B.foldMap row E.factorKey ps)
           (B.foldCongOn (λ p → row (E.factorKey p))
             (λ p → (+ P.predecessor p) * (m * f (+ P.divisor p) (+ P.divisor p))) ps
             (λ {p} _ → abFactor f m n p))))

-- Specialize the actual cancellation identity, not an asserted boundary
-- equation. This composes all previous finite owners.
scaledInterior : (f : B.Weight) (h : B.ShearSymmetry f) (m : ℤ) (boundary : ℤ → ℤ) →
  ((r : Nat) → S.scaledBoundaryPrefix f m (+ (suc r)) r ≡ boundary (+ (suc r))) →
  (n : Nat) (pn : zero < suc n) →
  m * B.foldZ (I.delta f) (G.omega (suc n)) +
    B.foldZ (λ p → (+ P.predecessor p) * (m * f (+ P.divisor p) (+ P.divisor p)))
      (P.positiveFactorPairs (suc n) pn)
  ≡ B.foldZ (λ p → boundary (+ P.divisor p)) (P.positiveFactorPairs (suc n) pn)
scaledInterior f h m boundary closed n pn =
  let o = G.omega (suc n)
      a = B.foldZ (I.delta f) o
      b = B.foldZ (B.F f) (B.eq S.a S.b o)
      c = B.foldZ (B.Gplus f) (B.eq S.x S.y o)
      base = trans (cong (a +_) (E.abFold (B.F f) (suc n) pn))
        (trans (I.interior f h (suc n) pn) (sym (E.xyFold (B.Gplus f) (suc n) pn)))
  in trans (cong (m * a +_) (sym (abClosed f m n pn)))
       (trans (sym (Z.*-distribˡ-+ m a b))
         (trans (cong (m *_) base) (xyClosed f m boundary closed n pn)))

closedInterior1 = scaledInterior S.weight1 S.weight1ShearSymmetry (+ 6) S.boundary1 S.boundaryClosed1

closedInterior2 = scaledInterior S.weight2 S.weight2ShearSymmetry (+ 30) S.boundary2 S.boundaryClosed2

closedInterior3 = scaledInterior S.weight3 S.weight3ShearSymmetry (+ 420) S.boundary3 S.boundaryClosed3

closedInterior4 = scaledInterior S.weight4 S.weight4ShearSymmetry (+ 30) S.boundary4 S.boundaryClosed4
