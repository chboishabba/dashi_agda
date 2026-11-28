module DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionInteriorFoldExact where

-- Source-written; kernel acceptance deferred. Reuse the actual signed
-- shear boundary and equality-stratum permutations.
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_<_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Integer.Base using (ℤ; +_; _+_; -_)
import Data.Integer.Properties as ZP
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionSignedBoundaryExact as B
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionEqualityPermutationExact as E
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionShearPermutationExact as G
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionShearExact as S

-- Distribute the two original observations on exactly the same list.
foldAdd : ∀ {A : Set} (f g : A → ℤ) (xs : List A) →
  B.foldZ (λ x → f x + g x) xs ≡ B.foldZ f xs + B.foldZ g xs
foldAdd f g [] = refl
foldAdd f g (x ∷ xs) =
  trans (cong ((f x + g x) +_) (foldAdd f g xs))
    (solve 4 (λ a b c d → (a :+ b) :+ (c :+ d) := (a :+ c) :+ (b :+ d))
      refl (f x) (g x) (B.foldZ f xs) (B.foldZ g xs))

-- Cancel the common interior baseline without discarding either signed
-- boundary. The double diagonal remains in both observations.
cancelBaseline : (a b c d : ℤ) → (a + b) + c ≡ b + d → a + c ≡ d
cancelBaseline a b c d h =
  ZP.+-cancelˡ-≡ b
    (trans (solve 3 (λ a b c → b :+ (a :+ c) := (a :+ b) :+ c)
      refl a b c) h)

delta : B.Weight → S.Quad → ℤ
delta f q = B.Gplus f q + (- B.F f q)

pointwise : (f : B.Weight) (q : S.Quad) →
  B.Gplus f q ≡ delta f q + B.F f q
pointwise f q =
  let a = B.Gplus f q
      b = B.F f q
  in sym (trans (ZP.+-assoc a (- b) b)
       (trans (cong (a +_) (ZP.+-inverseˡ b)) (ZP.+-identityʳ a)))

interior : (f : B.Weight) → B.ShearSymmetry f →
  (n : Nat) (pn : zero < n) →
  B.foldZ (delta f) (G.omega n) +
    B.foldZ (λ z → B.F f (E.abQuad z)) (E.abKeys n pn)
  ≡ B.foldZ (λ z → B.Gplus f (E.xyQuad z)) (E.xyKeys n pn)
interior f h n pn =
  let o = G.omega n
      a = B.foldZ (delta f) o
      b = B.foldZ (B.F f) o
      c = B.foldZ (B.F f) (B.eq S.a S.b o)
      d = B.foldZ (B.Gplus f) (B.eq S.x S.y o)
      e = trans (B.foldCongOn (B.Gplus f)
            (λ q → delta f q + B.F f q) o (λ {q} _ → pointwise f q))
            (foldAdd (delta f) (B.F f) o)
  in trans (cong (a +_) (sym (E.abFold (B.F f) n pn)))
    (trans (cancelBaseline a b c d
      (trans (cong (_+ c) (sym e)) (B.boundary f h n)))
      (E.xyFold (B.Gplus f) n pn))
