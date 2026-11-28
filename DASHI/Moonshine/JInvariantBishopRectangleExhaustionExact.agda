module DASHI.Moonshine.JInvariantBishopRectangleExhaustionExact where

-- Rectangles are filtered ORIGINAL square lists, not a new lattice codec.
-- Horizontal radius n, vertical radius max(n,m); origin remains a raw
-- omitted index via Ex.raw. Uniform absolute sandwich, then iterated
-- finite row limit passage. Source-written, kernel pending.
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Bool using (Bool)
open import Data.Nat.Base using (_⊔_) renaming (_≤_ to _≤N_)
import Data.Nat.Properties as NP
open import Data.Bool.Base using (T)
open import Data.Bool.Properties using (T-∧)
open import Data.List.Base using (List; filterᵇ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-filter⁺; ∈-filter⁻)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
open import Relation.Nullary.Decidable.Core using (T?; toWitness)
open import Function.Base using (_∘_)
open import Function.Bundles using (Equivalence)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised.Properties as QP
import Real as R
open R using (ℝ; _≃_; _≤_; _+_; _-_; _*_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopOriginalMachinAtanSmallPhaseExact as Bounds
import DASHI.Analysis.BishopMachinZetaSequentialContinuityReducerExact as Eps
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as L
import DASHI.Physics.Closure.NSTriadKNPhysicalRetainedSector as Cut
import DASHI.Moonshine.JInvariantPuncturedLatticeSquareShellExact as S
import DASHI.Moonshine.JInvariantBishopPuncturedShellFiniteFoldExact as F
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as K
import DASHI.Moonshine.JInvariantBishopSquareExhaustionExact as Ex
import DASHI.Moonshine.JInvariantBishopSquareShellReindexExact as Re
import DASHI.Moonshine.JInvariantBishopCofinalSquareSandwichExact as Co

horizontalOK : Nat → L.LatticePoint → Bool
horizontalOK n p = Cut.coordinateInCutoff? n (L.horizontal p)

rectangle : Nat → Nat → List L.LatticePoint
rectangle n m = filterᵇ (horizontalOK n) (S.squarePoints (n ⊔ m))

rectUnique : ∀ n m → Unique (rectangle n m)
rectUnique n m = UniqueP.filter⁺ (T? ∘ horizontalOK n) (S.squarePointsUnique (n ⊔ m))

inner : ∀ n m {p} → p ∈ S.squarePoints n → p ∈ rectangle n m
inner n m {p} h = ∈-filter⁺ (T? ∘ horizontalOK n)
  (Ex.squareSubset n (n ⊔ m) (NP.m≤m⊔n n m) h)
  (proj₁ (Equivalence.to T-∧ (Re.squareSound n p h)))

outer : ∀ n m {p} → p ∈ rectangle n m → p ∈ S.squarePoints (n ⊔ m)
outer n m h = proj₁ (∈-filter⁻ (T? ∘ horizontalOK n) {xs = S.squarePoints (n ⊔ m)} h)

module At
  (f : K.NonzeroLatticePoint → ℝ) (respect : Re.PointRespect f)
  (v a : ℝ)
  (shell : Seq._ConvergesTo_ (Seq.SeriesOf (λ k → F.shellComponent k f)) v)
  (absolute : Seq._ConvergesTo_ (Seq.SeriesOf (λ k → F.shellAbsolute k f)) a)
  where
  rect : Nat → Nat → ℝ
  rect n m = Re.sum (Ex.raw f) (rectangle n m)

  module Along (height : Nat → Nat) = Co.Cofinal f respect v a shell absolute
    (λ n → rectangle n (height n)) (λ n → n ⊔ height n)
    (λ n → rectUnique n (height n)) (λ n → inner n (height n))
    (λ n → outer n (height n)) (λ n → NP.m≤m⊔n n (height n))

  rectangleConverges : ∀ height → Seq._ConvergesTo_ (λ n → rect n (height n)) v
  rectangleConverges height = Along.converges height

  -- Once the finite sum of actual row limits is attached, no further
  -- interchange theorem is needed. Its modulus chooses the vertical
  -- radius; every such choice is already covered by rectangleConverges.
  iterated : (rows : Nat → ℝ) →
    (∀ n → Seq._ConvergesTo_ (rect n) (rows n)) →
    Seq._ConvergesTo_ rows v
  iterated rows rowConv = Seq.con* λ { (suc k) →
    let eps = (+ 1 / suc k) ⋆
        delta = ((+ 1 / 4) ⋆) * eps
        dp = P.posx,y⇒posx*y (Eps.reciprocalNatPositive 3) (Eps.reciprocalNatPositive k)
        -- Selection depends on precision and horizontal prefix, not on
        -- an assumed value of the infinite lattice series.
        moduli = λ n → Seq.fast-ε-from-convergence (rows n , rowConv n) delta dp
        height = λ n → proj₁ (moduli n)
        both = Seq.fast-ε-from-convergence (v , rectangleConverges height) delta dp
    in proj₁ both , λ n past →
      let h1 = P.<⇒≤ (proj₂ (moduli n) (height n) NP.≤-refl)
          h2 = P.<⇒≤ (proj₂ both n (NP.≤-trans (NP.n≤1+n (proj₁ both)) past))
          signed1 = P.≤-respˡ-≃ (P.∣x-y∣≃∣y-x∣ (rows n) (rect n (height n))) h1
          total = P.≤-respˡ-≃ (P.∣-∣-cong (let open P.ℝ-Solver in solve 3
            (λ x y z → x ⊖ z ⊜ (x ⊖ y) ⊕ (y ⊖ z))
            P.≃-refl (rows n) (rect n (height n)) v))
            (Bounds.boundAdd signed1 h2)
          budget = P.≤-respˡ-≃ (let open P.ℝ-Solver in solve 1
            (λ e → (Κ (+ 1 / 4) ⊗ e) ⊕ (Κ (+ 1 / 4) ⊗ e) ⊜ Κ (+ 1 / 2) ⊗ e)
            P.≃-refl eps)
            (P.≤-respʳ-≃ (P.*-identityˡ eps)
              (P.*-monoʳ-≤-nonNeg
                (P.p≤q⇒p⋆≤q⋆ (+ 1 / 2) (+ 1 / 1)
                  (toWitness {a? = QP._≤?_ (+ 1 / 2) (+ 1 / 1)} _))
                (P.pos⇒nonNeg (Eps.reciprocalNatPositive k))))
      in P.≤-trans total budget }
