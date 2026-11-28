module DASHI.Moonshine.JInvariantBishopShearExhaustionExact where

-- Actual T shear and its inverse, on the original signed lattice.
-- Use a cofinal 2n square, sandwich its image between n and 4n,
-- and take the same absolute tail to zero. No unbounded sum interface.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool.Base using (T)
open import Data.Bool.Properties using (T-∧)
open import Data.Integer.Base as Z using (+_)
import Data.Integer.Properties as ZP
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)
import Data.Nat.Properties as NP
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopVanishingDifferenceConvergenceExact as V
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Moonshine.JInvariantBishopSquareExhaustionExact as X
import DASHI.Moonshine.JInvariantBishopSquareShellReindexExact as Re
import DASHI.Moonshine.JInvariantPuncturedLatticeSquareShellExact as S
import DASHI.Moonshine.JInvariantBishopPuncturedShellFiniteFoldExact as F
import DASHI.Moonshine.JInvariantBishopPuncturedShellSummabilityExact as Sum
import DASHI.Moonshine.JInvariantBishopLatticeEvenPowerShellMajorantExact as E
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as K
import DASHI.Moonshine.CM163ClassicalHecke41GeneratorTransportExact as H
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as L
import DASHI.Physics.Closure.NSTriadKNPhysicalRetainedSector as Cut

twice : Nat → Nat
twice n = n + n

shear unshear : L.LatticePoint → L.LatticePoint
shear (L.lattice-point m k) = L.lattice-point m (m Z.+ k)
unshear (L.lattice-point m k) = L.lattice-point m (k Z.- m)

unshearShear : ∀ p → unshear (shear p) ≡ p
unshearShear (L.lattice-point m k) = L.lattice-ext refl
  (let open +-*-Solver in solve 2 (λ m k → (m :+ k) :- m := k) refl m k)

shearUnshear : ∀ p → shear (unshear p) ≡ p
shearUnshear (L.lattice-point m k) = L.lattice-ext refl
  (let open +-*-Solver in solve 2 (λ m k → m :+ (k :- m) := k) refl m k)

shearInjective : ∀ {p q} → shear p ≡ shear q → p ≡ q
shearInjective {p} {q} h = trans (sym (unshearShear p)) (trans (cong unshear h) (unshearShear q))

shearIsGenerator : ∀ p → L.forwardIndex H.T p ≡ shear p
shearIsGenerator (L.lattice-point m k) = let open +-*-Solver in L.lattice-ext
  (solve 2 (λ m k → m :* Κ (+ 1) :+ k :* Κ (+ 0) := m) refl m k)
  (solve 2 (λ m k → m :* Κ (+ 1) :+ k :* Κ (+ 1) := m :+ k) refl m k)

coordinateAdd : ∀ n a b → T (Cut.coordinateInCutoff? n a) →
  T (Cut.coordinateInCutoff? n b) → T (Cut.coordinateInCutoff? (twice n) (a Z.+ b))
coordinateAdd n a b ha hb = Equivalence.from T-∧
  (ZP.≤⇒≤ᵇ lower , ZP.≤⇒≤ᵇ upper)
  where
  lower : Z.- (+ twice n) Z.≤ (a Z.+ b)
  lower = subst (λ z → z Z.≤ (a Z.+ b))
    (let open +-*-Solver in solve 1 (λ r → (:- r) :+ (:- r) := :- (r :+ r)) refl (+ n))
    (ZP.+-mono-≤ (ZP.≤ᵇ⇒≤ (proj₁ (Equivalence.to T-∧ ha)))
                 (ZP.≤ᵇ⇒≤ (proj₁ (Equivalence.to T-∧ hb))))
  upper : (a Z.+ b) Z.≤ (+ twice n)
  upper = ZP.+-mono-≤ (ZP.≤ᵇ⇒≤ (proj₂ (Equivalence.to T-∧ ha)))
                      (ZP.≤ᵇ⇒≤ (proj₂ (Equivalence.to T-∧ hb)))

shearInside : ∀ n p → T (S.insideSquare? n p) → T (S.insideSquare? (twice n) (shear p))
shearInside n (L.lattice-point m k) h = Equivalence.from T-∧
  (Cut.coordinateInCutoffMonotone n (twice n) (NP.m≤m+n n n) m (proj₁ (Equivalence.to T-∧ h)) ,
   coordinateAdd n m k (proj₁ (Equivalence.to T-∧ h)) (proj₂ (Equivalence.to T-∧ h)))

unshearInside : ∀ n p → T (S.insideSquare? n p) → T (S.insideSquare? (twice n) (unshear p))
unshearInside n (L.lattice-point m k) h = Equivalence.from T-∧
  (Cut.coordinateInCutoffMonotone n (twice n) (NP.m≤m+n n n) m (proj₁ (Equivalence.to T-∧ h)) ,
   coordinateAdd n k (Z.- m) (proj₂ (Equivalence.to T-∧ h))
     (Cut.coordinateInCutoffNeg n m (proj₁ (Equivalence.to T-∧ h))))

inner : ∀ n {p} → p ∈ S.squarePoints n → p ∈ map shear (S.squarePoints (twice n))
inner n {p} h = subst (λ q → q ∈ map shear (S.squarePoints (twice n))) (shearUnshear p)
  (∈-map⁺ shear (Re.squareMember (twice n) (unshear p) (unshearInside n p (Re.squareSound n p h))))

outer : ∀ n {p} → p ∈ map shear (S.squarePoints (twice n)) →
  p ∈ S.squarePoints (twice (twice n))
outer n {p} h with ∈-map⁻ shear {xs = S.squarePoints (twice n)} h
... | q , qm , eq = subst (λ z → z ∈ S.squarePoints (twice (twice n))) (sym eq)
  (Re.squareMember (twice (twice n)) (shear q) (shearInside (twice n) q (Re.squareSound (twice n) q qm)))

cofinal : (f : L.LatticePoint → R.ℝ) → Nat → R.ℝ
cofinal f n = Re.sum f (map shear (S.squarePoints (twice n)))

absPrefix : (f : L.LatticePoint → R.ℝ) → Nat → R.ℝ
absPrefix f n = Re.sum (λ p → R.∣ f p ∣) (S.squarePoints n)

tailBudget : (f : L.LatticePoint → R.ℝ) → Nat → R.ℝ
tailBudget f n = R._-_ (absPrefix f (twice (twice n))) (absPrefix f n)

tailBound : ∀ f n → R._≤_ (R.∣ R._-_ (cofinal f n) (Re.sum f (S.squarePoints n)) ∣) (tailBudget f n)
tailBound f n = X.sandwich f (S.squarePointsUnique n)
  (UniqueP.map⁺ shearInjective (S.squarePointsUnique (twice n)))
  (S.squarePointsUnique (twice (twice n))) (inner n) (outer n)

twiceIncreasing : ∀ n → twice n NP.< twice (suc n)
twiceIncreasing n = NP.+-mono-< (NP.n<1+n n) (NP.n<1+n n)

fourIncreasing : ∀ n → twice (twice n) NP.< twice (twice (suc n))
fourIncreasing n = NP.+-mono-< (twiceIncreasing n) (twiceIncreasing n)

fourConverges : ∀ (f : Nat → R.ℝ) v → Seq._ConvergesTo_ f v →
  Seq._ConvergesTo_ (λ n → f (twice (twice n))) v
fourConverges f v h = Seq.xₙ⊆yₙ∧yₙ→y⇒xₙ→y
  (Seq.subseq* ((λ n → twice (twice n)) , (λ n → P.≃-refl) , fourIncreasing)) (v , h)

tailConverges : ∀ f v → Seq._ConvergesTo_ (absPrefix f) v →
  Seq._ConvergesTo_ (tailBudget f) R.0ℝ
tailConverges f v h = Seq.xₙ→x∧x≃y⇒xₙ→y
  (Seq.xₙ+yₙ→x₀+y₀ (v , fourConverges (absPrefix f) v h)
    (R.- v , Seq.-xₙ→-x₀ (v , h)))
  (P.+-inverseʳ v)

-- Actual convergence, not just a finite window comparison.
cofinalConverges : ∀ f v a →
  Seq._ConvergesTo_ (λ n → Re.sum f (S.squarePoints n)) v →
  Seq._ConvergesTo_ (absPrefix f) a →
  Seq._ConvergesTo_ (cofinal f) v
cofinalConverges f v a h ha = V.vanishingDifferenceConvergence h (tailConverges f a ha)
  (λ n → P.≤-trans (tailBound f n) (P.x≤∣x∣ (tailBudget f n)))

actualCofinal : ∀ f → Re.PointRespect f → (v a : R.ℝ) →
  Seq._ConvergesTo_ (Seq.SeriesOf (λ n → F.shellComponent n f)) v →
  Seq._ConvergesTo_ (Seq.SeriesOf (λ n → F.shellAbsolute n f)) a →
  Seq._ConvergesTo_ (cofinal (X.raw f)) v
actualCofinal f respect v a h ha = cofinalConverges (X.raw f) v a
  (X.prefixConverges f respect v h) (X.absPrefixConverges f respect a ha)

module At (tau : U.BishopUpperHalfPlanePoint) where
  module Base = Sum.At tau
  real4T = actualCofinal (λ i → C.re (E.summand 4 tau i))
    (λ i j h → proj₁ (Re.summandRespect 4 tau i j h))
    (Seq.lim Base.real4) (Seq.lim Base.real4Absolute) (proj₂ Base.real4) (proj₂ Base.real4Absolute)
  imag4T = actualCofinal (λ i → C.im (E.summand 4 tau i))
    (λ i j h → proj₂ (Re.summandRespect 4 tau i j h))
    (Seq.lim Base.imag4) (Seq.lim Base.imag4Absolute) (proj₂ Base.imag4) (proj₂ Base.imag4Absolute)
  real6T = actualCofinal (λ i → C.re (E.summand 6 tau i))
    (λ i j h → proj₁ (Re.summandRespect 6 tau i j h))
    (Seq.lim Base.real6) (Seq.lim Base.real6Absolute) (proj₂ Base.real6) (proj₂ Base.real6Absolute)
  imag6T = actualCofinal (λ i → C.im (E.summand 6 tau i))
    (λ i j h → proj₂ (Re.summandRespect 6 tau i j h))
    (Seq.lim Base.imag6) (Seq.lim Base.imag6Absolute) (proj₂ Base.imag6) (proj₂ Base.imag6Absolute)
