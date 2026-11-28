module DASHI.Moonshine.JInvariantBishopSquareShellReindexExact where

-- Concrete S-reindex on the original square-shell exhaustion.
-- S is exactly the generator used by the degree-41 chart tables.
-- No general summation operator on divergent functions is introduced.
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (tt)
open import Data.Bool.Base using (T; not)
open import Relation.Nullary.Decidable.Core using (T?)
open import Data.Bool.Properties using (T-∧)
open import Data.Integer.Base as Z using (+_; -_)
import Data.Integer.Properties as ZP
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using
  (∈-map⁺; ∈-map⁻; ∈-filter⁺; ∈-filter⁻; ∈-allFin; ∈-cartesianProductWith⁺)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Function.Base using (_∘_)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)
import Real as R
open R using (ℝ; _≃_; _+_; _*_)
import RealProperties as P
import Sequence as Seq
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as L
import DASHI.Physics.Closure.NSTriadKNPhysicalRetainedSector as Cut
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as W
import DASHI.Moonshine.JInvariantPuncturedLatticeSquareShellExact as S
import DASHI.Moonshine.JInvariantBishopPuncturedShellFiniteFoldExact as F
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as K
import DASHI.Moonshine.JInvariantPuncturedLatticeReindexExact as Re
import DASHI.Moonshine.CM163ClassicalHecke41GeneratorTransportExact as H
import DASHI.Moonshine.JInvariantBishopLatticeEvenPowerShellMajorantExact as E
import DASHI.Moonshine.JInvariantBishopPuncturedShellSummabilityExact as Sum
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Foundations.BishopInverseSquareProductExact as Inv

squareMember : ∀ n p → T (S.insideSquare? n p) → p ∈ S.squarePoints n
squareMember n p inside with S.squareDecodeComplete n p inside
... | (i , j) , law =
  subst (λ q → q ∈ S.squarePoints n) law
    (∈-map⁺ (S.decodeSquareCode n)
      (∈-cartesianProductWith⁺ _,_ (∈-allFin i) (∈-allFin j)))

squareSound : ∀ n p → p ∈ S.squarePoints n → T (S.insideSquare? n p)
squareSound n p member with ∈-map⁻ (S.decodeSquareCode n) {xs = S.squareCodes n} member
... | code , _ , law = subst (λ q → T (S.insideSquare? n q)) (sym law)
  (S.decodeSquareCodeInSquare n code)

shellMember : ∀ n p → T (S.onSuccessorSquareShell? n p) → p ∈ S.successorSquareShell n
shellMember n p h = ∈-filter⁺ (T? ∘ S.onSuccessorSquareShell? n)
  (squareMember (suc n) p (proj₁ (Equivalence.to T-∧ h))) h

shellSound : ∀ n p → p ∈ S.successorSquareShell n → T (S.onSuccessorSquareShell? n p)
shellSound n p m = proj₂ (∈-filter⁻ (T? ∘ S.onSuccessorSquareShell? n)
  {xs = S.squarePoints (suc n)} m)

rot back : L.LatticePoint → L.LatticePoint
rot (L.lattice-point m n) = L.lattice-point n (Z.- m)
back (L.lattice-point m n) = L.lattice-point (Z.- n) m

backRot : ∀ p → back (rot p) ≡ p
backRot (L.lattice-point m n) = L.lattice-ext (ZP.neg-involutive m) refl

rotBack : ∀ p → rot (back p) ≡ p
rotBack (L.lattice-point m n) = L.lattice-ext refl (ZP.neg-involutive n)

rotInjective : ∀ {p q} → rot p ≡ rot q → p ≡ q
rotInjective {p} {q} h = trans (sym (backRot p)) (trans (cong back h) (backRot q))

rotIsGenerator : ∀ p → L.forwardIndex H.S p ≡ rot p
rotIsGenerator (L.lattice-point m n) = let open +-*-Solver in
  L.lattice-ext
    (solve 2 (λ m n → m :* Κ (+ 0) :+ n :* Κ (+ 1) := n) refl m n)
    (solve 2 (λ m n → m :* Κ (Z.- (+ 1)) :+ n :* Κ (+ 0) := :- m) refl m n)

rotInside : ∀ n p → T (S.insideSquare? n p) → T (S.insideSquare? n (rot p))
rotInside n (L.lattice-point m k) h = Equivalence.from T-∧
  (proj₂ (Equivalence.to T-∧ h) ,
   Cut.coordinateInCutoffNeg n m (proj₁ (Equivalence.to T-∧ h)))

backInside : ∀ n p → T (S.insideSquare? n p) → T (S.insideSquare? n (back p))
backInside n (L.lattice-point m k) h = Equivalence.from T-∧
  (Cut.coordinateInCutoffNeg n k (proj₂ (Equivalence.to T-∧ h)) ,
   proj₁ (Equivalence.to T-∧ h))

truthExt : (a b : Bool) → (T a → T b) → (T b → T a) → a ≡ b
truthExt true true f g = refl
truthExt false false f g = refl
truthExt true false f g with f tt
... | ()
truthExt false true f g with g tt
... | ()

rotInsideEq : ∀ n p → S.insideSquare? n (rot p) ≡ S.insideSquare? n p
rotInsideEq n p = truthExt _ _
  (λ h → subst (λ q → T (S.insideSquare? n q)) (backRot p) (backInside n (rot p) h))
  (rotInside n p)

rotShellEq : ∀ n p → S.onSuccessorSquareShell? n (rot p) ≡ S.onSuccessorSquareShell? n p
rotShellEq n p rewrite rotInsideEq (suc n) p | rotInsideEq n p = refl

squarePermutation : ∀ n → map rot (S.squarePoints n) Perm.↭ S.squarePoints n
squarePermutation n = W.uniqueMembershipEquivalenceToPermutation
  (UniqueP.map⁺ rotInjective (S.squarePointsUnique n))
  (S.squarePointsUnique n) forward backward
  where
  forward : ∀ {p} → p ∈ map rot (S.squarePoints n) → p ∈ S.squarePoints n
  forward {p} h with ∈-map⁻ rot {xs = S.squarePoints n} h
  ... | q , qm , eq = subst (λ x → x ∈ S.squarePoints n) (sym eq)
    (squareMember n (rot q) (rotInside n q (squareSound n q qm)))
  backward : ∀ {p} → p ∈ S.squarePoints n → p ∈ map rot (S.squarePoints n)
  backward {p} h = subst (λ x → x ∈ map rot (S.squarePoints n)) (rotBack p)
    (∈-map⁺ rot (squareMember n (back p) (backInside n p (squareSound n p h))))

shellPermutation : ∀ n → map rot (S.successorSquareShell n) Perm.↭ S.successorSquareShell n
shellPermutation n = W.uniqueMembershipEquivalenceToPermutation
  (UniqueP.map⁺ rotInjective (S.successorSquareShellUnique n))
  (S.successorSquareShellUnique n) forward backward
  where
  forward : ∀ {p} → p ∈ map rot (S.successorSquareShell n) → p ∈ S.successorSquareShell n
  forward {p} h with ∈-map⁻ rot {xs = S.successorSquareShell n} h
  ... | q , qm , eq = subst (λ x → x ∈ S.successorSquareShell n) (sym eq)
    (shellMember n (rot q) (subst T (sym (rotShellEq n q)) (shellSound n q qm)))
  backward : ∀ {p} → p ∈ S.successorSquareShell n → p ∈ map rot (S.successorSquareShell n)
  backward {p} h = subst (λ x → x ∈ map rot (S.successorSquareShell n)) (rotBack p)
    (∈-map⁺ rot (shellMember n (back p)
      (subst T (rotShellEq n (back p))
        (subst (λ q → T (S.onSuccessorSquareShell? n q)) (sym (rotBack p)) (shellSound n p h)))))

-- Apply the original guard only; there is no value of an inverse at the origin.
guard : (n : Nat) → (K.NonzeroLatticePoint → ℝ) → L.LatticePoint → ℝ
guard n f p with S.onSuccessorSquareShell? n p in eq
... | false = R.0ℝ
... | true = f (F.nonzero n p (subst T (sym eq) tt))

sum : ∀ {X : Set} → (X → ℝ) → List X → ℝ
sum f [] = R.0ℝ
sum f (p ∷ ps) = f p + sum f ps

foldRead : ∀ n f ps → F.fold n f ps ≃ sum (guard n f) ps
foldRead n f [] = P.≃-refl
foldRead n f (p ∷ ps) with S.onSuccessorSquareShell? n p in eq
... | false = P.≃-trans (foldRead n f ps) (P.≃-symm (P.+-identityˡ (sum (guard n f) ps)))
... | true = P.+-cong P.≃-refl (foldRead n f ps)

sumMap : ∀ {X Y : Set} (f : Y → ℝ) (g : X → Y) ps →
  sum f (map g ps) ≃ sum (λ p → f (g p)) ps
sumMap f g [] = P.≃-refl
sumMap f g (p ∷ ps) = P.+-cong P.≃-refl (sumMap f g ps)

sumCong : ∀ {X : Set} (f g : X → ℝ) ps → (∀ p → f p ≃ g p) → sum f ps ≃ sum g ps
sumCong f g [] h = P.≃-refl
sumCong f g (p ∷ ps) h = P.+-cong (h p) (sumCong f g ps h)

sumPerm : ∀ {X : Set} (f : X → ℝ) {ps qs} → ps Perm.↭ qs → sum f ps ≃ sum f qs
sumPerm f Perm.refl = P.≃-refl
sumPerm f (Perm.prep p h) = P.+-cong P.≃-refl (sumPerm f h)
sumPerm f (Perm.swap {ys = ys} p q h) =
  P.≃-trans (P.+-cong P.≃-refl (P.+-cong P.≃-refl (sumPerm f h)))
    (let open P.ℝ-Solver in solve 3
      (λ p q t → p ⊕ (q ⊕ t) ⊜ q ⊕ (p ⊕ t))
      P.≃-refl (f p) (f q) (sum f ys))
sumPerm f (Perm.trans h k) = P.≃-trans (sumPerm f h) (sumPerm f k)

PointRespect : (K.NonzeroLatticePoint → ℝ) → Set
PointRespect f = ∀ i j → K.point i ≡ K.point j → f i ≃ f j

guardRot : ∀ n f → PointRespect f → ∀ p →
  guard n (λ i → f (Re.forwardPunctured H.S i)) p ≃ guard n f (rot p)
guardRot n f respect p with S.onSuccessorSquareShell? n p in eq | S.onSuccessorSquareShell? n (rot p) in eqr | rotShellEq n p
... | false | false | refl = P.≃-refl
... | true | true | refl = respect
  (Re.forwardPunctured H.S (F.nonzero n p (subst T (sym eq) tt)))
  (F.nonzero n (rot p) (subst T (sym eqr) tt)) (rotIsGenerator p)

shellReindexS : ∀ n f → PointRespect f →
  F.shellComponent n (λ i → f (Re.forwardPunctured H.S i)) ≃ F.shellComponent n f
shellReindexS n f respect =
  let ps = S.squarePoints (suc n) in
  P.≃-trans (foldRead n _ ps)
    (P.≃-trans (sumCong _ _ ps (guardRot n f respect))
      (P.≃-trans (P.≃-symm (sumMap (guard n f) rot ps))
        (P.≃-trans (sumPerm (guard n f) (squarePermutation (suc n)))
          (P.≃-symm (foldRead n f ps)))))

-- The original reciprocal ignores which positivity proof constructed it.
reciprocalWitnessRespect : ∀ z (a b : Rec.BishopComplexNonzero z) →
  C._≈C_ (Rec.reciprocalC z a) (Rec.reciprocalC z b)
reciprocalWitnessRespect z a b =
  let h = Inv.inverseCongruentPositive (Rec.normSquarePositive a) (Rec.normSquarePositive b) P.≃-refl in
  P.*-cong h P.≃-refl , P.*-cong h P.≃-refl

summandRespect : ∀ k tau i j → K.point i ≡ K.point j →
  C._≈C_ (E.summand k tau i) (E.summand k tau j)
summandRespect k tau (K.nonzero-lattice-point p a) (K.nonzero-lattice-point .p b) refl =
  A.powCCongruent
    (reciprocalWitnessRespect (K.latticeDenominator p (U.tau tau))
      (U.upperHalfPlaneDenominatorNonzero tau (K.nonzero-lattice-point p a))
      (U.upperHalfPlaneDenominatorNonzero tau (K.nonzero-lattice-point p b))) k

partialCong : ∀ (f g : Nat → ℝ) → (∀ n → f n ≃ g n) → ∀ n →
  Seq.SeriesOf f n ≃ Seq.SeriesOf g n
partialCong f g h 0 = P.≃-refl
partialCong f g h (suc n) = P.+-cong (partialCong f g h n) (h n)

reindexConverges : ∀ f → PointRespect f →
  (v : ℝ) → Seq._ConvergesTo_ (Seq.SeriesOf (λ n → F.shellComponent n f)) v →
  Seq._ConvergesTo_ (Seq.SeriesOf (λ n → F.shellComponent n
    (λ i → f (Re.forwardPunctured H.S i)))) v
reindexConverges f respect v h =
  Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc n) → P.≃-symm (partialCong _ _ (λ k → shellReindexS k f respect) (suc n))})
    (v , h)

-- Actual four convergent components, not an abstract reindex-invariance field.
module At (tau : U.BishopUpperHalfPlanePoint) where
  module Base = Sum.At tau
  real4S = reindexConverges (λ i → C.re (E.summand 4 tau i))
    (λ i j h → proj₁ (summandRespect 4 tau i j h))
    (Seq.lim Base.real4) (proj₂ Base.real4)
  imag4S = reindexConverges (λ i → C.im (E.summand 4 tau i))
    (λ i j h → proj₂ (summandRespect 4 tau i j h))
    (Seq.lim Base.imag4) (proj₂ Base.imag4)
  real6S = reindexConverges (λ i → C.re (E.summand 6 tau i))
    (λ i j h → proj₁ (summandRespect 6 tau i j h))
    (Seq.lim Base.real6) (proj₂ Base.real6)
  imag6S = reindexConverges (λ i → C.im (E.summand 6 tau i))
    (λ i j h → proj₂ (summandRespect 6 tau i j h))
    (Seq.lim Base.imag6) (proj₂ Base.imag6)
