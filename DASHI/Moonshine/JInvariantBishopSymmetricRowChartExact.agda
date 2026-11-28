module DASHI.Moonshine.JInvariantBishopSymmetricRowChartExact where

-- SOURCE-WRITTEN, kernel pending. The original rectangular coordinate
-- decoder enumerates [-n,n]; the existing dyadic row enumerates [-n,n-1].
-- Retain their one endpoint discrepancy literally.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base as Z using (ℤ; +_; -[1+_]; ∣_∣)
import Data.Integer.Properties as ZP
open import Data.Nat.Base using (_≤_; _<_; z≤n; s≤s)
import Data.Nat.Properties as NP
open import Data.Bool.Base using (T)
open import Data.Bool.Properties using (T-∧)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List; []; _∷_; _++_; map; allFin)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻; ∈-allFin; ∈-++⁻)
import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs.Core as AP
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UP
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans; _≢_)
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalRetainedSector as Cut
import DASHI.Mathematics.NumberTheory.FiniteDependentPairEnumerationExact as Dep
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as W
import DASHI.Moonshine.JInvariantBishopCenteredDyadicFoldReindexExact as I
import DASHI.Moonshine.JInvariantBishopCenteredDyadicRowClosureExact as Close
import DASHI.Moonshine.JInvariantBishopSquareShellReindexExact as Re
import DASHI.Moonshine.JInvariantBishopSquareExhaustionExact as Ex
open Re using (sum)

-- Actual cutoff equivalence on both integer constructors.
cutoffMagnitude : ∀ n z → T (Cut.coordinateInCutoff? n z) → ∣ z ∣ ≤ n
cutoffMagnitude n (+ k) h with ZP.≤ᵇ⇒≤ (proj₂ (Equivalence.to T-∧ h))
... | Z.+≤+ p = p
cutoffMagnitude zero -[1+ k ] h with ZP.≤ᵇ⇒≤ (proj₁ (Equivalence.to T-∧ h))
... | ()
cutoffMagnitude (suc n) -[1+ k ] h with ZP.≤ᵇ⇒≤ (proj₁ (Equivalence.to T-∧ h))
... | Z.-≤- p = s≤s p

magnitudeCutoff : ∀ n z → ∣ z ∣ ≤ n → T (Cut.coordinateInCutoff? n z)
magnitudeCutoff zero (+ k) h = Equivalence.from T-∧
  (ZP.≤⇒≤ᵇ (Z.+≤+ z≤n) , ZP.≤⇒≤ᵇ (Z.+≤+ h))
magnitudeCutoff (suc n) (+ k) h = Equivalence.from T-∧
  (ZP.≤⇒≤ᵇ Z.-≤+ , ZP.≤⇒≤ᵇ (Z.+≤+ h))
magnitudeCutoff zero -[1+ k ] ()
magnitudeCutoff (suc n) -[1+ k ] (s≤s h) = Equivalence.from T-∧
  (ZP.≤⇒≤ᵇ (Z.-≤- h) , ZP.≤⇒≤ᵇ Z.-≤+)

symmetric : Nat → List ℤ
symmetric n = I.interval n ++ ((+ n) ∷ [])

symmetricUnique : ∀ n → Unique (symmetric n)
symmetricUnique n = Dep.uniqueAppendDisjoint (I.intervalUnique n)
  (AP._∷_ All.[] AP.[]) cross
  where
  cross : ∀ {x y} → x ∈ I.interval n → y ∈ ((+ n) ∷ []) → x ≢ y
  cross xm (Any.here refl) refl = NP.<-irrefl refl (I.intervalSound n xm)
  cross xm (Any.there ()) eq

symmetricSound : ∀ n {z} → z ∈ symmetric n → ∣ z ∣ ≤ n
symmetricSound n {+ k} h with ∈-++⁻ (I.interval n) h
... | inj₁ m = NP.<⇒≤ (I.intervalSound n m)
... | inj₂ (Any.here refl) = NP.≤-refl
... | inj₂ (Any.there ())
symmetricSound n { -[1+ k ]} h with ∈-++⁻ (I.interval n) h
... | inj₁ m = I.intervalSound n m
... | inj₂ (Any.here ())
... | inj₂ (Any.there ())

symmetricComplete : ∀ n z → ∣ z ∣ ≤ n → z ∈ symmetric n
symmetricComplete n (+ k) h with NP.m≤n⇒m<n∨m≡n h
... | inj₁ lt = Dep.appendMemberLeft (I.positiveMember n k lt)
... | inj₂ refl = Dep.appendMemberRight (I.interval n) (Any.here refl)
symmetricComplete n -[1+ k ] h = Dep.appendMemberLeft (I.negativeMember n k h)

codes : Nat → List ℤ
codes n = map (Cube.decodeCoordinate n) (allFin (Cube.coordinateCodeBound n))

codeUnique : ∀ n → Unique (codes n)
codeUnique n = UP.map⁺ (Cube.decodeCoordinateInjective n) (UP.allFin⁺ _)

codeToSymmetric : ∀ n {z} → z ∈ codes n → z ∈ symmetric n
codeToSymmetric n {z} h with ∈-map⁻ (Cube.decodeCoordinate n) h
... | i , _ , eq = subst (_∈ symmetric n) (sym eq)
  (symmetricComplete n _ (cutoffMagnitude n _ (Cut.decodeCoordinateInCutoff n i)))

symmetricToCode : ∀ n {z} → z ∈ symmetric n → z ∈ codes n
symmetricToCode n {z} h with Cut.decodeCoordinateComplete n z (magnitudeCutoff n z (symmetricSound n h))
... | i , e = subst (_∈ codes n) e (∈-map⁺ (Cube.decodeCoordinate n) (∈-allFin i))

codePermutation : ∀ n → codes n Perm.↭ symmetric n
codePermutation n = W.uniqueMembershipEquivalenceToPermutation
  (codeUnique n) (symmetricUnique n) (codeToSymmetric n) (symmetricToCode n)

codeSum : ∀ f n → sum (λ i → f (Cube.decodeCoordinate n i))
  (allFin (Cube.coordinateCodeBound n)) R.≃ sum f (symmetric n)
codeSum f n = P.≃-trans
  (P.≃-symm (Re.sumMap f (Cube.decodeCoordinate n) (allFin (Cube.coordinateCodeBound n))))
  (Re.sumPerm f (codePermutation n))

symmetricPairRead : ∀ f n →
  sum f (symmetric n) R.≃ (Seq.SeriesOf (λ k → R._+_ (f (+ k)) (f (-[1+ k ]))) n R.+ f (+ n))
symmetricPairRead f n = P.≃-trans (Ex.sumAppend f (I.interval n) ((+ n) ∷ []))
  (P.+-cong (Close.intervalRead f n) (P.+-identityʳ (f (+ n))))

-- This is also the original zero-plus-paired-positive chart, obtained
-- by a finite telescoping identity (no infinite rearrangement).
positivePairRead : ∀ f n →
  sum f (symmetric n) R.≃
    (f (+ zero) R.+ Seq.SeriesOf (λ k → f (+ suc k) R.+ f (-[1+ k ])) n)
positivePairRead f zero = P.≃-trans (P.+-identityʳ (f (+ zero))) (P.≃-symm (P.+-identityʳ (f (+ zero))))
positivePairRead f (suc n) =
  P.≃-trans (symmetricPairRead f (suc n))
    (P.≃-trans (let open P.ℝ-Solver in solve 4
      (λ a b c d → (a ⊕ (b ⊕ c)) ⊕ d ⊜ (a ⊕ b) ⊕ (d ⊕ c))
      P.≃-refl (Seq.SeriesOf (λ k → f (+ k) R.+ f (-[1+ k ])) n)
        (f (+ n)) (f (-[1+ n ])) (f (+ suc n)))
      (P.≃-trans (P.+-cong
        (P.≃-trans (P.≃-symm (symmetricPairRead f n)) (positivePairRead f n)) P.≃-refl)
        (P.+-assoc (f (+ zero)) (Seq.SeriesOf (λ k → f (+ suc k) R.+ f (-[1+ k ])) n)
          (f (+ suc n) R.+ f (-[1+ n ])))))

negInject : ∀ {x y : ℤ} → Z.- x ≡ Z.- y → x ≡ y
negInject {x} {y} h = trans (sym (ZP.neg-involutive x))
  (trans (cong Z.-_ h) (ZP.neg-involutive y))

negPermutation : ∀ n → map Z.-_ (symmetric n) Perm.↭ symmetric n
negPermutation n = W.uniqueMembershipEquivalenceToPermutation
  (UP.map⁺ negInject (symmetricUnique n)) (symmetricUnique n) forward backward
  where
  closed : ∀ {x} → x ∈ symmetric n → Z.- x ∈ symmetric n
  closed {x} h = symmetricComplete n _
    (cutoffMagnitude n _ (Cut.coordinateInCutoffNeg n x (magnitudeCutoff n x (symmetricSound n h))))
  forward : ∀ {x} → x ∈ map Z.-_ (symmetric n) → x ∈ symmetric n
  forward h with ∈-map⁻ Z.-_ h
  ... | z , zm , eq = subst (_∈ symmetric n) (sym eq) (closed zm)
  backward : ∀ {x} → x ∈ symmetric n → x ∈ map Z.-_ (symmetric n)
  backward {x} h = subst (_∈ map Z.-_ (symmetric n)) (ZP.neg-involutive x)
    (∈-map⁺ Z.-_ (closed h))

negSum : ∀ f n → sum (λ j → f (Z.- j)) (symmetric n) R.≃ sum f (symmetric n)
negSum f n = P.≃-trans (P.≃-symm (Re.sumMap f Z.-_ (symmetric n)))
  (Re.sumPerm f (negPermutation n))
