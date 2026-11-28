module DASHI.Moonshine.CM163BishopHecke41ProductExact where

-- Source-written, kernel pending. The original Fin42 multiplication
-- fold is invariant under the actual analytic chart permutation on its
-- proof-relevant domain. A homogeneous product also exists everywhere.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin as Fin using (Fin)
open import Data.List.Base using (List; []; _∷_; map; allFin)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-allFin)
open import Data.List.Relation.Unary.Unique.Propositional.Properties as UP using (allFin⁺; map⁺)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; subst)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as Laws
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as W
import DASHI.Moonshine.ClassicalFiniteHeckeCorrespondenceCore as Fold
import DASHI.Moonshine.CM163ClassicalHecke41GeneratorTransportExact as H
import DASHI.Moonshine.CM163BishopHecke41AnalyticChartsExact as Chart
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as J
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as G
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_*C_; _-C_)
open Comp using (complexTrans; complexSym)

product : ∀ {n} → (Fin n → BishopComplex) → BishopComplex
product = Fold.foldFin _*C_ A.oneC

productCong : ∀ {n} (f g : Fin n → BishopComplex) →
  (∀ i → f i ≈C g i) → product f ≈C product g
productCong {zero} f g h = C.≈C-refl _
productCong {suc n} f g h = A.mulCCongruent (h Fin.zero)
  (productCong (λ i → f (Fin.suc i)) (λ i → g (Fin.suc i)) (λ i → h (Fin.suc i)))

listProduct : ∀ {X : Set} → (X → BishopComplex) → List X → BishopComplex
listProduct f [] = A.oneC
listProduct f (x ∷ xs) = f x *C listProduct f xs

productMap : ∀ {X Y : Set} (f : Y → BishopComplex) (g : X → Y) xs →
  listProduct f (map g xs) ≈C listProduct (λ x → f (g x)) xs
productMap f g [] = C.≈C-refl _
productMap f g (x ∷ xs) = A.mulCCongruent (C.≈C-refl _) (productMap f g xs)

productPerm : ∀ {X : Set} (f : X → BishopComplex) {xs ys} →
  xs Perm.↭ ys → listProduct f xs ≈C listProduct f ys
productPerm f Perm.refl = C.≈C-refl _
productPerm f (Perm.prep x h) = A.mulCCongruent (C.≈C-refl _) (productPerm f h)
productPerm f (Perm.swap {ys = ys} x y h) =
  complexTrans (A.mulCCongruent (C.≈C-refl _) (A.mulCCongruent (C.≈C-refl _) (productPerm f h)))
    (complexTrans (complexSym (Laws.complexMultiplyAssociative (f x) (f y) (listProduct f ys)))
      (complexTrans (A.mulCCongruent (Laws.complexMultiplyCommutative (f x) (f y)) (C.≈C-refl _))
        (Laws.complexMultiplyAssociative (f y) (f x) (listProduct f ys))))
productPerm f (Perm.trans h k) = complexTrans (productPerm f h) (productPerm f k)

productRead : ∀ {n} (f : Fin n → BishopComplex) → product f ≈C listProduct f (allFin n)
productRead {zero} f = C.≈C-refl _
productRead {suc n} f = A.mulCCongruent (C.≈C-refl _)
  (complexTrans (productRead (λ i → f (Fin.suc i))) (complexSym (productMap f Fin.suc (allFin n))))

allFinPerm : ∀ {n} (f g : Fin n → Fin n) →
  (∀ i → g (f i) ≡ i) → (∀ i → f (g i) ≡ i) →
  map f (allFin n) Perm.↭ allFin n
allFinPerm {n} f g l r = W.uniqueMembershipEquivalenceToPermutation
  (UP.map⁺ inject (UP.allFin⁺ n)) (UP.allFin⁺ n)
  (λ {i} _ → ∈-allFin i)
  (λ {i} _ → subst (λ x → x ∈ map f (allFin n)) (r i) (∈-map⁺ f (∈-allFin (g i))))
  where
  inject : ∀ {i j} → f i ≡ f j → i ≡ j
  inject {i} {j} h = trans (sym (l i)) (trans (cong g h) (l j))

reindex : ∀ {n} (f : Fin n → BishopComplex) (g h : Fin n → Fin n) →
  (∀ i → h (g i) ≡ i) → (∀ i → g (h i) ≡ i) →
  product (λ i → f (g i)) ≈C product f
reindex {n} f g h l r = complexTrans (productRead (λ i → f (g i)))
  (complexTrans (complexSym (productMap f g (allFin n)))
    (complexTrans (productPerm f (allFinPerm g h l r)) (complexSym (productRead f))))

zeroAt : ∀ {n} (f : Fin n → BishopComplex) i → f i ≈C A.zeroC → product f ≈C A.zeroC
zeroAt {suc n} f Fin.zero h = complexTrans
  (A.mulCCongruent h (C.≈C-refl _)) (Laws.complexMultiplyLeftZero _)
zeroAt {suc n} f (Fin.suc i) h = complexTrans
  (A.mulCCongruent (C.≈C-refl _) (zeroAt (λ j → f (Fin.suc j)) i h))
  (Laws.complexMultiplyRightZero _)

differenceSelf : ∀ x → (x -C x) ≈C A.zeroC
differenceSelf (C.complex a b) = P.+-inverseʳ a , P.+-inverseʳ b

module At (inputs : Round11.BishopCutset) where
  module K = J.At inputs
  module Charts = Chart.At inputs

  AllGuards : U.BishopUpperHalfPlanePoint → Set
  AllGuards p = ∀ i → K.Guard (Chart.chartPoint i p)

  guardS : ∀ p → AllGuards p → AllGuards (G.actS p)
  guardS p nz i = Charts.sGuard i p (nz (H.sIndex i))

  guardT : ∀ p → AllGuards p → AllGuards (G.actT p)
  guardT p nz i = Charts.tGuard i p (nz (H.tIndex i))

  value : ∀ p → AllGuards p → BishopComplex → BishopComplex
  value p nz y = product (λ i → y -C K.j (Chart.chartPoint i p) (nz i))

  valueCong : ∀ p (a b : AllGuards p) {x y} → x ≈C y → value p a x ≈C value p b y
  valueCong p a b h = productCong _ _
    (λ i → A.subCCongruent h (Charts.E.jCong _ _ (C.≈C-refl _) (a i) (b i)))

  valueS : ∀ p y (a : AllGuards p) (b : AllGuards (G.actS p)) → value (G.actS p) b y ≈C value p a y
  valueS p y a b = complexTrans (productCong _ _
    (λ i → A.subCCongruent (C.≈C-refl y) (Charts.sChartJ i p (a (H.sIndex i)) (b i))))
    (reindex (λ i → y -C K.j (Chart.chartPoint i p) (a i)) H.sIndex H.sIndex H.sRoundTrip H.sRoundTrip)

  valueT : ∀ p y (a : AllGuards p) (b : AllGuards (G.actT p)) → value (G.actT p) b y ≈C value p a y
  valueT p y a b = complexTrans (productCong _ _
    (λ i → A.subCCongruent (C.≈C-refl y) (Charts.tChartJ i p (a (H.tIndex i)) (b i))))
    (reindex (λ i → y -C K.j (Chart.chartPoint i p) (a i)) H.tIndex H.tBack H.tRoundTrip H.tReverseRoundTrip)

  diagonal : ∀ p → K.Guard p → AllGuards p → BishopComplex
  diagonal p nz all = value p all (K.j p nz)

  diagonalS : ∀ p (a : K.Guard p) (b : K.Guard (G.actS p))
    (c : AllGuards p) (d : AllGuards (G.actS p)) →
    diagonal (G.actS p) b d ≈C diagonal p a c
  diagonalS p a b c d = complexTrans (valueCong _ d d (K.jS p a b))
    (valueS p (K.j p a) c d)

  diagonalT : ∀ p (a : K.Guard p) (b : K.Guard (G.actT p))
    (c : AllGuards p) (d : AllGuards (G.actT p)) →
    diagonal (G.actT p) b d ≈C diagonal p a c
  diagonalT p a b c d = complexTrans (valueCong _ d d (K.jT p a b))
    (valueT p (K.j p a) c d)

  -- No reciprocal or global guard is needed to state this homogeneous
  -- diagonal, or to prove its zero from a single fixed chart.
  factor : U.BishopUpperHalfPlanePoint → Fin 42 → BishopComplex
  factor p i = (K.N p *C K.D (Chart.chartPoint i p)) -C
    (K.D p *C K.N (Chart.chartPoint i p))

  clearedDiagonal : U.BishopUpperHalfPlanePoint → BishopComplex
  clearedDiagonal p = product (factor p)

  fixedFactor : ∀ p i (a : K.Guard p) (b : K.Guard (Chart.chartPoint i p)) →
    K.j (Chart.chartPoint i p) b ≈C K.j p a → factor p i ≈C A.zeroC
  fixedFactor p i a b h =
    let q = Chart.chartPoint i p
        j = K.j p a
        jd = K.j q b
        nd = J.clearQuot (K.N p) (K.D p) a
        nq = J.clearQuot (K.N q) (K.D q) b
        move : ∀ x y z → ((x *C y) *C z) ≈C (x *C (z *C y))
        move x y z = complexTrans (Laws.complexMultiplyAssociative x y z)
          (A.mulCCongruent (C.≈C-refl _) (Laws.complexMultiplyCommutative y z))
        cross = complexTrans (A.mulCCongruent (complexSym nd) (C.≈C-refl _))
          (complexTrans (move (K.D p) j (K.D q))
            (complexTrans (A.mulCCongruent (C.≈C-refl _) (A.mulCCongruent (C.≈C-refl _) (complexSym h)))
              (A.mulCCongruent (C.≈C-refl _) nq)))
    in complexTrans (A.subCCongruent cross (C.≈C-refl _)) (differenceSelf _)

  fixedClearedDiagonal : ∀ p i (a : K.Guard p) (b : K.Guard (Chart.chartPoint i p)) →
    K.j (Chart.chartPoint i p) b ≈C K.j p a → clearedDiagonal p ≈C A.zeroC
  fixedClearedDiagonal p i a b h = zeroAt (factor p) i (fixedFactor p i a b h)

  fixedDiagonal : ∀ p i (a : K.Guard p) (b : AllGuards p) →
    K.j (Chart.chartPoint i p) (b i) ≈C K.j p a → diagonal p a b ≈C A.zeroC
  fixedDiagonal p i a b h = zeroAt (λ k → K.j p a -C K.j (Chart.chartPoint k p) (b k)) i
    (complexTrans (A.subCCongruent (C.≈C-refl _) h) (differenceSelf _))
