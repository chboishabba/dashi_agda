module DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact where

-- SOURCE-WRITTEN, kernel pending. The actual complex Cauchy row is
-- the original real formal ring in two Cartesian components.
-- Rotation is an endomorphism of that row. The cyclic norm is
-- invariant by an explicit first/last factor rotation.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin as Fin using (Fin; toℕ)
import Data.Fin.Properties as FP
import Data.Nat.Base as Nat
import Data.Nat.Properties as NP
open import Data.Nat.DivMod using (_%_)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Real as R
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopSignTwistedFiniteCauchyCoefficientExact as T
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopThetaCauchyProductExact as CP
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as Power
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as Gen
import DASHI.Moonshine.CM163BishopHeckeProductAlgebraExact as Alg
import DASHI.Moonshine.CM163BishopHecke41RamifiedPhaseExact as Ram
import DASHI.Moonshine.CM163BishopHecke41SectorFilterExact as Filter
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_*C_; _+C_; _-C_; powC)
open Comp using (complexTrans; complexSym)

SeriesC : Set
SeriesC = Nat → BishopComplex

infix 4 _≈cs_
_≈cs_ : SeriesC → SeriesC → Set
f ≈cs g = ∀ n → f n ≈C g n

reflCs : ∀ {f} → f ≈cs f
reflCs n = C.≈C-refl _
symCs : ∀ {f g} → f ≈cs g → g ≈cs f
symCs h n = complexSym (h n)
transCs : ∀ {f g h} → f ≈cs g → g ≈cs h → f ≈cs h
transCs p q n = complexTrans (p n) (q n)

infixl 7 _⊗c_
_⊗c_ : SeriesC → SeriesC → SeriesC
_⊗c_ = CP.complexRow

unit : SeriesC
unit zero = A.oneC
unit (suc n) = A.zeroC

sumC : ∀ {n} → (Fin n → BishopComplex) → BishopComplex
sumC f = C.complex (Row.BishopSum.sum (λ i → C.re (f i))) (Row.BishopSum.sum (λ i → C.im (f i)))

sumCong : ∀ {n} (f g : Fin n → BishopComplex) → (∀ i → f i ≈C g i) → sumC f ≈C sumC g
sumCong f g h = Row.BishopSum.sum-cong-≋ (λ i → proj₁ (h i)) ,
  Row.BishopSum.sum-cong-≋ (λ i → proj₂ (h i))

sumMul : ∀ {n} (f : Fin n → BishopComplex) z →
  sumC (λ i → f i *C z) ≈C (sumC f *C z)
sumMul {zero} f z = complexSym (L.complexMultiplyLeftZero z)
sumMul {suc n} f z = complexTrans (A.addCCongruent (C.≈C-refl _) (sumMul (λ i → f (Fin.suc i)) z))
  (complexSym (L.complexMultiplyDistributesRight (f Fin.zero) (sumC (λ i → f (Fin.suc i))) z))

rowRead : ∀ f g n → (f ⊗c g) n ≈C
  sumC (λ (i : Fin (suc n)) → f (toℕ i) *C g (n Nat.∸ toℕ i))
rowRead f g n =
  P.≃-symm (CP.sumSub (suc n) (λ i → R._*_ (C.re (f (toℕ i))) (C.re (g (n Nat.∸ toℕ i))))
    (λ i → R._*_ (C.im (f (toℕ i))) (C.im (g (n Nat.∸ toℕ i))))) ,
  P.≃-symm (Row.BishopSum.∑-distrib-+
    (λ i → R._*_ (C.re (f (toℕ i))) (C.im (g (n Nat.∸ toℕ i))))
    (λ i → R._*_ (C.im (f (toℕ i))) (C.re (g (n Nat.∸ toℕ i)))))

mulCong : ∀ {f g a b} → f ≈cs a → g ≈cs b → (f ⊗c g) ≈cs (a ⊗c b)
mulCong {f} {g} {a} {b} h k n = complexTrans (rowRead f g n)
  (complexTrans (sumCong _ _ (λ i → A.mulCCongruent (h (toℕ i)) (k (n Nat.∸ toℕ i))))
    (complexSym (rowRead a b n)))

mulComm : ∀ a b → (a ⊗c b) ≈cs (b ⊗c a)
mulComm a b n =
  (let open G.Solver in solve 4
    (λ ar ai br bi → ((ar ⊗ br) ⊖ (ai ⊗ bi)) ⊜ ((br ⊗ ar) ⊖ (bi ⊗ ai)))
    G.reflS (C.realTerms a) (C.imagTerms a) (C.realTerms b) (C.imagTerms b) n) ,
  (let open G.Solver in solve 4
    (λ ar ai br bi → ((ar ⊗ bi) ⊕ (ai ⊗ br)) ⊜ ((br ⊗ ai) ⊕ (bi ⊗ ar)))
    G.reflS (C.realTerms a) (C.imagTerms a) (C.realTerms b) (C.imagTerms b) n)

mulAssoc : ∀ a b c → ((a ⊗c b) ⊗c c) ≈cs (a ⊗c (b ⊗c c))
mulAssoc a b c n =
  (let open G.Solver in solve 6
    (λ ar ai br bi cr ci → ((((ar ⊗ br) ⊖ (ai ⊗ bi)) ⊗ cr) ⊖ (((ar ⊗ bi) ⊕ (ai ⊗ br)) ⊗ ci)) ⊜ ((ar ⊗ ((br ⊗ cr) ⊖ (bi ⊗ ci))) ⊖ (ai ⊗ ((br ⊗ ci) ⊕ (bi ⊗ cr)))))
    G.reflS (C.realTerms a) (C.imagTerms a) (C.realTerms b) (C.imagTerms b) (C.realTerms c) (C.imagTerms c) n) ,
  (let open G.Solver in solve 6
    (λ ar ai br bi cr ci → ((((ar ⊗ br) ⊖ (ai ⊗ bi)) ⊗ ci) ⊕ (((ar ⊗ bi) ⊕ (ai ⊗ br)) ⊗ cr)) ⊜ ((ar ⊗ ((br ⊗ ci) ⊕ (bi ⊗ cr))) ⊕ (ai ⊗ ((br ⊗ cr) ⊖ (bi ⊗ ci)))))
    G.reflS (C.realTerms a) (C.imagTerms a) (C.realTerms b) (C.imagTerms b) (C.realTerms c) (C.imagTerms c) n)

mulUnitLeft : ∀ a → (unit ⊗c a) ≈cs a
mulUnitLeft a n =
  (let open G.Solver in solve 2
    (λ ar ai → ((Κ 1ℚᵘ ⊗ ar) ⊖ (Κ 0ℚᵘ ⊗ ai)) ⊜ ar)
    G.reflS (C.realTerms a) (C.imagTerms a) n) ,
  (let open G.Solver in solve 2
    (λ ar ai → ((Κ 1ℚᵘ ⊗ ai) ⊕ (Κ 0ℚᵘ ⊗ ar)) ⊜ ai)
    G.reflS (C.realTerms a) (C.imagTerms a) n)

mulUnitRight : ∀ a → (a ⊗c unit) ≈cs a
mulUnitRight a n =
  (let open G.Solver in solve 2
    (λ ar ai → ((ar ⊗ Κ 1ℚᵘ) ⊖ (ai ⊗ Κ 0ℚᵘ)) ⊜ ar)
    G.reflS (C.realTerms a) (C.imagTerms a) n) ,
  (let open G.Solver in solve 2
    (λ ar ai → ((ar ⊗ Κ 0ℚᵘ) ⊕ (ai ⊗ Κ 1ℚᵘ)) ⊜ ai)
    G.reflS (C.realTerms a) (C.imagTerms a) n)

twist : BishopComplex → SeriesC → SeriesC
twist w f n = f n *C powC w n

twistCong : ∀ w {f g} → f ≈cs g → twist w f ≈cs twist w g
twistCong w h n = A.mulCCongruent (h n) (C.≈C-refl _)

twistPhaseCong : ∀ {w v} → w ≈C v → ∀ f → twist w f ≈cs twist v f
twistPhaseCong h f n = A.mulCCongruent (C.≈C-refl _) (A.powCCongruent h n)

twistOne : ∀ f → twist A.oneC f ≈cs f
twistOne f n = complexTrans (A.mulCCongruent (C.≈C-refl _) (Power.powUnit n))
  (L.complexMultiplyRightIdentity (f n))

twistUnit : ∀ w → twist w unit ≈cs unit
twistUnit w zero = L.complexMultiplyRightIdentity A.oneC
twistUnit w (suc n) = L.complexMultiplyLeftZero _

twistCompose : ∀ w v f → twist w (twist v f) ≈cs twist (v *C w) f
twistCompose w v f n =
  complexTrans (L.complexMultiplyAssociative (f n) (powC v n) (powC w n))
    (A.mulCCongruent (C.≈C-refl _) (complexSym (Gen.powProduct v w n)))

twistMul : ∀ w f g → (twist w f ⊗c twist w g) ≈cs twist w (f ⊗c g)
twistMul w f g n =
  let j = λ (i : Fin (suc n)) → n Nat.∸ toℕ i
      a = λ (i : Fin (suc n)) → f (toℕ i) *C g (j i)
      point : ∀ i → (twist w f (toℕ i) *C twist w g (j i)) ≈C (a i *C powC w n)
      point i = complexTrans (Alg.shuffle (f (toℕ i)) (powC w (toℕ i)) (g (j i)) (powC w (j i)))
        (A.mulCCongruent (C.≈C-refl _)
          (complexTrans (Power.powAdd w (toℕ i) (j i))
            (Filter.powIndex w (T.indexPlusTruncatedComplement n (toℕ i) (FP.toℕ≤pred[n] i)))))
  in complexTrans (rowRead (twist w f) (twist w g) n)
    (complexTrans (sumCong _ _ point)
      (complexTrans (sumMul a (powC w n))
        (A.mulCCongruent (complexSym (rowRead f g n)) (C.≈C-refl _))))

module At (inputs : Round11.BishopCutset) where
  module Rm = Ram.At inputs
  module S = Filter.At inputs
  zeta = Rm.zeta

  factor : SeriesC → Nat → SeriesC
  factor f k = twist (powC zeta k) f

  rotateFactor : ∀ f k → twist zeta (factor f k) ≈cs factor f (suc k)
  rotateFactor f k = transCs (twistCompose zeta (powC zeta k) f)
    (twistPhaseCong (L.complexMultiplyCommutative (powC zeta k) zeta) f)

  normFrom : SeriesC → Nat → Nat → SeriesC
  normFrom f k zero = unit
  normFrom f k (suc n) = factor f k ⊗c normFrom f (suc k) n

  rotateFrom : ∀ f k n → twist zeta (normFrom f k n) ≈cs normFrom f (suc k) n
  rotateFrom f k zero = twistUnit zeta
  rotateFrom f k (suc n) =
    transCs (symCs (twistMul zeta (factor f k) (normFrom f (suc k) n)))
      (mulCong (rotateFactor f k) (rotateFrom f (suc k) n))

  snoc : ∀ f k n → normFrom f k (suc n) ≈cs (normFrom f k n ⊗c factor f (k + n))
  snoc f k zero =
    transCs (mulUnitRight (factor f k))
      (transCs (twistPhaseCong (Filter.powIndex zeta (sym (NP.+-identityʳ k))) f)
        (symCs (mulUnitLeft (factor f (k + zero)))))
  snoc f k (suc n) =
    transCs (mulCong reflCs (snoc f (suc k) n))
      (transCs (symCs (mulAssoc (factor f k) (normFrom f (suc k) n) (factor f (suc k + n))))
        (mulCong reflCs (twistPhaseCong (Filter.powIndex zeta (sym (NP.+-suc k n))) f)))

  norm : SeriesC → SeriesC
  norm f = normFrom f zero 41

  factorWrap : ∀ f → factor f 41 ≈cs factor f zero
  factorWrap f = twistPhaseCong Rm.phaseOrder f

  rotateNorm : ∀ f → twist zeta (norm f) ≈cs norm f
  rotateNorm f =
    transCs (rotateFrom f zero 41)
      (transCs (snoc f 1 40)
        (transCs (mulCong reflCs (factorWrap f))
          (mulComm (normFrom f 1 40) (factor f zero))))

  covariance : ∀ f n → (powC zeta n *C norm f n) ≈C norm f n
  covariance f n = complexTrans (L.complexMultiplyCommutative (powC zeta n) (norm f n)) (rotateNorm f n)

  offSector : ∀ f n → (n % 41 ≡ zero → ⊥) → norm f n ≈C A.zeroC
  offSector f n hn = S.offSectorZero n (norm f n) hn (covariance f n)
