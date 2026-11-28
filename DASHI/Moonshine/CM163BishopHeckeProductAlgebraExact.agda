module DASHI.Moonshine.CM163BishopHeckeProductAlgebraExact where

-- SOURCE-WRITTEN, kernel pending. Original finite Hecke fold; all
-- normalization identities below are commutative ring equalities
-- with no division by a branch difference.
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Agda.Builtin.Nat as Nat
open import Data.Fin as Fin using (Fin)
import Data.Fin.Properties as FP
import Data.Nat.Properties as NP
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Moonshine.CM163BishopHecke41RamifiedPhaseExact as Ram
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
open import Data.Product.Base using (_,_)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as Gen
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as Power
import DASHI.Moonshine.CM163BishopHecke41ProductExact as H
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open C using (BishopComplex; _≈C_)
open A using (_*C_; _-C_; powC)
open Comp using (complexTrans; complexSym)

shuffle : ∀ a b c d → ((a *C b) *C (c *C d)) ≈C ((a *C c) *C (b *C d))
shuffle (C.complex ar ai) (C.complex br bi) (C.complex cr ci) (C.complex dr di) =
  (let open P.ℝ-Solver in solve 8
    (λ ar ai br bi cr ci dr di → ((((ar ⊗ br) ⊖ (ai ⊗ bi)) ⊗ ((cr ⊗ dr) ⊖ (ci ⊗ di))) ⊖ (((ar ⊗ bi) ⊕ (ai ⊗ br)) ⊗ ((cr ⊗ di) ⊕ (ci ⊗ dr)))) ⊜ ((((ar ⊗ cr) ⊖ (ai ⊗ ci)) ⊗ ((br ⊗ dr) ⊖ (bi ⊗ di))) ⊖ (((ar ⊗ ci) ⊕ (ai ⊗ cr)) ⊗ ((br ⊗ di) ⊕ (bi ⊗ dr)))))
    P.≃-refl ar ai br bi cr ci dr di) ,
  (let open P.ℝ-Solver in solve 8
    (λ ar ai br bi cr ci dr di → ((((ar ⊗ br) ⊖ (ai ⊗ bi)) ⊗ ((cr ⊗ di) ⊕ (ci ⊗ dr))) ⊕ (((ar ⊗ bi) ⊕ (ai ⊗ br)) ⊗ ((cr ⊗ dr) ⊖ (ci ⊗ di)))) ⊜ ((((ar ⊗ cr) ⊖ (ai ⊗ ci)) ⊗ ((br ⊗ di) ⊕ (bi ⊗ dr))) ⊕ (((ar ⊗ ci) ⊕ (ai ⊗ cr)) ⊗ ((br ⊗ dr) ⊖ (bi ⊗ di)))))
    P.≃-refl ar ai br bi cr ci dr di)

mulSub : ∀ a b c → (a *C (b -C c)) ≈C ((a *C b) -C (a *C c))
mulSub (C.complex ar ai) (C.complex br bi) (C.complex cr ci) =
  (let open P.ℝ-Solver in solve 6
    (λ ar ai br bi cr ci → ((ar ⊗ (br ⊖ cr)) ⊖ (ai ⊗ (bi ⊖ ci))) ⊜ (((ar ⊗ br) ⊖ (ai ⊗ bi)) ⊖ ((ar ⊗ cr) ⊖ (ai ⊗ ci))))
    P.≃-refl ar ai br bi cr ci) ,
  (let open P.ℝ-Solver in solve 6
    (λ ar ai br bi cr ci → ((ar ⊗ (bi ⊖ ci)) ⊕ (ai ⊗ (br ⊖ cr))) ⊜ (((ar ⊗ bi) ⊕ (ai ⊗ br)) ⊖ ((ar ⊗ ci) ⊕ (ai ⊗ cr))))
    P.≃-refl ar ai br bi cr ci)

negativeFactor : ∀ a b c → ((Gen.minusOneC *C a) *C (b -C c)) ≈C ((a *C c) -C (a *C b))
negativeFactor (C.complex ar ai) (C.complex br bi) (C.complex cr ci) =
  (let open P.ℝ-Solver in solve 6
    (λ ar ai br bi cr ci → (((((⊝ Κ 1ℚᵘ) ⊗ ar) ⊖ (Κ 0ℚᵘ ⊗ ai)) ⊗ (br ⊖ cr)) ⊖ ((((⊝ Κ 1ℚᵘ) ⊗ ai) ⊕ (Κ 0ℚᵘ ⊗ ar)) ⊗ (bi ⊖ ci))) ⊜ (((ar ⊗ cr) ⊖ (ai ⊗ ci)) ⊖ ((ar ⊗ br) ⊖ (ai ⊗ bi))))
    P.≃-refl ar ai br bi cr ci) ,
  (let open P.ℝ-Solver in solve 6
    (λ ar ai br bi cr ci → (((((⊝ Κ 1ℚᵘ) ⊗ ar) ⊖ (Κ 0ℚᵘ ⊗ ai)) ⊗ (bi ⊖ ci)) ⊕ ((((⊝ Κ 1ℚᵘ) ⊗ ai) ⊕ (Κ 0ℚᵘ ⊗ ar)) ⊗ (br ⊖ cr))) ⊜ (((ar ⊗ ci) ⊕ (ai ⊗ cr)) ⊖ ((ar ⊗ bi) ⊕ (ai ⊗ br))))
    P.≃-refl ar ai br bi cr ci)

minusProduct : ∀ a b → ((Gen.minusOneC *C a) *C (Gen.minusOneC *C b)) ≈C (a *C b)
minusProduct (C.complex ar ai) (C.complex br bi) =
  (let open P.ℝ-Solver in solve 4
    (λ ar ai br bi → (((((⊝ Κ 1ℚᵘ) ⊗ ar) ⊖ (Κ 0ℚᵘ ⊗ ai)) ⊗ (((⊝ Κ 1ℚᵘ) ⊗ br) ⊖ (Κ 0ℚᵘ ⊗ bi))) ⊖ ((((⊝ Κ 1ℚᵘ) ⊗ ai) ⊕ (Κ 0ℚᵘ ⊗ ar)) ⊗ (((⊝ Κ 1ℚᵘ) ⊗ bi) ⊕ (Κ 0ℚᵘ ⊗ br)))) ⊜ ((ar ⊗ br) ⊖ (ai ⊗ bi)))
    P.≃-refl ar ai br bi) ,
  (let open P.ℝ-Solver in solve 4
    (λ ar ai br bi → (((((⊝ Κ 1ℚᵘ) ⊗ ar) ⊖ (Κ 0ℚᵘ ⊗ ai)) ⊗ (((⊝ Κ 1ℚᵘ) ⊗ bi) ⊕ (Κ 0ℚᵘ ⊗ br))) ⊕ ((((⊝ Κ 1ℚᵘ) ⊗ ai) ⊕ (Κ 0ℚᵘ ⊗ ar)) ⊗ (((⊝ Κ 1ℚᵘ) ⊗ br) ⊖ (Κ 0ℚᵘ ⊗ bi)))) ⊜ ((ar ⊗ bi) ⊕ (ai ⊗ br)))
    P.≃-refl ar ai br bi)

prodMul : ∀ {n} (f g : Fin n → BishopComplex) →
  H.product (λ i → f i *C g i) ≈C (H.product f *C H.product g)
prodMul {zero} f g = complexSym (L.complexMultiplyLeftIdentity A.oneC)
prodMul {suc n} f g = complexTrans
  (A.mulCCongruent (C.≈C-refl _) (prodMul (λ i → f (Fin.suc i)) (λ i → g (Fin.suc i))))
  (shuffle (f Fin.zero) (g Fin.zero) (H.product (λ i → f (Fin.suc i)))
    (H.product (λ i → g (Fin.suc i))))

prodConstant : ∀ n a → H.product {n} (λ _ → a) ≈C powC a n
prodConstant zero a = C.≈C-refl _
prodConstant (suc n) a = A.mulCCongruent (C.≈C-refl _) (prodConstant n a)

prodLast : ∀ {n} (f : Fin (suc n) → BishopComplex) →
  H.product f ≈C (H.product (λ i → f (Fin.inject₁ i)) *C f (Fin.fromℕ n))
prodLast {zero} f = complexTrans (L.complexMultiplyRightIdentity (f Fin.zero))
  (complexSym (L.complexMultiplyLeftIdentity (f Fin.zero)))
prodLast {suc n} f =
  complexTrans (A.mulCCongruent (C.≈C-refl _) (prodLast (λ i → f (Fin.suc i))))
    (complexSym (L.complexMultiplyAssociative (f Fin.zero)
      (H.product (λ i → f (Fin.suc (Fin.inject₁ i)))) (f (Fin.fromℕ (suc n)))))

sumPowers : Nat → Nat → Nat
sumPowers zero k = zero
sumPowers (suc n) k = k Nat.+ sumPowers n (suc k)

prodPowers : ∀ n k z → H.product {n} (λ i → powC z (k Nat.+ Fin.toℕ i)) ≈C powC z (sumPowers n k)
prodPowers zero k z = C.≈C-refl _
prodPowers (suc n) k z =
  complexTrans (A.mulCCongruent (powIndex z (NP.+-identityʳ k))
    (complexTrans (H.productCong _ _
      (λ i → powIndex z (NP.+-suc k (Fin.toℕ i))))
      (prodPowers n (suc k) z)))
    (Power.powAdd z k (sumPowers n (suc k)))

-- Exact index transport, rather than extensional equality of complex values.
  where
  powIndex : ∀ z {a b} → a ≡ b → powC z a ≈C powC z b
  powIndex z refl = C.≈C-refl _

phaseProduct : ∀ z → powC z 41 ≈C A.oneC →
  H.product {41} (λ i → powC z (Fin.toℕ i)) ≈C A.oneC
phaseProduct z hz = complexTrans (prodPowers 41 zero z)
  (complexTrans (complexSym (Ram.powPow z 41 20))
    (complexTrans (A.powCCongruent hz 20) (Power.powUnit 20)))

minusEven : ∀ n → powC Gen.minusOneC (2 Nat.* n) ≈C A.oneC
minusEven n = complexTrans (powIndex Gen.minusOneC (NP.*-comm 2 n))
  (complexTrans (complexSym (Ram.powPow Gen.minusOneC 2 n))
    (complexTrans (A.powCCongruent
      (complexTrans (complexSym (Power.powTwo Gen.minusOneC)) Ram.negativeSquare) n)
      (Power.powUnit n)))
  where
  powIndex : ∀ z {a b} → a ≡ b → powC z a ≈C powC z b
  powIndex z refl = C.≈C-refl _

minus41 : powC Gen.minusOneC 41 ≈C Gen.minusOneC
minus41 = complexTrans (A.mulCCongruent (C.≈C-refl _) (minusEven 20))
  (L.complexMultiplyRightIdentity Gen.minusOneC)
