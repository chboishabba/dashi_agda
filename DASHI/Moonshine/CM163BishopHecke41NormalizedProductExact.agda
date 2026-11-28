module DASHI.Moonshine.CM163BishopHecke41NormalizedProductExact where

-- SOURCE-WRITTEN, kernel pending. Assemble the actual 42 guarded
-- chart factors with their original cusp-normalization powers.
-- No cancellation of j, j-K, or a branch difference.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin as Fin using (Fin)
import Data.Fin.Properties as FP
import Data.Nat.Properties as NP
open import Relation.Binary.PropositionalEquality using (cong)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
open import Data.Product.Base using (_,_)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Moonshine.JInvariantBishopRamanujanDeltaNonvanishingExact as Global
import DASHI.Moonshine.JInvariantBishopRamanujanComplexReadoutExact as Read
import DASHI.Moonshine.JInvariantBishopRamanujanDeltaUnitExact as Unit
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as Power
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as Gen
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as Radius
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.CM163BishopHecke41AnalyticChartsExact as Chart
import DASHI.Moonshine.CM163BishopHecke41ProductExact as H
import DASHI.Moonshine.CM163BishopHecke41RamifiedPhaseExact as Ram
import DASHI.Moonshine.CM163BishopHeckeProductAlgebraExact as Alg
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_*C_; _-C_; powC)
open Comp using (complexTrans; complexSym)

finiteChart : ∀ (i : Fin 41) p → Chart.chartPoint (Fin.inject₁ i) p ≡ Chart.finitePoint (Fin.toℕ i) p
finiteChart i p rewrite FP.toℕ-inject₁ i with Fin.toℕ i NP.≟ 41
... | yes eq = ⊥-elim (NP.<-irrefl eq (FP.toℕ<n i))
... | no _ = refl

infinityChart : ∀ p → Chart.chartPoint (Fin.fromℕ 41) p ≡ Chart.infinityPoint p
infinityChart p rewrite FP.toℕ-fromℕ 41 with 41 NP.≟ 41
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)

eqValue : ∀ {X : Set} (f : X → BishopComplex) {x y} → x ≡ y → f x ≈C f y
eqValue f refl = C.≈C-refl _

-- q^k times the normalized first power q*j gives q^(k+1)*j.
liftUnit : ∀ q j v k → (q *C j) ≈C v →
  (powC q (suc k) *C j) ≈C (powC q k *C v)
liftUnit q j v k h =
  complexTrans (A.mulCCongruent
    (complexTrans (complexSym (Power.powAdd q 1 k))
      (complexTrans (A.mulCCongruent (Power.powOne q) (C.≈C-refl _))
        (L.complexMultiplyCommutative q (powC q k)))) (C.≈C-refl j))
    (complexTrans (L.complexMultiplyAssociative (powC q k) q j)
      (A.mulCCongruent (C.≈C-refl _) h))

module At (inputs : Round11.BishopCutset) where
  module Rm = Ram.At inputs
  module G = Global.At inputs
  module Ph = Rm.Ph
  open G using (j)

  q = Ph.q
  t = Rm.t

  junit : ∀ p → Read.Readout (q p) Unit.Junit
  junit p = Global.AtDisk.Jread (q p) (Radius.machinQRadius (C.im (U.tau p))) (Ph.disk p)

  Jvalue : U.BishopUpperHalfPlanePoint → BishopComplex
  Jvalue p = Read.value (junit p)

  qj : ∀ p → (q p *C j p) ≈C Jvalue p
  qj p = Global.AtDisk.actualJ (q p) (Radius.machinQRadius (C.im (U.tau p)))
    (Ph.disk p) (G.qNonzero p)

  fin : Fin 41 → U.BishopUpperHalfPlanePoint → U.BishopUpperHalfPlanePoint
  fin i p = Chart.finitePoint (Fin.toℕ i) p

  inf = Chart.infinityPoint

  finiteFactors : ∀ p y → Fin 41 → BishopComplex
  finiteFactors p y i = y -C j (fin i p)

  infinityFactor : ∀ p y → BishopComplex
  infinityFactor p y = y -C j (inf p)

  split : ∀ p y → G.product p y ≈C
    (H.product (finiteFactors p y) *C infinityFactor p y)
  split p y = complexTrans (Alg.prodLast (λ i → y -C j (Chart.chartPoint i p)))
    (A.mulCCongruent (H.productCong _ _ (λ i → A.subCCongruent (C.≈C-refl _)
      (eqValue j (finiteChart i p))))
      (A.subCCongruent (C.≈C-refl _) (eqValue j (infinityChart p))))

  -- Actual normalized factors; their phase is not discarded.
  dFinite : ∀ p → Fin 41 → BishopComplex
  dFinite p i = Jvalue p -C (powC (q (fin i p)) 40 *C Jvalue (fin i p))

  dInfinity : ∀ p → BishopComplex
  dInfinity p = (powC (q p) 40 *C Jvalue p) -C Jvalue (inf p)

  dFiniteLaw : ∀ p i → (q p *C finiteFactors p (j p) i) ≈C dFinite p i
  dFiniteLaw p i = complexTrans (Alg.mulSub (q p) (j p) (j (fin i p)))
    (A.subCCongruent (qj p)
      (complexTrans (A.mulCCongruent (complexSym (Rm.finitePower (Fin.toℕ i) p)) (C.≈C-refl _))
        (liftUnit (q (fin i p)) (j (fin i p)) (Jvalue (fin i p)) 40 (qj (fin i p)))))

  dInfinityLaw : ∀ p → (powC (q p) 41 *C infinityFactor p (j p)) ≈C dInfinity p
  dInfinityLaw p = complexTrans (Alg.mulSub (powC (q p) 41) (j p) (j (inf p)))
    (A.subCCongruent (liftUnit (q p) (j p) (Jvalue p) 40 (qj p))
      (complexTrans (A.mulCCongruent (complexSym (Rm.infinityQ p)) (C.≈C-refl _)) (qj (inf p))))

  dFiniteProduct : ∀ p → (powC (q p) 41 *C H.product (finiteFactors p (j p))) ≈C H.product (dFinite p)
  dFiniteProduct p = complexTrans
    (A.mulCCongruent (complexSym (Alg.prodConstant 41 (q p))) (C.≈C-refl _))
    (complexTrans (complexSym (Alg.prodMul (λ _ → q p) (finiteFactors p (j p))))
      (H.productCong _ _ (dFiniteLaw p)))

  diagonalNormalized : U.BishopUpperHalfPlanePoint → BishopComplex
  diagonalNormalized p = H.product (dFinite p) *C dInfinity p

  diagonalQ : ∀ p → (powC (q p) 82 *C G.diagonal p) ≈C diagonalNormalized p
  diagonalQ p = complexTrans (A.mulCCongruent (complexSym (Power.powAdd (q p) 41 41)) (split p (j p)))
    (complexTrans (Alg.shuffle (powC (q p) 41) (powC (q p) 41)
      (H.product (finiteFactors p (j p))) (infinityFactor p (j p)))
      (A.mulCCongruent (dFiniteProduct p) (dInfinityLaw p)))

  diagonalT : ∀ p → (powC (t p) 3362 *C G.diagonal p) ≈C diagonalNormalized p
  diagonalT p = complexTrans (A.mulCCongruent
    (complexTrans (complexSym (Ram.powPow (t p) 41 82))
      (A.powCCongruent (Rm.tPower p) 82)) (C.≈C-refl _)) (diagonalQ p)

  sFinite : ∀ p y → Fin 41 → BishopComplex
  sFinite p y i = Jvalue (fin i p) -C (q (fin i p) *C y)

  sInfinity : ∀ p y → BishopComplex
  sInfinity p y = Jvalue (inf p) -C (q (inf p) *C y)

  sFiniteLaw : ∀ p y i →
    ((Gen.minusOneC *C q (fin i p)) *C finiteFactors p y i) ≈C sFinite p y i
  sFiniteLaw p y i = complexTrans (Alg.negativeFactor (q (fin i p)) y (j (fin i p)))
    (A.subCCongruent (qj (fin i p)) (C.≈C-refl _))

  sInfinityLaw : ∀ p y →
    ((Gen.minusOneC *C powC (q p) 41) *C infinityFactor p y) ≈C sInfinity p y
  sInfinityLaw p y = complexTrans (Alg.negativeFactor (powC (q p) 41) y (j (inf p)))
    (A.subCCongruent
      (complexTrans (A.mulCCongruent (complexSym (Rm.infinityQ p)) (C.≈C-refl _)) (qj (inf p)))
      (A.mulCCongruent (complexSym (Rm.infinityQ p)) (C.≈C-refl _)))

  finiteQProduct : ∀ p → H.product (λ i → q (fin i p)) ≈C q p
  finiteQProduct p = complexTrans (H.productCong _ _ (λ i → Rm.finiteQ (Fin.toℕ i) p))
    (complexTrans (Alg.prodMul (λ i → powC Rm.zeta (Fin.toℕ i)) (λ _ → t p))
      (complexTrans (A.mulCCongruent (Alg.phaseProduct Rm.zeta Rm.phaseOrder) (Alg.prodConstant 41 (t p)))
        (complexTrans (L.complexMultiplyLeftIdentity _) (Rm.tPower p))))

  negativeQProduct : ∀ p → H.product {41} (λ i → Gen.minusOneC *C q (fin i p)) ≈C (Gen.minusOneC *C q p)
  negativeQProduct p = complexTrans (Alg.prodMul (λ _ → Gen.minusOneC) (λ i → q (fin i p)))
    (A.mulCCongruent (complexTrans (Alg.prodConstant 41 Gen.minusOneC) Alg.minus41) (finiteQProduct p))

  sFiniteProduct : ∀ p y → ((Gen.minusOneC *C q p) *C H.product (finiteFactors p y)) ≈C H.product (sFinite p y)
  sFiniteProduct p y = complexTrans (A.mulCCongruent (complexSym (negativeQProduct p)) (C.≈C-refl _))
    (complexTrans (complexSym (Alg.prodMul (λ i → Gen.minusOneC *C q (fin i p)) (finiteFactors p y)))
      (H.productCong _ _ (sFiniteLaw p y)))

  sliceNormalized : ∀ p y → BishopComplex
  sliceNormalized p y = H.product (sFinite p y) *C sInfinity p y

  sliceQ : ∀ p y → (powC (q p) 42 *C G.product p y) ≈C sliceNormalized p y
  sliceQ p y = complexTrans
    (A.mulCCongruent
      (complexTrans (complexSym (Power.powAdd (q p) 1 41))
        (complexTrans (A.mulCCongruent (Power.powOne (q p)) (C.≈C-refl _))
          (complexSym (Alg.minusProduct (q p) (powC (q p) 41))))) (split p y))
    (complexTrans (Alg.shuffle (Gen.minusOneC *C q p) (Gen.minusOneC *C powC (q p) 41)
      (H.product (finiteFactors p y)) (infinityFactor p y))
      (A.mulCCongruent (sFiniteProduct p y) (sInfinityLaw p y)))

  sliceT : ∀ p y → (powC (t p) 1722 *C G.product p y) ≈C sliceNormalized p y
  sliceT p y = complexTrans (A.mulCCongruent
    (complexTrans (complexSym (Ram.powPow (t p) 41 42))
      (A.powCCongruent (Rm.tPower p) 42)) (C.≈C-refl _)) (sliceQ p y)
