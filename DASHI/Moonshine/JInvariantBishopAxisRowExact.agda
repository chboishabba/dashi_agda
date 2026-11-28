module DASHI.Moonshine.JInvariantBishopAxisRowExact where

-- SOURCE-WRITTEN, kernel pending. At m=0 the origin is omitted and the
-- remaining two real reciprocal-power rays are the SAME even zeta series.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (ℤ; +_; -[1+_])
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong)
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Foundations.BishopCubicTranslationIteratedExact as N
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as NatRec
import DASHI.Moonshine.JInvariantBishopEvenZetaNormalizationExact as Z
import DASHI.Moonshine.JInvariantBishopEvenLatticeReflectionExact as Neg
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as G
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorModularityExact as Mod
import DASHI.Moonshine.JInvariantBishopLatticeEvenPowerShellMajorantExact as E
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as K
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopSquareShellReindexExact as Re
import DASHI.Moonshine.JInvariantBishopSymmetricRowChartExact as Chart
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Inv
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as L
import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Cube
open import Data.List.Base using (allFin)
open C using (BishopComplex; _≈C_)
open A using (_+C_; _*C_; powC)
open Comp using (complexTrans; complexSym)

axisNZ : ∀ {n} → (+ suc n) ≡ (+ zero) → L.⊥
axisNZ ()

index : Nat → K.NonzeroLatticePoint
index n = K.nonzero-lattice-point (L.lattice-point (+ zero) (+ suc n))
  (λ h → axisNZ (cong L.vertical h))

denomRead : ∀ p n → K.latticeDenominator (K.point (index n)) (U.tau p) ≈C
  Z.realC (N.natReal (suc n))
denomRead p n =
  (let open P.ℝ-Solver in solve 2 (λ x r → Κ 0ℚᵘ ⊗ x ⊕ r ⊜ r)
    P.≃-refl (C.re (U.tau p)) (N.natReal (suc n))) ,
  (let open P.ℝ-Solver in solve 1 (λ y → Κ 0ℚᵘ ⊗ y ⊕ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
    P.≃-refl (C.im (U.tau p)))

axisRecip : ∀ p n → E.reciprocal p (index n) ≈C Z.realC (Z.r n)
axisRecip p n = G.reciprocalUnique _ _ _
  (complexTrans (A.mulCCongruent (denomRead p n) (C.≈C-refl _))
    (complexTrans (Z.realMul _ _) (Z.realCong
      (P.≃-trans (P.*-comm (N.natReal (suc n)) (Z.r n))
        (NatRec.embeddedReciprocalNatCancels n)))))

rawAxis : Nat → U.BishopUpperHalfPlanePoint → ℤ → BishopComplex
rawAxis w p j = Mod.rawC (E.summand w p) (L.lattice-point (+ zero) j)

positive : ∀ w p n → rawAxis w p (+ suc n) ≈C Z.realC (Z.term w n)
positive w p n = complexTrans (Mod.rawCRead (E.summand w p) (Re.summandRespect w p) (index n))
  (complexTrans (A.powCCongruent (axisRecip p n) w) (Z.realPow (Z.r n) w))

negative : ∀ {w} → Neg.EvenWeight w → ∀ p n →
  rawAxis w p (-[1+ n ]) ≈C Z.realC (Z.term w n)
negative {w} e p n = complexTrans (Neg.rawNeg e p (K.point (index n))) (positive w p n)

axisPrefix : Nat → U.BishopUpperHalfPlanePoint → Nat → BishopComplex
axisPrefix w p n = Mod.sumC (λ i → rawAxis w p (Cube.decodeCoordinate n i))
  (allFin (Cube.coordinateCodeBound n))

zeroAxis : ∀ w p → rawAxis w p (+ zero) ≈C A.zeroC
zeroAxis w p = C.≈C-refl _

realPair : ∀ {w} → Neg.EvenWeight w → ∀ p n →
  (C.re (rawAxis w p (+ suc n)) R.+ C.re (rawAxis w p (-[1+ n ]))) R.≃
    (((+ 2 / 1) R.⋆) R.* Z.term w n)
realPair {w} e p n = P.≃-trans (P.+-cong (proj₁ (positive w p n)) (proj₁ (negative e p n)))
  (let open P.ℝ-Solver in solve 1 (λ x → x ⊕ x ⊜ Κ (+ 2 / 1) ⊗ x) P.≃-refl (Z.term w n))

imagPair : ∀ {w} → Neg.EvenWeight w → ∀ p n →
  (C.im (rawAxis w p (+ suc n)) R.+ C.im (rawAxis w p (-[1+ n ]))) R.≃ R.0ℝ
imagPair {w} e p n = P.≃-trans (P.+-cong (proj₂ (positive w p n)) (proj₂ (negative e p n)))
  (P.+-identityʳ R.0ℝ)

axisPrefixRead : ∀ {w} → Neg.EvenWeight w → ∀ p n →
  axisPrefix w p n ≈C Z.realC (((+ 2 / 1) R.⋆) R.* Seq.SeriesOf (Z.term w) n)
axisPrefixRead {w} e p n =
  P.≃-trans (Chart.codeSum (λ j → C.re (rawAxis w p j)) n)
    (P.≃-trans (Chart.positivePairRead (λ j → C.re (rawAxis w p j)) n)
      (P.≃-trans (P.+-cong (proj₁ (zeroAxis w p))
        (P.≃-trans (Z.prefixCong _ _ (realPair e p) n)
          (Z.prefixScale ((+ 2 / 1) R.⋆) (Z.term w) n))) (P.+-identityˡ _))) ,
  P.≃-trans (Chart.codeSum (λ j → C.im (rawAxis w p j)) n)
    (P.≃-trans (Chart.positivePairRead (λ j → C.im (rawAxis w p j)) n)
      (P.≃-trans (P.+-cong (proj₂ (zeroAxis w p))
        (Z.prefixCong _ (λ _ → R.0ℝ) (imagPair e p) n))
        (P.≃-trans (P.+-identityˡ _) (zeroPrefix n))))
  where
  zeroPrefix : ∀ n → Seq.SeriesOf (λ _ → R.0ℝ) n R.≃ R.0ℝ
  zeroPrefix zero = P.≃-refl
  zeroPrefix (suc n) = P.≃-trans (P.+-cong (zeroPrefix n) P.≃-refl) (P.+-identityʳ R.0ℝ)

axisValue : Nat → BishopComplex
axisValue extra = Z.realC (((+ 2 / 1) R.⋆) R.* Z.zeta extra)

axisLimit : ∀ extra → Neg.EvenWeight (suc (suc extra)) → ∀ p →
  Mod.Converges (axisPrefix (suc (suc extra)) p) (axisValue extra)
axisLimit extra e p = Mod.limitCong
  (λ n → Z.realC (((+ 2 / 1) R.⋆) R.* Seq.SeriesOf (Z.term (suc (suc extra))) n))
  (axisPrefix (suc (suc extra)) p) (axisValue extra)
  (λ n → complexSym (axisPrefixRead e p n))
  (Inv.mulR (Power.constantConverges ((+ 2 / 1) R.⋆)) (proj₂ (Z.zetaConvergent extra)) ,
   Power.constantConverges R.0ℝ)
