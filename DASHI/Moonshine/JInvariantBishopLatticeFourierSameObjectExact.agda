module DASHI.Moonshine.JInvariantBishopLatticeFourierSameObjectExact where

-- SOURCE-WRITTEN; kernel acceptance pending. No Fourier identification
-- or infinite interchange premise is passed to the terminal.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₂)
import Real as R
open R using (_*_; _⋆; _≃_)
import RealProperties as P
import Sequence as Seq
import Inverse as I
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Foundations.BishopCubicTranslationIteratedExact as N
import DASHI.Foundations.BishopSqrtTwoThirdsMachinConstantExact as MP
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as NatRec
import DASHI.Moonshine.JInvariantBishopAllLatticeRowsExact as Rows
import DASHI.Moonshine.JInvariantBishopLambertSeriesRegroupExact as Lam
import DASHI.Moonshine.JInvariantBishopLatticeNormalizedGeneratorsExact as Norm
import DASHI.Moonshine.JInvariantBishopEvenZetaNormalizationExact as Z
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as D
import DASHI.Moonshine.JInvariantBishopNormalizedPositiveRowExact as Pos
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as Radius
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as Disk
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesExact as E
import DASHI.Moonshine.JInvariantEisensteinBishopMajorantSeriesExact as Major
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorModularityExact as Mod
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Inv
import DASHI.Moonshine.JInvariantBishopCenteredDyadicSummandLimitExact as Leaf
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as G
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as H
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_; scaleC)
open Comp using (complexTrans; complexSym)

two = (+ 2 / 1) ⋆

limitTransport : ∀ {f v w} → v ≈C w → Mod.Converges f v → Mod.Converges f w
limitTransport (hr , hi) (cr , ci) =
  Seq.xₙ→x∧x≃y⇒xₙ→y cr hr , Seq.xₙ→x∧x≃y⇒xₙ→y ci hi

piCancel : Norm.piInverse * D.pi ≃ R.1ℝ
piCancel = P.≃-trans (P.*-comm _ _) (I.*-inverseʳ D.pi (inj₂ MP.machinPiPositive))

powerCancel : ∀ w → R.pow Norm.piInverse w * R.pow D.pi w ≃ R.1ℝ
powerCancel w = P.≃-trans (P.≃-symm (Z.powProd Norm.piInverse D.pi w))
  (P.≃-trans (Z.powCong piCancel w) (NatRec.oneToAnyNatPower w))

normalizePlus : ∀ g z x → g * (two * z) ≃ R.1ℝ →
  (Z.realC g *C (Z.realC (two * z) +C scaleC two (scaleC z x))) ≈C (A.oneC +C x)
normalizePlus g z (C.complex x y) h =
  complexTrans (Pos.realScale g _) (
    P.≃-trans (let open P.ℝ-Solver in solve 3
      (λ g z x → g ⊗ (Κ (+ 2 / 1) ⊗ z ⊕ Κ (+ 2 / 1) ⊗ (z ⊗ x))
        ⊜ (g ⊗ (Κ (+ 2 / 1) ⊗ z)) ⊗ (Κ 1ℚᵘ ⊕ x)) P.≃-refl g z x)
      (P.≃-trans (P.*-congʳ h) (P.*-identityˡ _)) ,
    P.≃-trans (let open P.ℝ-Solver in solve 3
      (λ g z y → g ⊗ (Κ 0ℚᵘ ⊕ Κ (+ 2 / 1) ⊗ (z ⊗ y))
        ⊜ (g ⊗ (Κ (+ 2 / 1) ⊗ z)) ⊗ (Κ 0ℚᵘ ⊕ y)) P.≃-refl g z y)
      (P.≃-trans (P.*-congʳ h) (P.*-identityˡ _)))

normalizeMinus : ∀ g z x → g * (two * z) ≃ R.1ℝ →
  (Z.realC g *C (Z.realC (two * z) +C scaleC two (scaleC (R.- z) x))) ≈C (A.oneC -C x)
normalizeMinus g z (C.complex x y) h =
  complexTrans (Pos.realScale g _) (
    P.≃-trans (let open P.ℝ-Solver in solve 3
      (λ g z x → g ⊗ (Κ (+ 2 / 1) ⊗ z ⊕ Κ (+ 2 / 1) ⊗ ((⊝ z) ⊗ x))
        ⊜ (g ⊗ (Κ (+ 2 / 1) ⊗ z)) ⊗ (Κ 1ℚᵘ ⊖ x)) P.≃-refl g z x)
      (P.≃-trans (P.*-congʳ h) (P.*-identityˡ _)) ,
    P.≃-trans (let open P.ℝ-Solver in solve 3
      (λ g z y → g ⊗ (Κ 0ℚᵘ ⊕ Κ (+ 2 / 1) ⊗ ((⊝ z) ⊗ y))
        ⊜ (g ⊗ (Κ (+ 2 / 1) ⊗ z)) ⊗ (Κ 0ℚᵘ ⊖ y)) P.≃-refl g z y)
      (P.≃-trans (P.*-congʳ h) (P.*-identityˡ _)))

module At (inputs : Round11.BishopCutset) (p : U.BishopUpperHalfPlanePoint) where
  module L = Rows.At inputs p
  module Rw = D.At inputs
  q = Rw.q p
  r = Radius.machinQRadius (C.im (U.tau p))
  disk = Rw.disk p
  unit = Disk.unitInterval disk
  env = Disk.powerEnvelope disk
  tail4 = E.e4BishopTailLimit q unit env
  tail6 = E.e6BishopUnsignedTailLimit q unit env

  budget4 : Seq._isConvergent (Seq.SeriesOf (Lam.degreeBudget 240 3 r))
  budget4 = Seq.proposition-3-5 (Seq.absolute⇒isConvergent (Major.e4MajorantAbsoluteConvergence unit))
    (zero , λ n _ → P.≤-respˡ-≃
      (P.nonNegx⇒∣x∣≃x (P.nonNegx,y⇒nonNegx*y (E.e4CoefficientNonnegative n)
        (E.ratioPowerNonnegative unit (suc n))))
      (P.≤-respʳ-≃ (E.e4MajorantMeaning r n)
        (P.*-monoʳ-≤-nonNeg (E.e4CoefficientBound n) (E.ratioPowerNonnegative unit (suc n)))))

  module Lam4 = Lam.At 240 3 q r disk
  module Degree4 = Lam4.FromDegree tail4 (Seq.lim budget4)
    (E.e4BishopTailConvergence q unit env) (proj₂ budget4)

  unsigned4 : Nat → BishopComplex
  unsigned4 zero = A.zeroC
  unsigned4 (suc m) = scaleC (N.natReal 240) (L.N.PositiveRow.F4 m)

  row4Conv : ∀ m → Mod.Converges
    (λ n → Mod.sumC (λ d → Lam.term 240 3 q (m , d)) (H.oneTo n)) (unsigned4 m)
  row4Conv zero = Mod.limitCong (λ _ → A.zeroC) _ A.zeroC
    (λ n → P.≃-symm (Lam.zeroSum (H.oneTo n)) , P.≃-symm (Lam.zeroSum (H.oneTo n)))
    (Power.constantConverges R.0ℝ , Power.constantConverges R.0ℝ)
  row4Conv (suc m) =
    let point = Pos.positivePoint p m
    in limitTransport (A.scaleCCongruent
      (complexTrans (Rw.actualFourier4 point) (L.N.PositiveRow.row4Read m)) (N.natReal 240))
      (Lam4.rowConverges m (Rw.q point) _ (Rw.disk point) (L.N.qPower m))

  unsignedPrefix4 : Nat → BishopComplex
  unsignedPrefix4 n = C.complex (Seq.SeriesOf (λ m → C.re (unsigned4 (suc m))) n)
    (Seq.SeriesOf (λ m → C.im (unsigned4 (suc m))) n)

  unsigned4Conv : Mod.Converges unsignedPrefix4 tail4
  unsigned4Conv = Mod.limitCong (λ n → Mod.sumC unsigned4 (H.oneTo n)) unsignedPrefix4 tail4
    (λ n → Lam.oneToRead (λ m → C.re (unsigned4 m)) n ,
            Lam.oneToRead (λ m → C.im (unsigned4 m)) n)
    (Degree4.actualRows unsigned4 row4Conv)

  scalar4 : L.N.coeff4 ≃ Z.zeta 2 * N.natReal 240
  scalar4 = P.*-comm _ _

  rawRow4 : ∀ m → L.value4 m ≈C scaleC (Z.zeta 2) (unsigned4 (suc m))
  rawRow4 m = complexTrans (Leaf.scaleCong scalar4 (C.≈C-refl _))
    (Lam.scaleScale _ _ _)

  rawPrefix4 : ∀ n → L.Four.positivePrefix n ≈C
    scaleC (Z.zeta 2) (unsignedPrefix4 n)
  rawPrefix4 n =
    P.≃-trans (Z.prefixCong _ _ (λ m → proj₁ (rawRow4 m)) n)
      (Z.prefixScale _ (λ m → C.re (unsigned4 (suc m))) n) ,
    P.≃-trans (Z.prefixCong _ _ (λ m → proj₂ (rawRow4 m)) n)
      (Z.prefixScale _ (λ m → C.im (unsigned4 (suc m))) n)

  axisScale4 : C.re Norm.factor4 * (two * Z.zeta 2) ≃ R.1ℝ
  axisScale4 = P.≃-trans (P.*-congˡ (P.*-congˡ L.N.Zn.zeta4))
    (P.≃-trans (let open P.ℝ-Solver in solve 2
      (λ i p → (Κ (+ 45 / 1) ⊗ i) ⊗ (Κ (+ 2 / 1) ⊗ (Κ (+ 1 / 90) ⊗ p))
        ⊜ i ⊗ p) P.≃-refl (R.pow Norm.piInverse 4) (R.pow D.pi 4))
      (powerCancel 4))

  normalizedPrefix4 : ∀ n → (Norm.factor4 *C L.Four.doublePrefix n) ≈C
    (A.oneC +C unsignedPrefix4 n)
  normalizedPrefix4 n = complexTrans
    (A.mulCCongruent (C.≈C-refl _) (A.addCCongruent (C.≈C-refl _)
      (A.scaleCCongruent (rawPrefix4 n) two)))
    (normalizePlus _ _ _ axisScale4)

  same4 : Norm.E4 p ≈C E.e4BishopLimit q unit env
  same4 = Mod.limitUnique (λ n → A.oneC +C unsignedPrefix4 n) _ _
    (Mod.limitCong (λ n → Norm.factor4 *C L.Four.doublePrefix n) _ _
      normalizedPrefix4 (Mod.mulLimit L.Four.doublePrefix L.B.G4 Norm.factor4 L.G4Rows))
    (Inv.addR (Power.constantConverges R.1ℝ) (proj₁ unsigned4Conv) ,
     Inv.addR (Power.constantConverges R.0ℝ) (proj₂ unsigned4Conv))

  budget6 : Seq._isConvergent (Seq.SeriesOf (Lam.degreeBudget 504 5 r))
  budget6 = Seq.proposition-3-5 (Seq.absolute⇒isConvergent (Major.e6MajorantAbsoluteConvergence unit))
    (zero , λ n _ → P.≤-respˡ-≃
      (P.nonNegx⇒∣x∣≃x (P.nonNegx,y⇒nonNegx*y (E.e6CoefficientNonnegative n)
        (E.ratioPowerNonnegative unit (suc n))))
      (P.≤-respʳ-≃ (E.e6MajorantMeaning r n)
        (P.*-monoʳ-≤-nonNeg (E.e6CoefficientBound n) (E.ratioPowerNonnegative unit (suc n)))))

  module Lam6 = Lam.At 504 5 q r disk
  module Degree6 = Lam6.FromDegree tail6 (Seq.lim budget6)
    (E.e6BishopUnsignedTailConvergence q unit env) (proj₂ budget6)

  unsigned6 : Nat → BishopComplex
  unsigned6 zero = A.zeroC
  unsigned6 (suc m) = scaleC (N.natReal 504) (L.N.PositiveRow.F6 m)

  row6Conv : ∀ m → Mod.Converges
    (λ n → Mod.sumC (λ d → Lam.term 504 5 q (m , d)) (H.oneTo n)) (unsigned6 m)
  row6Conv zero = Mod.limitCong (λ _ → A.zeroC) _ A.zeroC
    (λ n → P.≃-symm (Lam.zeroSum (H.oneTo n)) , P.≃-symm (Lam.zeroSum (H.oneTo n)))
    (Power.constantConverges R.0ℝ , Power.constantConverges R.0ℝ)
  row6Conv (suc m) =
    let point = Pos.positivePoint p m
    in limitTransport (A.scaleCCongruent
      (complexTrans (Rw.actualFourier6 point) (L.N.PositiveRow.row6Read m)) (N.natReal 504))
      (Lam6.rowConverges m (Rw.q point) _ (Rw.disk point) (L.N.qPower m))

  unsignedPrefix6 : Nat → BishopComplex
  unsignedPrefix6 n = C.complex (Seq.SeriesOf (λ m → C.re (unsigned6 (suc m))) n)
    (Seq.SeriesOf (λ m → C.im (unsigned6 (suc m))) n)

  unsigned6Conv : Mod.Converges unsignedPrefix6 tail6
  unsigned6Conv = Mod.limitCong (λ n → Mod.sumC unsigned6 (H.oneTo n)) unsignedPrefix6 tail6
    (λ n → Lam.oneToRead (λ m → C.re (unsigned6 m)) n ,
            Lam.oneToRead (λ m → C.im (unsigned6 m)) n)
    (Degree6.actualRows unsigned6 row6Conv)

  scalar6 : L.N.coeff6 ≃ (R.- (Z.zeta 4)) * N.natReal 504
  scalar6 = let open P.ℝ-Solver in solve 2 (λ c z → ⊝ (c ⊗ z) ⊜ (⊝ z) ⊗ c)
    P.≃-refl (N.natReal 504) (Z.zeta 4)

  rawRow6 : ∀ m → L.value6 m ≈C scaleC (R.- (Z.zeta 4)) (unsigned6 (suc m))
  rawRow6 m = complexTrans (Leaf.scaleCong scalar6 (C.≈C-refl _))
    (Lam.scaleScale _ _ _)

  rawPrefix6 : ∀ n → L.Six.positivePrefix n ≈C
    scaleC (R.- (Z.zeta 4)) (unsignedPrefix6 n)
  rawPrefix6 n =
    P.≃-trans (Z.prefixCong _ _ (λ m → proj₁ (rawRow6 m)) n)
      (Z.prefixScale _ (λ m → C.re (unsigned6 (suc m))) n) ,
    P.≃-trans (Z.prefixCong _ _ (λ m → proj₂ (rawRow6 m)) n)
      (Z.prefixScale _ (λ m → C.im (unsigned6 (suc m))) n)

  axisScale6 : C.re Norm.factor6 * (two * Z.zeta 4) ≃ R.1ℝ
  axisScale6 = P.≃-trans (P.*-congˡ (P.*-congˡ L.N.Zn.zeta6))
    (P.≃-trans (let open P.ℝ-Solver in solve 2
      (λ i p → (Κ (+ 945 / 2) ⊗ i) ⊗ (Κ (+ 2 / 1) ⊗ (Κ (+ 1 / 945) ⊗ p))
        ⊜ i ⊗ p) P.≃-refl (R.pow Norm.piInverse 6) (R.pow D.pi 6))
      (powerCancel 6))

  normalizedPrefix6 : ∀ n → (Norm.factor6 *C L.Six.doublePrefix n) ≈C
    (A.oneC -C unsignedPrefix6 n)
  normalizedPrefix6 n = complexTrans
    (A.mulCCongruent (C.≈C-refl _) (A.addCCongruent (C.≈C-refl _)
      (A.scaleCCongruent (rawPrefix6 n) two)))
    (normalizeMinus _ _ _ axisScale6)

  same6 : Norm.E6 p ≈C E.e6BishopLimit q unit env
  same6 = Mod.limitUnique (λ n → A.oneC -C unsignedPrefix6 n) _ _
    (Mod.limitCong (λ n → Norm.factor6 *C L.Six.doublePrefix n) _ _
      normalizedPrefix6 (Mod.mulLimit L.Six.doublePrefix L.B.G6 Norm.factor6 L.G6Rows))
    (Inv.subR (Power.constantConverges R.1ℝ) (proj₁ unsigned6Conv) ,
     Inv.subR (Power.constantConverges R.0ℝ) (proj₂ unsigned6Conv))

-- Transport the already-owned lattice generator laws to the original q object.
module For (inputs : Round11.BishopCutset) where
  module Rw = D.At inputs
  qE4 : U.BishopUpperHalfPlanePoint → BishopComplex
  qE4 p = E.e4BishopLimit (Rw.q p) (Disk.unitInterval (Rw.disk p)) (Disk.powerEnvelope (Rw.disk p))
  qE6 : U.BishopUpperHalfPlanePoint → BishopComplex
  qE6 p = E.e6BishopLimit (Rw.q p) (Disk.unitInterval (Rw.disk p)) (Disk.powerEnvelope (Rw.disk p))
  qE4S : ∀ p → qE4 (G.actS p) ≈C (A.powC (U.tau p) 4 *C qE4 p)
  qE4S p = complexTrans (complexSym (At.same4 inputs (G.actS p)))
    (complexTrans (Norm.E4S p) (A.mulCCongruent (C.≈C-refl _) (At.same4 inputs p)))
  qE4T : ∀ p → qE4 (G.actT p) ≈C qE4 p
  qE4T p = complexTrans (complexSym (At.same4 inputs (G.actT p)))
    (complexTrans (Norm.E4T p) (At.same4 inputs p))
  qE6S : ∀ p → qE6 (G.actS p) ≈C (A.powC (U.tau p) 6 *C qE6 p)
  qE6S p = complexTrans (complexSym (At.same6 inputs (G.actS p)))
    (complexTrans (Norm.E6S p) (A.mulCCongruent (C.≈C-refl _) (At.same6 inputs p)))
  qE6T : ∀ p → qE6 (G.actT p) ≈C qE6 p
  qE6T p = complexTrans (complexSym (At.same6 inputs (G.actT p)))
    (complexTrans (Norm.E6T p) (At.same6 inputs p))
