module DASHI.Moonshine.JInvariantBishopAllLatticeRowsExact where

-- SOURCE-WRITTEN, kernel pending. Assemble the actual positive, negative
-- and punctured axis rows into the existing cofinal lattice sum. No
-- equality between the resulting Lambert series and E4/E6 is assumed.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base as Z using (ℤ; +_; -[1+_])
import Data.Integer.Properties as ZP
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ)
open import Data.List.Base using (allFin)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym; subst)
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as Laws
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorModularityExact as Mod
import DASHI.Moonshine.JInvariantBishopLatticeEvenPowerShellMajorantExact as E
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as K
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopSquareShellReindexExact as Re
import DASHI.Moonshine.JInvariantBishopRectangleRowLimitAttachmentExact as Rect
import DASHI.Moonshine.JInvariantBishopRowEndpointNullExact as Endpoint
import DASHI.Moonshine.JInvariantBishopSymmetricRowChartExact as Chart
import DASHI.Moonshine.JInvariantBishopEvenLatticeReflectionExact as Neg
import DASHI.Moonshine.JInvariantBishopAxisRowExact as Axis
import DASHI.Moonshine.JInvariantBishopEvenZetaNormalizationExact as Zeta
import DASHI.Moonshine.JInvariantBishopNormalizedPositiveRowExact as Pos
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as LR
import DASHI.Moonshine.JInvariantBishopCenteredDyadicRowClosureExact as Close
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopPuncturedShellSummabilityExact as Sum
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Cube
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as L
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_+C_; _*C_; scaleC)
open Comp using (complexTrans; complexSym)

rowPrefix : Nat → U.BishopUpperHalfPlanePoint → ℤ → Nat → BishopComplex
rowPrefix w p j n = Mod.sumC
  (λ i → Mod.rawC (E.summand w p) (L.lattice-point j (Cube.decodeCoordinate n i)))
  (allFin (Cube.coordinateCodeBound n))

negativePrefix : ∀ {w} → Neg.EvenWeight w → ∀ p m n →
  rowPrefix w p (-[1+ m ]) n ≈C rowPrefix w p (+ suc m) n
negativePrefix {w} even p m n =
  let f = Mod.rawC (E.summand w p)
      a = λ j → f (L.lattice-point (-[1+ m ]) j)
      b = λ j → f (L.lattice-point (+ suc m) j)
      point : ∀ j → a j ≈C b (Z.- j)
      point j = subst (λ z → f (L.lattice-point (-[1+ m ]) z) ≈C b (Z.- j))
        (ZP.neg-involutive j) (Neg.rawNeg even p (L.lattice-point (+ suc m) (Z.- j)))
  in P.≃-trans (Chart.codeSum (λ j → C.re (a j)) n)
       (P.≃-trans (Re.sumCong (λ j → C.re (a j)) (λ j → C.re (b (Z.- j)))
         (Chart.symmetric n) (λ j → proj₁ (point j)))
         (P.≃-trans (Chart.negSum (λ j → C.re (b j)) n)
           (P.≃-symm (Chart.codeSum (λ j → C.re (b j)) n)))) ,
     P.≃-trans (Chart.codeSum (λ j → C.im (a j)) n)
       (P.≃-trans (Re.sumCong (λ j → C.im (a j)) (λ j → C.im (b (Z.- j)))
         (Chart.symmetric n) (λ j → proj₂ (point j)))
         (P.≃-trans (Chart.negSum (λ j → C.im (b j)) n)
           (P.≃-symm (Chart.codeSum (λ j → C.im (b j)) n))))

module Weight
  (extra : Nat) (even : Neg.EvenWeight (suc (suc extra)))
  (p : U.BishopUpperHalfPlanePoint)
  (v a : BishopComplex)
  (shell : Mod.ShellConverges (suc (suc extra)) p v)
  (absolute : Mod.ShellAbsConverges (suc (suc extra)) p a)
  (positiveValue : Nat → BishopComplex)
  (positiveCentered : ∀ m → Lim.Conv
    (Close.pairPrefix (λ j → E.summand (suc (suc extra)) p (Pos.index m j))) (positiveValue m))
  where
  w = suc (suc extra)
  f = E.summand w p
  respect = Re.summandRespect w p
  real = λ i → C.re (f i)
  imag = λ i → C.im (f i)
  realRespect : Re.PointRespect real
  realRespect i j h = proj₁ (respect i j h)
  imagRespect : Re.PointRespect imag
  imagRespect i j h = proj₂ (respect i j h)

  module EndRe = Endpoint.At real realRespect (C.re a) (proj₁ absolute)
  module EndIm = Endpoint.At imag imagRespect (C.im a) (proj₂ absolute)
  module RRe = Rect.At real realRespect (C.re v) (C.re a) (proj₁ shell) (proj₁ absolute)
  module RIm = Rect.At imag imagRespect (C.im v) (C.im a) (proj₂ shell) (proj₂ absolute)

  value : ℤ → BishopComplex
  value (+ zero) = Axis.axisValue extra
  value (+ suc m) = positiveValue m
  value -[1+ m ] = positiveValue m

  centeredRaw : ∀ m → Lim.Conv
    (Close.pairPrefix (λ j → Mod.rawC f (L.lattice-point (+ suc m) j))) (positiveValue m)
  centeredRaw m = Lim.convTransport
    (LR.prefixCong (λ j → f (Pos.index m j)) (λ j → Mod.rawC f (L.lattice-point (+ suc m) j))
      (λ j → complexSym (Mod.rawCRead f respect (Pos.index m j)))) (positiveCentered m)

  positiveLimit : ∀ m → Mod.Converges (rowPrefix w p (+ suc m)) (positiveValue m)
  positiveLimit m =
    EndRe.symmetricLimit (+ suc m) (C.re (positiveValue m)) (Completion.realConverges (centeredRaw m)) ,
    EndIm.symmetricLimit (+ suc m) (C.im (positiveValue m)) (Completion.imaginaryConverges (centeredRaw m))

  rowLimit : ∀ j → Mod.Converges (rowPrefix w p j) (value j)
  rowLimit (+ zero) = Axis.axisLimit extra even p
  rowLimit (+ suc m) = positiveLimit m
  rowLimit -[1+ m ] = Mod.limitCong
    (rowPrefix w p (+ suc m)) (rowPrefix w p (-[1+ m ])) (positiveValue m)
    (λ n → complexSym (negativePrefix even p m n)) (positiveLimit m)

  rows : Nat → BishopComplex
  rows n = Mod.sumC (λ i → value (Cube.decodeCoordinate n i)) (allFin (Cube.coordinateCodeBound n))

  actualRows : Mod.Converges rows v
  actualRows =
    RRe.actualRowSum (λ j → C.re (value j)) (λ j → proj₁ (rowLimit j)) ,
    RIm.actualRowSum (λ j → C.im (value j)) (λ j → proj₂ (rowLimit j))

  positivePrefix : Nat → BishopComplex
  positivePrefix n = C.complex (Seq.SeriesOf (λ m → C.re (positiveValue m)) n)
    (Seq.SeriesOf (λ m → C.im (positiveValue m)) n)

  doublePrefix : Nat → BishopComplex
  doublePrefix n = Axis.axisValue extra +C scaleC ((+ 2 / 1) R.⋆) (positivePrefix n)

  rowRead : ∀ n → rows n ≈C doublePrefix n
  rowRead n =
    P.≃-trans (Chart.codeSum (λ j → C.re (value j)) n)
      (P.≃-trans (Chart.positivePairRead (λ j → C.re (value j)) n)
        (P.+-cong P.≃-refl (P.≃-trans (Zeta.prefixCong _ _
          (λ m → let open P.ℝ-Solver in solve 1
            (λ x → x ⊕ x ⊜ Κ (+ 2 / 1) ⊗ x) P.≃-refl (C.re (positiveValue m))) n)
          (Zeta.prefixScale ((+ 2 / 1) R.⋆) (λ m → C.re (positiveValue m)) n)))) ,
    P.≃-trans (Chart.codeSum (λ j → C.im (value j)) n)
      (P.≃-trans (Chart.positivePairRead (λ j → C.im (value j)) n)
        (P.+-cong P.≃-refl (P.≃-trans (Zeta.prefixCong _ _
          (λ m → let open P.ℝ-Solver in solve 1
            (λ x → x ⊕ x ⊜ Κ (+ 2 / 1) ⊗ x) P.≃-refl (C.im (positiveValue m))) n)
          (Zeta.prefixScale ((+ 2 / 1) R.⋆) (λ m → C.im (positiveValue m)) n))))

  actualDouble : Mod.Converges doublePrefix v
  actualDouble = Mod.limitCong rows doublePrefix v rowRead actualRows

module At (inputs : Round11.BishopCutset) (p : U.BishopUpperHalfPlanePoint) where
  module B = Sum.At p
  module N = Pos.At inputs p

  value4 : Nat → BishopComplex
  value4 m = scaleC N.coeff4 (N.PositiveRow.F4 m)
  value6 : Nat → BishopComplex
  value6 m = scaleC N.coeff6 (N.PositiveRow.F6 m)

  module Four = Weight 2 Neg.four p B.G4
    (C.complex (Seq.lim B.real4Absolute) (Seq.lim B.imag4Absolute))
    (proj₂ B.real4 , proj₂ B.imag4) (proj₂ B.real4Absolute , proj₂ B.imag4Absolute)
    value4 N.PositiveRow.actualRow4
  module Six = Weight 4 Neg.six p B.G6
    (C.complex (Seq.lim B.real6Absolute) (Seq.lim B.imag6Absolute))
    (proj₂ B.real6 , proj₂ B.imag6) (proj₂ B.real6Absolute , proj₂ B.imag6Absolute)
    value6 N.PositiveRow.actualRow6

  G4Rows : Mod.Converges Four.doublePrefix B.G4
  G4Rows = Four.actualDouble

  G6Rows : Mod.Converges Six.doublePrefix B.G6
  G6Rows = Six.actualDouble
