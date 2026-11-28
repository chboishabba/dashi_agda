module DASHI.Moonshine.JInvariantBishopRamanujanDeltaNonvanishingExact where

-- SOURCE-WRITTEN, kernel pending. The literal normalized discriminant
-- has an absolutely convergent reciprocal unit at every |q|<1.
-- The original q is nonzero on the upper half-plane, hence the
-- original normalized discriminant has a native apartness witness.
-- No imported eta-product equality, modular orbit reduction, or
-- discriminant nonvanishing assumption.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₂)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (ℝ; _≃_; _*_; _⋆)
import RealProperties as P
import Sequence as Seq
import Inverse as I
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as Laws
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexNonzeroFromComponentExact as NZ
import DASHI.Foundations.BishopSquareNonnegativeExact as Square
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Foundations.BishopFiniteCauchyRingWeldExact as Ring
import DASHI.Foundations.BishopSqrtTwoThirdsMachinConstantExact as MP
import DASHI.Moonshine.JInvariantBishopEulerDefectUniquenessExact as Pos
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
import DASHI.Moonshine.JInvariantBishopRamanujanDeltaUnitExact as D
import DASHI.Moonshine.JInvariantBishopRamanujanDeltaDiskConvergenceExact as DiskConv
import DASHI.Moonshine.JInvariantBishopRamanujanComplexReadoutExact as Read
import DASHI.Moonshine.JInvariantBishopThetaCauchyProductExact as CP
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesExact as E
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as Disk
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as Phase
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as Radius
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as UHP
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as J
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as Gens
import DASHI.Moonshine.JInvariantBishopNativeProofRelevantKleinExact as K
import DASHI.Moonshine.CM163BishopHecke41AnalyticChartsExact as Chart
import DASHI.Moonshine.CM163BishopHecke41ProductExact as Hecke
import DASHI.Moonshine.CM163BishopHecke41SelectedFixedChartsExact as Fixed
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open G using (Series; _≈s_; _⊗s_; _⊖s_)
open C using (BishopComplex; _≈C_)
open A using (_*C_; _+C_; _-C_; scaleC; powC)
open Comp using (complexTrans; complexSym)
open Read using (Readout; value; weight)

normNN : ∀ z → R.NonNegative (Norm.normSqC z)
normNN (C.complex a b) = P.nonNegx,y⇒nonNegx+y
  (Square.bishopSquareNonnegative a) (Square.bishopSquareNonnegative b)

-- A true inverse witness gives an explicit positive norm-square floor.
-- Upper-bound the inverse norm-square by an Archimedean integer and
-- multiply by its positive reciprocal. No decidable real equality.
inverseGivesGuard : ∀ z v → (z *C v) ≈C A.oneC → Rec.BishopComplexNonzero z
inverseGivesGuard z v h =
  let a = Norm.normSqC z
      b = Norm.normSqC v
      eq = P.≃-trans (P.≃-symm (Norm.normSqMultiply z v))
        (P.≃-trans (Phase.normCong h) Norm.normSqOne)
      upper = P.fast-archimedean-ℝ b
      m = NR.natReal (suc (proj₁ upper))
      mp = Pos.positiveNat (proj₁ upper)
      mnz = inj₂ (P.posx⇒0<x mp)
      mi = I._⁻¹ m mnz
      mip = I.0<x⇒0<x⁻¹ mnz (P.posx⇒0<x mp)
      oneBelow = P.≤-respˡ-≃ eq
        (P.*-monoˡ-≤-nonNeg (P.<⇒≤ (proj₂ upper)) (normNN z))
      onePositive = P.posx⇒0<x (Pos.positiveNat zero)
      productPositive = P.<-≤-trans onePositive oneBelow
      scaled = J.positiveMul mip productPositive
      clear = P.≃-trans (let open P.ℝ-Solver in solve 3
        (λ i a m → i ⊗ (a ⊗ m) ⊜ a ⊗ (m ⊗ i)) P.≃-refl mi a m)
        (P.≃-trans (P.*-congˡ (I.*-inverseʳ m mnz)) (P.*-identityʳ a))
  in record { Rec.normSquarePositive = P.<-respʳ-≃ clear scaled }

-- The normalized shift is the exact literal multiplication by q.
deltaShift : (Read.monomial ⊗s D.unit) ≈s D.Delta
deltaShift zero = P.≃-trans (U.mul0 {f = Read.monomial} {g = D.unit} P.≃-refl D.unit0)
  (P.≃-trans (P.*-zeroˡ R.1ℝ) (P.≃-symm D.delta0))
deltaShift (suc n) = P.≃-trans (U.zeroHead Read.monomial D.unit P.≃-refl n)
  (Ring.rowUnitLeft D.unit n)

module AtDisk (q : BishopComplex) (r : ℝ) (disk : Disk.BishopUnitDiskQ q r) where
  module DC = DiskConv.AtDisk q r disk
  module K0 = K.AtDisk disk
  u = Disk.unitInterval disk
  env = Disk.powerEnvelope disk

  xTail : Nat → BishopComplex
  xTail = E.e4BishopTerm q

  xHeadRead : ∀ n → Read.prepend A.oneC xTail n ≈C weight q U.X n
  xHeadRead zero = complexSym (P.*-identityˡ R.1ℝ , P.*-zeroʳ R.1ℝ)
  xHeadRead (suc n) = C.≈C-refl _

  xRead : Readout q U.X
  xRead =
    let ab = E.e4BishopComponentwiseAbsoluteConvergence q u env
        cv = E.e4BishopTailConvergence q u env
        ha = C.componentwise-absolute-series-convergent
          (Read.prependAbs R.1ℝ (C.realTerms xTail) (C.realAbsolute ab))
          (Read.prependAbs R.0ℝ (C.imagTerms xTail) (C.imagAbsolute ab))
    in record { value = K0.E4 ; absolute = CP.complexAbsTransport xHeadRead ha
      ; converges = CP.complexLimitTransport xHeadRead
          (Read.prependComplex A.oneC xTail _ ab cv ha) }

  yUnsigned : Nat → BishopComplex
  yUnsigned = E.e6BishopUnsignedTerm q
  yTail : Nat → BishopComplex
  yTail n = A.zeroC -C yUnsigned n

  yHeadRead : ∀ n → Read.prepend A.oneC yTail n ≈C weight q U.Y n
  yHeadRead zero = complexSym (P.*-identityˡ R.1ℝ , P.*-zeroʳ R.1ℝ)
  yHeadRead (suc n) =
    (let open P.ℝ-Solver in solve 2 (λ a x → Κ 0ℚᵘ ⊖ a ⊗ x ⊜ (⊝ a) ⊗ x)
      P.≃-refl (E.e6CoefficientReal n) (C.re (powC q (suc n)))) ,
    (let open P.ℝ-Solver in solve 2 (λ a x → Κ 0ℚᵘ ⊖ a ⊗ x ⊜ (⊝ a) ⊗ x)
      P.≃-refl (E.e6CoefficientReal n) (C.im (powC q (suc n))))

  yRead : Readout q U.Y
  yRead =
    let ab = E.e6BishopComponentwiseAbsoluteConvergence q u env
        cv = E.e6BishopUnsignedTailConvergence q u env
        v = E.e6BishopUnsignedTailLimit q u env
        tb = C.componentwise-absolute-series-convergent
          (CP.minusAbs (λ _ → R.0ℝ) (C.realTerms yUnsigned) Read.zeroAbs (C.realAbsolute ab))
          (CP.minusAbs (λ _ → R.0ℝ) (C.imagTerms yUnsigned) Read.zeroAbs (C.imagAbsolute ab))
        tc = C.complex-series-converges-to
          (CP.minusConv Read.zeroConv (C.realConverges cv))
          (CP.minusConv Read.zeroConv (C.imagConverges cv))
        ha = C.componentwise-absolute-series-convergent
          (Read.prependAbs R.1ℝ (C.realTerms yTail) (C.realAbsolute tb))
          (Read.prependAbs R.0ℝ (C.imagTerms yTail) (C.imagAbsolute tb))
        pre = Read.prependComplex A.oneC yTail (A.zeroC -C v) tb tc ha
        final = C.complex-series-converges-to
          (Seq.xₙ→x∧x≃y⇒xₙ→y (C.realConverges pre)
            (let open P.ℝ-Solver in solve 1 (λ x → Κ 1ℚᵘ ⊕ (Κ 0ℚᵘ ⊖ x) ⊜ Κ 1ℚᵘ ⊖ x)
              P.≃-refl (C.re v)))
          (Seq.xₙ→x∧x≃y⇒xₙ→y (C.imagConverges pre)
            (let open P.ℝ-Solver in solve 1 (λ x → Κ 0ℚᵘ ⊕ (Κ 0ℚᵘ ⊖ x) ⊜ Κ 0ℚᵘ ⊖ x)
              P.≃-refl (C.im v)))
    in record { value = K0.E6 ; absolute = CP.complexAbsTransport yHeadRead ha
      ; converges = CP.complexLimitTransport yHeadRead final }

  x3 : Readout q U.X3
  x3 = Read.product (Read.product xRead xRead) xRead

  discriminant : Readout q D.Delta
  discriminant = Read.transport (G.scaleIsProduct (+ 1 / 1728) U.disc)
    (Read.product (Read.constantRead q ((+ 1 / 1728) ⋆))
      (Read.subtract x3 (Read.product yRead yRead)))

  deltaRead : value discriminant ≈C K0.Delta
  deltaRead =
    let h = (+ 1 / 1728) ⋆
        z = K.cube K0.E4 -C (K0.E6 *C K0.E6)
    in (let open P.ℝ-Solver in solve 3
        (λ h x y → h ⊗ x ⊖ Κ 0ℚᵘ ⊗ y ⊜ h ⊗ x) P.≃-refl h (C.re z) (C.im z)) ,
       (let open P.ℝ-Solver in solve 3
        (λ h x y → h ⊗ y ⊕ Κ 0ℚᵘ ⊗ x ⊜ h ⊗ y) P.≃-refl h (C.re z) (C.im z))

  unitRead : Readout q D.unit
  unitRead = Read.fromAbsolute DC.unitAbsolute
  inverseRead : Readout q D.reciprocal
  inverseRead = Read.fromAbsolute DC.inverseAbsolute

  unitLaw : (value unitRead *C value inverseRead) ≈C A.oneC
  unitLaw = Read.same (Read.transport D.unitInverse (Read.product unitRead inverseRead))
    (Read.constantRead q R.1ℝ)

  unitGuard : Rec.BishopComplexNonzero (value unitRead)
  unitGuard = inverseGivesGuard _ _ unitLaw

  qUnit : (q *C value unitRead) ≈C K0.Delta
  qUnit = complexTrans
    (Read.same (Read.transport deltaShift (Read.product (Read.monomialRead q) unitRead)) discriminant)
    deltaRead

  deltaGuard : Rec.BishopComplexNonzero q → Rec.BishopComplexNonzero K0.Delta
  deltaGuard nz = Phase.guardCong qUnit (J.nonzeroMul nz unitGuard)

  Jread : Readout q D.Junit
  Jread = Read.product x3 inverseRead

  JunitLaw : (value unitRead *C value Jread) ≈C K.cube K0.E4
  JunitLaw = Read.same (Read.transport D.jRelation (Read.product unitRead Jread)) x3

  -- The actual normalized j readout is not a different coefficient
  -- stream. It is q times the native proof-relevant quotient.
  actualJ : (nz : Rec.BishopComplexNonzero q) →
    (q *C J.quot (K.cube K0.E4) K0.Delta (deltaGuard nz)) ≈C value Jread
  actualJ nz =
    let j = J.quot (K.cube K0.E4) K0.Delta (deltaGuard nz)
        u0 = value unitRead
        left = complexTrans (complexSym (Laws.complexMultiplyAssociative u0 q j))
          (complexTrans (A.mulCCongruent (Laws.complexMultiplyCommutative u0 q) (C.≈C-refl j))
            (complexTrans (A.mulCCongruent qUnit (C.≈C-refl j))
              (J.clearQuot (K.cube K0.E4) K0.Delta (deltaGuard nz))))
    in J.cancelLeft u0 (q *C j) (value Jread) unitGuard
      (complexTrans left (complexSym JunitLaw))

module At (inputs : Round11.BishopCutset) where
  module Pha = Phase.At inputs
  module KJ = J.At inputs
  module Hk = Hecke.At inputs
  module Selected = Fixed.At inputs

  qNonzero : ∀ p → Rec.BishopComplexNonzero (Pha.q p)
  qNonzero p = record
    { Rec.normSquarePositive = P.<-respʳ-≃
        (P.≃-symm (Disk.normSquareAgreement (Pha.disk p)))
        (NZ.squarePositiveFromApart
          (inj₂ (Radius.qRadiusPositive MP.machinPiPositive (UHP.imaginaryPositive p)))) }

  globalGuard : ∀ p → KJ.Guard p
  globalGuard p = AtDisk.deltaGuard (Pha.q p)
    (Radius.machinQRadius (C.im (UHP.tau p))) (Pha.disk p) (qNonzero p)

  allGuards : ∀ p → Hk.AllGuards p
  allGuards p i = globalGuard (Chart.chartPoint i p)

  j : UHP.BishopUpperHalfPlanePoint → BishopComplex
  j p = KJ.j p (globalGuard p)

  product : UHP.BishopUpperHalfPlanePoint → BishopComplex → BishopComplex
  product p y = Hk.value p (allGuards p) y

  diagonal : UHP.BishopUpperHalfPlanePoint → BishopComplex
  diagonal p = Hk.diagonal p (globalGuard p) (allGuards p)

  productS : ∀ p y → product (Gens.actS p) y ≈C product p y
  productS p y = Hk.valueS p y (allGuards p) (allGuards (Gens.actS p))

  productT : ∀ p y → product (Gens.actT p) y ≈C product p y
  productT p y = Hk.valueT p y (allGuards p) (allGuards (Gens.actT p))

  diagonalS : ∀ p → diagonal (Gens.actS p) ≈C diagonal p
  diagonalS p = Hk.diagonalS p (globalGuard p) (globalGuard (Gens.actS p))
    (allGuards p) (allGuards (Gens.actS p))

  diagonalT : ∀ p → diagonal (Gens.actT p) ≈C diagonal p
  diagonalT p = Hk.diagonalT p (globalGuard p) (globalGuard (Gens.actT p))
    (allGuards p) (allGuards (Gens.actT p))

  selectedDiagonalZero : diagonal Fixed.p ≈C A.zeroC
  selectedDiagonalZero = complexTrans
    (Hk.valueCong Fixed.p (allGuards Fixed.p) (allGuards Fixed.p)
      (J.quotCong (C.≈C-refl _) (C.≈C-refl _) (globalGuard Fixed.p) Selected.guard))
    (Selected.quotientDiagonalZero (allGuards Fixed.p))
