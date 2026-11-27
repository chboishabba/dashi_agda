module DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact where

-- SOURCE-WRITTEN, UNCOMPILED. The signed dyadic distribution is now on
-- the ORIGINAL Machin exponential at actual upper-half-plane points.
-- Both lifts (z+1)/2 and (z-1)/2 are retained. A selected signed binary
-- refinement does not change either weighted Fourier row.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as Q using (_/_; 0ℚᵘ; 1ℚᵘ)
import Data.Rational.Unnormalised.Properties as QP
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Real as R
open R using (ℝ; _+_; _-_; _*_; _⋆; _≃_)
import RealProperties as P
import DASHI.Analysis.BishopSetoidComplexExact as ExpC
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopMachinCayleyNativeProductFirstZeroExact as Native
import DASHI.Analysis.BishopOriginalMachinCayleyEndpointExact as MachinEnd
import DASHI.Analysis.BishopImaginaryProductPythagoreanReuseExact as Product
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialCauchyProductExact as ExpProduct
import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as E
import DASHI.Physics.YangMills.BalabanBishopSeriesParityAndLimitExact as Parity
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
import DASHI.Moonshine.BishopMachinSetoidComplexInstanceExact as Route
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Weld
import DASHI.Moonshine.AbelBishopOriginalQParameterExact as QAt
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as Radius
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as Disk
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as G
import DASHI.Moonshine.JInvariantBishopDyadicFourierRowExact as D
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopFourierRowRationalExact as Rat
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_; scaleC)
open Comp using (complexTrans; complexSym)

half two pi : ℝ
half = (+ 1 / 2) ⋆
two = (+ 2 / 1) ⋆
pi = Machin.bishopMachinPi

halfPositive : R._<_ R.0ℝ half
halfPositive = P.p<q⇒p⋆<q⋆ Q.0ℚᵘ (+ 1 / 2) (QP.positive⁻¹ (+ 1 / 2))

data Side : Set where
  positive negative : Side

shift : Side → ℝ
shift positive = R.1ℝ
shift negative = R.- R.1ℝ

halfHeightPositive : ∀ p → R._<_ R.0ℝ (half * C.im (U.tau p))
halfHeightPositive p = P.posx⇒0<x (P.posx,y⇒posx*y
  (P.0<x⇒posx halfPositive) (P.0<x⇒posx (U.imaginaryPositive p)))

left : U.BishopUpperHalfPlanePoint → U.BishopUpperHalfPlanePoint
left p = U.bishop-upper-half-plane-point
  (C.complex (half * C.re (U.tau p)) (half * C.im (U.tau p))) (halfHeightPositive p)

right : Side → U.BishopUpperHalfPlanePoint → U.BishopUpperHalfPlanePoint
right s p = U.bishop-upper-half-plane-point
  (C.complex (half * (C.re (U.tau p) + shift s)) (half * C.im (U.tau p)))
  (halfHeightPositive p)

normCong : ∀ {z w} → z ≈C w → Norm.normSqC z ≃ Norm.normSqC w
normCong {C.complex _ _} {C.complex _ _} (a , b) =
  P.+-cong (P.*-cong a a) (P.*-cong b b)

guardCong : ∀ {z w} → z ≈C w → Rec.BishopComplexNonzero z → Rec.BishopComplexNonzero w
guardCong eq nz = record
  { normSquarePositive = P.<-respʳ-≃ (normCong eq) (Rec.normSquarePositive nz) }

gapCong : ∀ {q w} → q ≈C w → D.gapMinus q ≈C D.gapMinus w
gapCong h = A.subCCongruent (C.≈C-refl _) h

XC : ∀ {q w} nz nw → q ≈C w → D.X q nz ≈C D.X w nw
XC {q} {w} nz nw eq =
  let h = G.reciprocalCong (D.gapMinus q) (D.gapMinus w) nz nw (gapCong eq)
  in A.mulCCongruent eq (A.mulCCongruent h h)

P4Cong : ∀ {q w} → q ≈C w → D.P4 q ≈C D.P4 w
P4Cong h = A.addCCongruent h (D.scaleCong 6 (A.mulCCongruent h h))

P6Cong : ∀ {q w} → q ≈C w → D.P6 q ≈C D.P6 w
P6Cong h = A.addCCongruent
  (A.addCCongruent h (D.scaleCong 30 (A.mulCCongruent h h)))
  (D.scaleCong 120 (A.mulCCongruent h (A.mulCCongruent h h)))

module At (inputs : Round11.BishopCutset) where
  T = Route.machinTranscendentals inputs
  product = Native.originalNativeImaginaryExpProduct inputs
  quarter = MachinEnd.originalQuarterEquality inputs
  endpoints = Product.round11MachinTrigEndpointFromImaginaryProduct inputs product quarter

  sinB = Product.sinB inputs
  cosB = Product.cosB inputs

  expAdd : ∀ z w →
    ExpC._≈C_ (ExpC.expC T (ExpC._+C_ z w))
      (ExpC._*C_ (ExpC.expC T z) (ExpC.expC T w))
  expAdd (ExpC.complex a b) (ExpC.complex c d) =
    let laws = ExpC.imaginaryExponentialProductGivesAddition T b d (product b d)
        ea = Exp.bishopExp a
        ec = Exp.bishopExp c
        cb = cosB b
        cd = cosB d
        sb = sinB b
        sd = sinB d
    in ExpC.complex-equivalent
      (P.≃-trans (P.*-cong (ExpProduct.bishopExpAdd a c) (proj₂ laws))
        (let open P.ℝ-Solver in solve 6
          (λ a c cb cd sb sd → (a ⊗ c) ⊗ (cb ⊗ cd ⊖ sb ⊗ sd)
            ⊜ (a ⊗ cb) ⊗ (c ⊗ cd) ⊖ (a ⊗ sb) ⊗ (c ⊗ sd))
          P.≃-refl ea ec cb cd sb sd))
      (P.≃-trans (P.*-cong (ExpProduct.bishopExpAdd a c) (proj₁ laws))
        (let open P.ℝ-Solver in solve 6
          (λ a c cb cd sb sd → (a ⊗ c) ⊗ (sb ⊗ cd ⊕ cb ⊗ sd)
            ⊜ (a ⊗ cb) ⊗ (c ⊗ sd) ⊕ (a ⊗ sb) ⊗ (c ⊗ cd))
          P.≃-refl ea ec cb cd sb sd))

  expS : BishopComplex → BishopComplex
  expS = Weld.originalBishopExpOnSeries T

  expAddS : ∀ z w → expS (z +C w) ≈C (expS z *C expS w)
  expAddS (C.complex a b) (C.complex c d) =
    Weld.originalExpEquivalenceToSeries (expAdd (ExpC.complex a b) (ExpC.complex c d))

  exponent : U.BishopUpperHalfPlanePoint → BishopComplex
  exponent p = C.complex (R.- ((two * pi) * C.im (U.tau p))) ((two * pi) * C.re (U.tau p))

  q : U.BishopUpperHalfPlanePoint → BishopComplex
  q p = expS (exponent p)

  exponentRead : ∀ p → ExpC._≈C_
    (ExpC._*C_ (QAt.originalTwoPiI T) (Weld.toExponential (U.tau p)))
    (Weld.toExponential (exponent p))
  exponentRead p =
    let a = C.re (U.tau p)
        b = C.im (U.tau p)
    in ExpC.complex-equivalent
      (let open P.ℝ-Solver in solve 3
        (λ p a b →
          (((Κ Q.0ℚᵘ ⊗ p ⊖ Κ Q.1ℚᵘ ⊗ Κ Q.0ℚᵘ)
            ⊕ ((Κ Q.0ℚᵘ ⊗ p ⊖ Κ Q.1ℚᵘ ⊗ Κ Q.0ℚᵘ) ⊕ Κ Q.0ℚᵘ)) ⊗ a)
          ⊖ (((Κ Q.0ℚᵘ ⊗ Κ Q.0ℚᵘ ⊕ Κ Q.1ℚᵘ ⊗ p)
            ⊕ ((Κ Q.0ℚᵘ ⊗ Κ Q.0ℚᵘ ⊕ Κ Q.1ℚᵘ ⊗ p) ⊕ Κ Q.0ℚᵘ)) ⊗ b)
          ⊜ ⊝ ((Κ (+ 2 / 1) ⊗ p) ⊗ b))
        P.≃-refl pi a b)
      (let open P.ℝ-Solver in solve 3
        (λ p a b →
          (((Κ Q.0ℚᵘ ⊗ p ⊖ Κ Q.1ℚᵘ ⊗ Κ Q.0ℚᵘ)
            ⊕ ((Κ Q.0ℚᵘ ⊗ p ⊖ Κ Q.1ℚᵘ ⊗ Κ Q.0ℚᵘ) ⊕ Κ Q.0ℚᵘ)) ⊗ b)
          ⊕ (((Κ Q.0ℚᵘ ⊗ Κ Q.0ℚᵘ ⊕ Κ Q.1ℚᵘ ⊗ p)
            ⊕ ((Κ Q.0ℚᵘ ⊗ Κ Q.0ℚᵘ ⊕ Κ Q.1ℚᵘ ⊗ p) ⊕ Κ Q.0ℚᵘ)) ⊗ a)
          ⊜ (Κ (+ 2 / 1) ⊗ p) ⊗ a)
        P.≃-refl pi a b)

  actualQ : ∀ p → QAt.originalRound11MachinQAtForSeries inputs (U.tau p) ≈C q p
  actualQ p = Weld.originalExpEquivalenceToSeries (ExpC.expCongruent T (exponentRead p))

  disk : ∀ p → Disk.BishopUnitDiskQ (q p) (Radius.machinQRadius (C.im (U.tau p)))
  disk p = record
    { unitInterval = Radius.machinQRadiusUnitInterval (U.imaginaryPositive p)
    ; normSquareAgreement = Norm.unitPhaseScaledNormSquare
        (Product.round11PythagoreanFromImaginaryProduct inputs product ((two * pi) * C.re (U.tau p)))
    }

  -- Actual signed half sheets, not an abstract choice of square root.
  doubleExponent : ∀ p → (exponent (left p) +C exponent (left p)) ≈C exponent p
  doubleExponent p =
    (let open P.ℝ-Solver in solve 2
      (λ p b → (⊝ ((Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 2) ⊗ b)))
        ⊕ (⊝ ((Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 2) ⊗ b)))
        ⊜ ⊝ ((Κ (+ 2 / 1) ⊗ p) ⊗ b)) P.≃-refl pi (C.im (U.tau p)))
    ,
    (let open P.ℝ-Solver in solve 2
      (λ p a → ((Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 2) ⊗ a))
        ⊕ ((Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 2) ⊗ a))
        ⊜ (Κ (+ 2 / 1) ⊗ p) ⊗ a) P.≃-refl pi (C.re (U.tau p)))

  squareQ : ∀ p → (q (left p) *C q (left p)) ≈C q p
  squareQ p = complexTrans (complexSym (expAddS (exponent (left p)) (exponent (left p))))
    (Weld.originalBishopExpOnSeriesCongruent T (doubleExponent p))

  shiftAngle : Side → ℝ
  shiftAngle positive = pi
  shiftAngle negative = R.- pi

  shiftExponent : ∀ s p → exponent (right s p) ≈C
    (exponent (left p) +C C.complex R.0ℝ (shiftAngle s))
  shiftExponent positive p =
    P.≃-symm (P.+-identityʳ (C.re (exponent (left p)))) ,
    (let open P.ℝ-Solver in solve 2
      (λ p a → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 2) ⊗ (a ⊕ Κ Q.1ℚᵘ))
        ⊜ ((Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 2) ⊗ a)) ⊕ p)
      P.≃-refl pi (C.re (U.tau p)))
  shiftExponent negative p =
    P.≃-symm (P.+-identityʳ (C.re (exponent (left p)))) ,
    (let open P.ℝ-Solver in solve 2
      (λ p a → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 2) ⊗ (a ⊕ (⊝ Κ Q.1ℚᵘ)))
        ⊜ ((Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 2) ⊗ a)) ⊕ (⊝ p))
      P.≃-refl pi (C.re (U.tau p)))

  negativeOne : BishopComplex
  negativeOne = C.complex (R.- R.1ℝ) R.0ℝ

  shiftPhase : ∀ s → expS (C.complex R.0ℝ (shiftAngle s)) ≈C negativeOne
  shiftPhase positive = Weld.originalExpEquivalenceToSeries
    (ExpC.≈C-trans (ExpC.expImaginaryIsTrigPair T pi)
      (ExpC.complex-equivalent (proj₂ endpoints) (proj₁ endpoints)))
  shiftPhase negative = Weld.originalExpEquivalenceToSeries
    (ExpC.≈C-trans (ExpC.expImaginaryIsTrigPair T (R.- pi))
      (ExpC.complex-equivalent
        (P.≃-trans (Parity.bishopCosNeg (Round11.round11ParityInputs inputs) pi) (proj₂ endpoints))
        (P.≃-trans (Parity.bishopSinNeg (Round11.round11ParityInputs inputs) pi)
          (P.≃-trans (P.-‿cong (proj₁ endpoints)) (P.≃-symm P.0≃-0)))))

  timesNegativeOne : ∀ z → (z *C negativeOne) ≈C D.negC z
  timesNegativeOne (C.complex a b) =
    (let open P.ℝ-Solver in solve 2
      (λ a b → a ⊗ (⊝ Κ Q.1ℚᵘ) ⊖ b ⊗ Κ Q.0ℚᵘ ⊜ ⊝ a) P.≃-refl a b)
    ,
    (let open P.ℝ-Solver in solve 2
      (λ a b → a ⊗ Κ Q.0ℚᵘ ⊕ b ⊗ (⊝ Κ Q.1ℚᵘ) ⊜ ⊝ b) P.≃-refl a b)

  signedQ : ∀ s p → q (right s p) ≈C D.negC (q (left p))
  signedQ s p = complexTrans
    (Weld.originalBishopExpOnSeriesCongruent T (shiftExponent s p))
    (complexTrans (expAddS (exponent (left p)) (C.complex R.0ℝ (shiftAngle s)))
      (complexTrans (A.mulCCongruent (C.≈C-refl _) (shiftPhase s))
        (timesNegativeOne (q (left p)))))

  gapNZ : ∀ p → Rec.BishopComplexNonzero (D.gapMinus (q p))
  gapNZ p = Lim.AtDisk.gapGuard (disk p)

  row4 row6 : U.BishopUpperHalfPlanePoint → BishopComplex
  row4 p = D.P4 (D.X (q p) (gapNZ p))
  row6 p = D.P6 (D.X (q p) (gapNZ p))

  actualFourier4 : ∀ p → Lim.AtDisk.row (disk p) 3 ≈C row4 p
  actualFourier4 p = Rat.AtDisk.fourierRow4 (disk p)

  actualFourier6 : ∀ p → Lim.AtDisk.row (disk p) 5 ≈C row6 p
  actualFourier6 p = Rat.AtDisk.fourierRow6 (disk p)

  module Split (s : Side) (p : U.BishopUpperHalfPlanePoint) where
    h = q (left p)
    nzP = gapNZ (left p)
    nzM = guardCong (gapCong (signedQ s p)) (gapNZ (right s p))
    nz2 = guardCong (gapCong (complexSym (squareQ p))) (gapNZ p)
    module Dsplit = D.At h nzP nzM nz2

    readMinus : D.X (q (right s p)) (gapNZ (right s p)) ≈C Dsplit.V
    readMinus = XC (gapNZ (right s p)) nzM (signedQ s p)

    readParent : Dsplit.W ≈C D.X (q p) (gapNZ p)
    readParent = XC nz2 (gapNZ p) (squareQ p)

    distribution4 : (row4 (left p) +C row4 (right s p)) ≈C D.scale 16 (row4 p)
    distribution4 = complexTrans (A.addCCongruent (C.≈C-refl _) (P4Cong readMinus))
      (complexTrans Dsplit.distribution4 (D.scaleCong 16 (P4Cong readParent)))

    distribution6 : (row6 (left p) +C row6 (right s p)) ≈C D.scale 64 (row6 p)
    distribution6 = complexTrans (A.addCCongruent (C.≈C-refl _) (P6Cong readMinus))
      (complexTrans Dsplit.distribution6 (D.scaleCong 64 (P6Cong readParent)))

  shrink4 : ∀ z → scaleC ((+ 1 / 16) ⋆) (D.scale 16 z) ≈C z
  shrink4 (C.complex a b) =
    (let open P.ℝ-Solver in solve 1 (λ a → Κ (+ 1 / 16) ⊗ (Κ (+ 16 / 1) ⊗ a) ⊜ a) P.≃-refl a) ,
    (let open P.ℝ-Solver in solve 1 (λ b → Κ (+ 1 / 16) ⊗ (Κ (+ 16 / 1) ⊗ b) ⊜ b) P.≃-refl b)

  shrink6 : ∀ z → scaleC ((+ 1 / 64) ⋆) (D.scale 64 z) ≈C z
  shrink6 (C.complex a b) =
    (let open P.ℝ-Solver in solve 1 (λ a → Κ (+ 1 / 64) ⊗ (Κ (+ 64 / 1) ⊗ a) ⊜ a) P.≃-refl a) ,
    (let open P.ℝ-Solver in solve 1 (λ b → Κ (+ 1 / 64) ⊗ (Κ (+ 64 / 1) ⊗ b) ⊜ b) P.≃-refl b)

  -- Exact all-depth refinement. The sheet can be chosen at every vertex;
  -- a later signed-centred exhaustion is a specialization, not a new row.
  Selector : Set
  Selector = Nat → U.BishopUpperHalfPlanePoint → Side

  refine4 : Selector → Nat → U.BishopUpperHalfPlanePoint → BishopComplex
  refine4 select zero p = row4 p
  refine4 select (suc n) p = scaleC ((+ 1 / 16) ⋆)
    (refine4 select n (left p) +C refine4 select n (right (select n p) p))

  refine6 : Selector → Nat → U.BishopUpperHalfPlanePoint → BishopComplex
  refine6 select zero p = row6 p
  refine6 select (suc n) p = scaleC ((+ 1 / 64) ⋆)
    (refine6 select n (left p) +C refine6 select n (right (select n p) p))

  refinement4 : ∀ select n p → refine4 select n p ≈C row4 p
  refinement4 select zero p = C.≈C-refl _
  refinement4 select (suc n) p =
    complexTrans (A.scaleCCongruent
      (complexTrans (A.addCCongruent (refinement4 select n (left p))
        (refinement4 select n (right (select n p) p)))
        (Split.distribution4 (select n p) p)) ((+ 1 / 16) ⋆))
      (shrink4 (row4 p))

  refinement6 : ∀ select n p → refine6 select n p ≈C row6 p
  refinement6 select zero p = C.≈C-refl _
  refinement6 select (suc n) p =
    complexTrans (A.scaleCCongruent
      (complexTrans (A.addCCongruent (refinement6 select n (left p))
        (refinement6 select n (right (select n p) p)))
        (Split.distribution6 (select n p) p)) ((+ 1 / 64) ⋆))
      (shrink6 (row6 p))
