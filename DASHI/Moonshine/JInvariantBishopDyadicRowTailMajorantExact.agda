module DASHI.Moonshine.JInvariantBishopDyadicRowTailMajorantExact where

-- SOURCE-WRITTEN, UNCOMPILED. Actual signed half-angle gap estimate.
-- An integer-tail cell supplies u >= 0, theta = +/-u, u <= 2,
-- and h*j <= 2*u/3. The lower bound is then rho0*h²*j².
-- These are geometric range inputs, not analytic domination assumptions.
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Integer.Base using (ℤ; +_)
open import Data.Rational.Unnormalised as Q using (_/_; 0ℚᵘ; 1ℚᵘ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
import Real as R
open R using (ℝ; _≃_; _≤_; _<_; _+_; _-_; _*_; _⋆; ∣_∣)
import RealProperties as P
import Data.Rational.Unnormalised.Properties as QP
import DASHI.Foundations.BishopNonnegativeSquareReflectionExact as Reflect
import DASHI.Foundations.BishopInverseSquareProductExact as InvProduct
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as InvSq
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as BaselRead
import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
import DASHI.Foundations.BishopCubicTranslationIteratedExact as N
import DASHI.Foundations.BishopNatRealPositiveExact as NP
import DASHI.Foundations.BishopNegativeExponentialGlobalUnitIntervalExact as One
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as K
import DASHI.Moonshine.JInvariantBishopCenteredDyadicRowExact as Chart
import DASHI.Foundations.BishopSqrtTwoThirdsMachinConstantExact as Pi
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as Laws
import Inverse as I
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopPositiveCrossReciprocalUpperExact as Cross
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Analysis.BishopSinePositiveTwoBallFromCubicExact as SinLower
import DASHI.Analysis.BishopImaginaryProductPythagoreanReuseExact as Trig
import DASHI.Analysis.BishopMachinCayleyNativeProductFirstZeroExact as Native
import DASHI.Analysis.BishopOriginalMachinAtanSmallPhaseExact as Bounds
import DASHI.Foundations.BishopSquareNonnegativeExact as Sq
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialPositiveOrderExact as ExpOrder
import DASHI.Foundations.BishopExponentialCauchyProductExact as ExpProduct
import DASHI.Foundations.BishopExponentialSetoidCongruenceExact as ExpCong
import DASHI.Foundations.BishopSineCosineSetoidCongruenceExact as Cong
import DASHI.Analysis.BishopOriginalNonnegativeNegativeExpBoundExact as NegExp
import DASHI.Physics.YangMills.BalabanBishopSineTwoBallCubicLowerExact as TwoBall
import DASHI.Physics.YangMills.BalabanBishopSeriesParityAndLimitExact as Parity
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as D
import DASHI.Moonshine.JInvariantBishopCenteredDyadicSummandLimitExact as Leaf
import DASHI.Moonshine.JInvariantBishopDyadicScaledRowLimitExact as S
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Inv
import DASHI.Moonshine.JInvariantBishopDyadicFourierRowExact as Row
import DASHI.Moonshine.JInvariantBishopFourierRowRationalExact as Rat
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open C using (BishopComplex; _≈C_)
open A using (_*C_; _+C_; scaleC; powC)
open Comp using (complexTrans; complexSym)

square = Norm.square

squareMono : ∀ {a b} → R.NonNegative a → a ≤ b → square a ≤ square b
squareMono an le = P.*-mono-≤ an an le le

plusNN : ∀ {a b} → R.NonNegative b → a ≤ a + b
plusNN {a} bn = P.≤-respˡ-≃ (P.≃-symm (P.+-identityʳ a))
  (P.+-mono-≤ P.≤-refl (P.nonNegx⇒0≤x bn))

cancelPositive : ∀ {a b c} → R._<_ R.0ℝ a → (a * b) ≤ (a * c) → b ≤ c
cancelPositive {a} {b} {c} pos le =
  let i = Cross.positiveInverse pos
      law = I.*-inverseʳ a (Cross.positiveNonzero pos)
      cancel : ∀ x → (a * x) * i ≃ x
      cancel x = P.≃-trans
        (let open P.ℝ-Solver in solve 3 (λ a x i → (a ⊗ x) ⊗ i ⊜ (a ⊗ i) ⊗ x) P.≃-refl a x i)
        (P.≃-trans (P.*-congʳ law) (P.*-identityˡ x))
  in P.≤-respʳ-≃ (cancel c)
    (P.≤-respˡ-≃ (P.≃-symm (cancel b))
      (P.*-monoʳ-≤-nonNeg le (Cross.positiveInverseNonnegative pos)))

-- Uniform radial floor on 0 <= u <= a, derived from the original
-- positive exponential tail and its native additive product.
negativeExpFloor : ∀ a u → R.NonNegative a → R.NonNegative u → u ≤ a →
  Exp.bishopExp (R.- a) ≤ Exp.bishopExp (R.- u)
negativeExpFloor a u an un ua =
  let d = a - u
      dn = P.0≤x⇒nonNegx (P.≤-respʳ-≃
        (let open P.ℝ-Solver in solve 2 (λ a u → a ⊕ (⊝ u) ⊜ a ⊖ u) P.≃-refl a u)
        (P.≤-respˡ-≃ (P.≃-symm (P.+-inverseʳ u)) (P.+-mono-≤ ua P.≤-refl)))
      r = Exp.bishopExp (R.- a)
      rNN = P.pos⇒nonNeg (P.0<x⇒posx (NegExp.originalNegativeExpPositiveForNonnegative a an))
      eq = let open P.ℝ-Solver in solve 2
        (λ a u → (⊝ a) ⊕ (a ⊖ u) ⊜ ⊝ u) P.≃-refl a u
  in P.≤-respˡ-≃ (P.≃-symm (P.*-identityʳ r))
    (P.≤-respʳ-≃
      (P.≃-trans (P.≃-symm (ExpProduct.bishopExpAdd (R.- a) d)) (ExpCong.bishopExpCongruent eq))
      (P.*-monoˡ-≤-nonNeg (ExpOrder.bishopExpAtLeastOneOnNonnegative dn) rNN))

module At (inputs : Round11.BishopCutset) where
  module Rw = D.At inputs
  sin = Trig.sinB inputs
  cos = Trig.cosB inputs
  product = Native.originalNativeImaginaryExpProduct inputs

  sinLower : ∀ u → R.NonNegative u → ∣ u ∣ ≤ TwoBall.bishopTwo →
    (TwoBall.bishopOneThird * u) ≤ sin u
  sinLower u un inside = P.≤-trans
    (P.≤-respˡ-≃ (P.*-comm TwoBall.bishopOneThird u)
      (P.≤-respʳ-≃ (P.≃-symm (SinLower.cubicSineLowerFactors u))
        (P.*-monoˡ-≤-nonNeg (SinLower.oneThirdBelowSineFactor u un inside) un)))
    (TwoBall.sineCubicLowerTwoBall record
      { termIdentification = Round11.concreteTermIdentification inputs
      ; valueNonnegative = un
      ; insideTwo = inside })

  signedSinSquare : ∀ t u → (t ≃ u) ⊎ (t ≃ R.- u) →
    square (sin t) ≃ square (sin u)
  signedSinSquare t u (inj₁ eq) =
    let e = Cong.bishopSinCongruent (Round11.concreteTermIdentification inputs) eq
    in P.*-cong e e
  signedSinSquare t u (inj₂ eq) =
    let e = P.≃-trans (Cong.bishopSinCongruent (Round11.concreteTermIdentification inputs) eq)
          (Parity.bishopSinNeg (Round11.round11ParityInputs inputs) u)
    in P.≃-trans (P.*-cong e e)
      (let open P.ℝ-Solver in solve 1 (λ s → (⊝ s) ⊗ (⊝ s) ⊜ s ⊗ s) P.≃-refl (sin u))

  cosDouble : ∀ t → cos (t + t) ≃ (R.1ℝ - ((+ 2 / 1) ⋆) * square (sin t))
  cosDouble t =
    let add = proj₂ (Cartesian.imaginaryExponentialProductGivesAddition Rw.T t t (product t t))
        unit = Trig.round11PythagoreanFromImaginaryProduct inputs product t
    in P.≃-trans add
      (P.≃-trans
        (let open P.ℝ-Solver in solve 2
          (λ c s → c ⊗ c ⊖ s ⊗ s ⊜ (c ⊗ c ⊕ s ⊗ s) ⊖ Κ (+ 2 / 1) ⊗ (s ⊗ s))
          P.≃-refl (cos t) (sin t))
        (P.+-cong unit P.≃-refl))

  -- Literal Cartesian phase, with radius not silently set to one.
  phase : ℝ → ℝ → BishopComplex
  phase rho t = C.complex (rho * cos (t + t)) (rho * sin (t + t))

  gapNorm : ∀ rho t → Norm.normSqC (Row.gapMinus (phase rho t)) ≃
    (square (R.1ℝ - rho) + ((+ 4 / 1) ⋆) * rho * square (sin t))
  gapNorm rho t =
    let c = cos (t + t)
        s = sin (t + t)
        p = sin t
        unit = Trig.round11PythagoreanFromImaginaryProduct inputs product (t + t)
    in P.≃-trans
      (let open P.ℝ-Solver in solve 3
        (λ r c s → (Κ 1ℚᵘ ⊖ r ⊗ c) ⊗ (Κ 1ℚᵘ ⊖ r ⊗ c)
          ⊕ (Κ 0ℚᵘ ⊖ r ⊗ s) ⊗ (Κ 0ℚᵘ ⊖ r ⊗ s)
          ⊜ (Κ 1ℚᵘ ⊖ Κ (+ 2 / 1) ⊗ r ⊗ c) ⊕ (r ⊗ r) ⊗ (c ⊗ c ⊕ s ⊗ s))
        P.≃-refl rho c s)
      (P.≃-trans (P.+-cong
          (P.+-cong P.≃-refl (P.-‿cong (P.*-congˡ (cosDouble t))))
          (P.*-congˡ unit))
        (let open P.ℝ-Solver in solve 2
          (λ r p → (Κ 1ℚᵘ ⊖ Κ (+ 2 / 1) ⊗ r ⊗ (Κ 1ℚᵘ ⊖ Κ (+ 2 / 1) ⊗ (p ⊗ p)))
            ⊕ (r ⊗ r) ⊗ Κ 1ℚᵘ
            ⊜ (Κ 1ℚᵘ ⊖ r) ⊗ (Κ 1ℚᵘ ⊖ r) ⊕ Κ (+ 4 / 1) ⊗ r ⊗ (p ⊗ p))
          P.≃-refl rho p))

  -- h*J <= (2/3)*u is the centred signed lattice distance estimate.
  -- It implies h*J <= 2*sin(u), so no loss of the negative sheet.
  gapLower : ∀ rho rho0 t u h J →
    R.NonNegative rho0 → rho0 ≤ rho → R.NonNegative u →
    ∣ u ∣ ≤ TwoBall.bishopTwo → (t ≃ u) ⊎ (t ≃ R.- u) →
    R.NonNegative (h * J) →
    (h * J) ≤ ((+ 2 / 3) ⋆) * u →
    (rho0 * square (h * J)) ≤ Norm.normSqC (Row.gapMinus (phase rho t))
  gapLower rho rho0 t u h J r0n r0r un inside sign hjNN dist =
    let s = sin u
        lo = sinLower u un inside
        twoS = ((+ 2 / 1) ⋆) * s
        hjTwoS = P.≤-trans dist
          (P.≤-respˡ-≃
            (let open P.ℝ-Solver in solve 1
              (λ u → Κ (+ 2 / 3) ⊗ u ⊜ Κ (+ 2 / 1) ⊗ (Κ (+ 1 / 3) ⊗ u))
              P.≃-refl u)
            (P.*-monoˡ-≤-nonNeg lo Bounds.twoNN))
        raw = P.*-mono-≤ r0n (Sq.bishopSquareNonnegative (h * J)) r0r
                (squareMono hjNN hjTwoS)
        signed = P.*-congˡ (P.≃-symm (signedSinSquare t u sign))
        radial = square (R.1ℝ - rho)
        expr = ((+ 4 / 1) ⋆) * rho * square (sin t)
    in P.≤-trans
      (P.≤-respʳ-≃
        (P.≃-trans
          (let open P.ℝ-Solver in solve 2
            (λ r s → r ⊗ ((Κ (+ 2 / 1) ⊗ s) ⊗ (Κ (+ 2 / 1) ⊗ s))
              ⊜ Κ (+ 4 / 1) ⊗ r ⊗ (s ⊗ s)) P.≃-refl rho s) signed) raw)
      (P.≤-respʳ-≃ (P.≃-symm (gapNorm rho t))
        (P.≤-respʳ-≃ (P.+-comm expr radial) (plusNN (Sq.bishopSquareNonnegative (R.1ℝ - rho)))))

-- Algebraic bridge from the gap estimate to the actual scaled inverse.
-- No evaluation of the unscaled inverse at h=0.
scaledInverseBound : ∀ q (nz : Rec.BishopComplexNonzero (Row.gapMinus q)) h b →
  R._<_ R.0ℝ h → R.NonNegative b →
  square h ≤ b * Norm.normSqC (Row.gapMinus q) →
  Norm.normSqC (scaleC (R.- h) (Rec.reciprocalC (Row.gapMinus q) nz)) ≤ b
scaledInverseBound q nz h b hp bn cross =
  let g = Row.gapMinus q
      i = Rec.reciprocalC g nz
      v = scaleC (R.- h) i
      d = Norm.normSqC g
      law = Inv.normInverse g i (Rec.multiplyReciprocal g nz)
      raw = P.*-monoʳ-≤-nonNeg cross (Inv.normNN i)
      left = P.≃-trans (Rec.normSquareScale (R.- h) i)
        (P.*-congʳ (let open P.ℝ-Solver in solve 1
          (λ h → (⊝ h) ⊗ (⊝ h) ⊜ h ⊗ h) P.≃-refl h))
      right = P.≃-trans (P.*-assoc b d (Norm.normSqC i))
        (P.≃-trans (P.*-congˡ law) (P.*-identityʳ b))
  in P.≤-respʳ-≃ right (P.≤-respˡ-≃ left raw)

Box : BishopComplex → ℝ → Set
Box z b = (∣ C.re z ∣ ≤ b) × (∣ C.im z ∣ ≤ b)

boxCong : ∀ {z w b} → z ≈C w → Box w b → Box z b
boxCong (r , i) (a , b) = P.≤-respˡ-≃ (P.∣-∣-cong r) a , P.≤-respˡ-≃ (P.∣-∣-cong i) b

boxBudget : ∀ {z a b} → a ≃ b → Box z a → Box z b
boxBudget eq (r , i) = P.≤-respʳ-≃ eq r , P.≤-respʳ-≃ eq i

boxAdd : ∀ {z w a b} → Box z a → Box w b → Box (z +C w) (a + b)
boxAdd (r , i) (s , t) = Bounds.boundAdd r s , Bounds.boundAdd i t

boxScale : ∀ {a b z} → R.NonNegative a → Box z b → Box (scaleC a z) (a * b)
boxScale {a} an (r , i) =
  Bounds.boundMul (P.≤-reflexive (P.nonNegx⇒∣x∣≃x an)) r ,
  Bounds.boundMul (P.≤-reflexive (P.nonNegx⇒∣x∣≃x an)) i

boxFromNorm : ∀ z b → R.NonNegative b → Norm.normSqC z ≤ square b → Box z b
boxFromNorm z b bn bound =
  Reflect.squareReflectsOnNonnegative (P.nonNeg∣x∣ (C.re z)) bn
    (P.≤-respˡ-≃ (Norm.absoluteSquare (C.re z))
      (P.≤-trans (Norm.componentSquareBelowNormSqReal z) bound)) ,
  Reflect.squareReflectsOnNonnegative (P.nonNeg∣x∣ (C.im z)) bn
    (P.≤-respˡ-≃ (Norm.absoluteSquare (C.im z))
      (P.≤-trans (Norm.componentSquareBelowNormSqImag z) bound))

normSquareProductBound : ∀ z w a b → Norm.normSqC z ≤ a → Norm.normSqC w ≤ b →
  Norm.normSqC (z *C w) ≤ a * b
normSquareProductBound z w a b az bw =
  P.≤-respˡ-≃ (Norm.normSqMultiply z w) (P.*-mono-≤ (Inv.normNN z) (Inv.normNN w) az bw)

-- Once the signed geometric estimate pays the cross, the row tail
-- domination uses the actual scaled rational row (not its limit).
module TailCell (q : BishopComplex) (nz : Rec.BishopComplexNonzero (Row.gapMinus q))
  (h b B : ℝ) (hp : R._<_ R.0ℝ h) (hOne : h ≤ R.1ℝ)
  (bn : R.NonNegative b) (Bn : R.NonNegative B) (bB : b ≤ B)
  (qNorm : Norm.normSqC q ≤ R.1ℝ)
  (cross : square h ≤ b * Norm.normSqC (Row.gapMinus q)) where

  v = scaleC (R.- h) (Rec.reciprocalC (Row.gapMinus q) nz)
  Y = q *C Rat.square v
  X = Row.X q nz

  normV : Norm.normSqC v ≤ b
  normV = scaledInverseBound q nz h b hp bn cross

  normY : Norm.normSqC Y ≤ square b
  normY = P.≤-respʳ-≃ (P.*-identityˡ (square b))
    (normSquareProductBound q (Rat.square v) R.1ℝ (square b) qNorm
      (normSquareProductBound v v b b normV normV))

  yBox : Box Y b
  yBox = boxFromNorm Y b bn normY

  y2Box : Box (Rat.square Y) (square b)
  y2Box = boxFromNorm (Rat.square Y) (square b) (Sq.bishopSquareNonnegative b)
    (normSquareProductBound Y Y (square b) (square b) normY normY)

  y3Box : Box (Rat.cube Y) (b * square b)
  y3Box = boxFromNorm (Rat.cube Y) (b * square b)
    (P.nonNegx,y⇒nonNegx*y bn (Sq.bishopSquareNonnegative b))
    (P.≤-respʳ-≃
      (let open P.ℝ-Solver in solve 1
        (λ b → (b ⊗ b) ⊗ ((b ⊗ b) ⊗ (b ⊗ b)) ⊜
          (b ⊗ (b ⊗ b)) ⊗ (b ⊗ (b ⊗ b))) P.≃-refl b)
      (normSquareProductBound Y (Rat.square Y) (square b) (square (square b)) normY
        (normSquareProductBound Y Y (square b) (square b) normY normY)))

  hn = P.pos⇒nonNeg (P.0<x⇒posx hp)
  h2One : square h ≤ R.1ℝ
  h2One = P.≤-respʳ-≃ (P.*-identityˡ R.1ℝ) (squareMono hn hOne)
  h4One : S.fourthR h ≤ R.1ℝ
  h4One = P.≤-respʳ-≃ (P.*-identityˡ R.1ℝ)
    (squareMono (Sq.bishopSquareNonnegative h) h2One)

  boundedScale : ∀ a z c → R.NonNegative a → a ≤ R.1ℝ →
    R.NonNegative c → Box z c → Box (scaleC a z) c
  boundedScale a z c an a1 cn (r , i) =
    let raw = boxScale an (r , i)
        upper = P.≤-respʳ-≃ (P.*-identityˡ c) (P.*-monoʳ-≤-nonNeg a1 cn)
    in P.≤-trans (proj₁ raw) upper , P.≤-trans (proj₂ raw) upper

  yRead : Y ≈C scaleC (square h) X
  yRead = S.scaledX h q (Rec.reciprocalC (Row.gapMinus q) nz)

  row4Read : scaleC (S.fourthR h) (Row.P4 X) ≈C
    (scaleC (square h) Y +C Row.scale 6 (Rat.square Y))
  row4Read = complexTrans (S.scaled4Read h X)
    (A.addCCongruent (A.scaleCCongruent (complexSym yRead) (square h))
      (Row.scaleCong 6 (A.mulCCongruent (complexSym yRead) (complexSym yRead))))

  row6Read : scaleC (S.sixthR h) (Row.P6 X) ≈C
    ((scaleC (S.fourthR h) Y +C Row.scale 30 (scaleC (square h) (Rat.square Y)))
      +C Row.scale 120 (Rat.cube Y))
  row6Read =
    let eq = complexSym yRead
        sqEq = A.mulCCongruent eq eq
    in complexTrans (S.scaled6Read h X)
      (A.addCCongruent (A.addCCongruent (A.scaleCCongruent eq (S.fourthR h))
        (Row.scaleCong 30 (A.scaleCCongruent sqEq (square h))))
        (Row.scaleCong 120 (A.mulCCongruent eq sqEq)))

  sixNN : R.NonNegative ((+ 6 / 1) ⋆)
  sixNN = Bounds.ratNN (+ 6 / 1) (QP.nonNegative⁻¹ (+ 6 / 1))
  thirtyNN : R.NonNegative ((+ 30 / 1) ⋆)
  thirtyNN = Bounds.ratNN (+ 30 / 1) (QP.nonNegative⁻¹ (+ 30 / 1))
  oneTwentyNN : R.NonNegative ((+ 120 / 1) ⋆)
  oneTwentyNN = Bounds.ratNN (+ 120 / 1) (QP.nonNegative⁻¹ (+ 120 / 1))

  tail4 : Box (scaleC (S.fourthR h) (Row.P4 X))
    (b + ((+ 6 / 1) ⋆) * square b)
  tail4 = boxCong row4Read (boxAdd
    (boundedScale (square h) Y b (Sq.bishopSquareNonnegative h) h2One bn yBox)
    (boxScale sixNN y2Box))

  tail6 : Box (scaleC (S.sixthR h) (Row.P6 X))
    ((b + ((+ 30 / 1) ⋆) * square b) + ((+ 120 / 1) ⋆) * (b * square b))
  tail6 = boxCong row6Read
    (boxAdd (boxAdd
      (boundedScale (S.fourthR h) Y b (Sq.bishopSquareNonnegative (square h)) h4One bn yBox)
      (boxScale thirtyNN
        (boundedScale (square h) (Rat.square Y) (square b)
          (Sq.bishopSquareNonnegative h) h2One (Sq.bishopSquareNonnegative b) y2Box)))
      (boxScale oneTwentyNN y3Box))

  b2Upper : square b ≤ B * b
  b2Upper = P.*-monoʳ-≤-nonNeg bB bn

  b3Upper : b * square b ≤ square B * b
  b3Upper = P.≤-respˡ-≃ (P.≃-symm (P.*-assoc b b b))
    (P.*-monoʳ-≤-nonNeg (squareMono bn bB) bn)

  -- A single summable b=C/J² dominates every moving row, because
  -- higher powers are bounded by B*b and B²*b with fixed B.
  tail4Linear : Box (scaleC (S.fourthR h) (Row.P4 X))
    ((R.1ℝ + ((+ 6 / 1) ⋆) * B) * b)
  tail4Linear =
    let r , i = tail4
        le = P.≤-respʳ-≃
          (let open P.ℝ-Solver in solve 2
            (λ B b → b ⊕ Κ (+ 6 / 1) ⊗ (B ⊗ b)
              ⊜ (Κ 1ℚᵘ ⊕ Κ (+ 6 / 1) ⊗ B) ⊗ b) P.≃-refl B b)
          (P.+-mono-≤ P.≤-refl (P.*-monoˡ-≤-nonNeg b2Upper sixNN))
    in P.≤-trans r le , P.≤-trans i le


  tail6Linear : Box (scaleC (S.sixthR h) (Row.P6 X))
    (((R.1ℝ + ((+ 30 / 1) ⋆) * B) + ((+ 120 / 1) ⋆) * square B) * b)
  tail6Linear =
    let r , i = tail6
        le = P.≤-respʳ-≃
          (let open P.ℝ-Solver in solve 2
            (λ B b → (b ⊕ Κ (+ 30 / 1) ⊗ (B ⊗ b))
              ⊕ Κ (+ 120 / 1) ⊗ ((B ⊗ B) ⊗ b)
              ⊜ ((Κ 1ℚᵘ ⊕ Κ (+ 30 / 1) ⊗ B) ⊕ Κ (+ 120 / 1) ⊗ (B ⊗ B)) ⊗ b)
            P.≃-refl B b)
          (P.+-mono-≤ (P.+-mono-≤ P.≤-refl (P.*-monoˡ-≤-nonNeg b2Upper thirtyNN))
            (P.*-monoˡ-≤-nonNeg b3Upper oneTwentyNN))
    in P.≤-trans r le , P.≤-trans i le

-- Pay the inverse-square majorant using the actual lower gap, not a
-- caller-supplied abstract tail function. The same b is used at both
-- weights and is independent of the dyadic depth.
module CrossFromGap (q : BishopComplex) (nz : Rec.BishopComplexNonzero (Row.gapMinus q))
  (h rho0 J : ℝ) (hp : R._<_ R.0ℝ h) (hOne : h ≤ R.1ℝ)
  (rp : R._<_ R.0ℝ rho0) (jp : R._<_ R.0ℝ J) (jOne : R.1ℝ ≤ J)
  (qNorm : Norm.normSqC q ≤ R.1ℝ)
  (lower : (rho0 * square (h * J)) ≤ Norm.normSqC (Row.gapMinus q)) where
  a = rho0 * square J
  ap = Leaf.positiveProduct rp (Leaf.positiveProduct jp jp)
  b = Cross.positiveInverse ap
  B = Cross.positiveInverse rp
  bn = Cross.positiveInverseNonnegative ap
  Bn = Cross.positiveInverseNonnegative rp
  law = I.*-inverseʳ a (Cross.positiveNonzero ap)

  bB : b ≤ B
  bB = P.≤-respʳ-≃ (P.*-identityˡ B)
    (Cross.positiveCrossReciprocalUpper rp ap
      (P.≤-respʳ-≃ (P.≃-symm (P.*-identityˡ a))
        (P.≤-respˡ-≃ (P.≃-symm (P.*-identityʳ rho0))
          (P.*-monoˡ-≤-nonNeg
            (P.≤-respˡ-≃ (P.≃-symm (P.*-identityˡ R.1ℝ))
              (squareMono (P.pos⇒nonNeg (P.0<x⇒posx One.onePositive)) jOne))
            (P.pos⇒nonNeg (P.0<x⇒posx rp))))))

  cross : square h ≤ b * Norm.normSqC (Row.gapMinus q)
  cross =
    let raw = P.*-monoʳ-≤-nonNeg lower bn
        left = P.≃-trans
          (let open P.ℝ-Solver in solve 4
            (λ r h J b → (r ⊗ ((h ⊗ J) ⊗ (h ⊗ J))) ⊗ b
              ⊜ (h ⊗ h) ⊗ ((r ⊗ (J ⊗ J)) ⊗ b))
            P.≃-refl rho0 h J b)
          (P.≃-trans (P.*-congˡ law) (P.*-identityʳ (square h)))
    in P.≤-respʳ-≃ (P.*-comm (Norm.normSqC (Row.gapMinus q)) b)
      (P.≤-respˡ-≃ (P.≃-symm left) raw)

  jInv = Cross.positiveInverse (Leaf.positiveProduct jp jp)
  jInvRead : jInv ≃ InvSq.inverseSquare J (Cross.positiveNonzero jp)
  jInvRead = P.≃-symm (I.⁻¹-unique (InvSq.inverseSquare J (Cross.positiveNonzero jp))
    (square J) (Cross.positiveNonzero (Leaf.positiveProduct jp jp))
    (InvSq.inverseSquareCancelsSquare J (Cross.positiveNonzero jp)))

  bFactor : b ≃ B * InvSq.inverseSquare J (Cross.positiveNonzero jp)
  bFactor = P.≃-trans (InvProduct.inverseProduct rp (Leaf.positiveProduct jp jp))
    (P.*-congˡ jInvRead)

  module Paid = TailCell q nz h b B hp hOne bn Bn bB qNorm cross

-- Literal reciprocal-square integer weight. The existing Basel owner
-- supplies convergence for this very factor, not a synthetic power law.
module NaturalTail (q : BishopComplex) (nz : Rec.BishopComplexNonzero (Row.gapMinus q))
  (h rho0 : ℝ) (k : Nat) (hp : R._<_ R.0ℝ h) (hOne : h ≤ R.1ℝ)
  (rp : R._<_ R.0ℝ rho0)
  (jOne : R.1ℝ ≤ N.natReal (suc k))
  (qNorm : Norm.normSqC q ≤ R.1ℝ)
  (lower : (rho0 * square (h * N.natReal (suc k))) ≤
    Norm.normSqC (Row.gapMinus q)) where
  module Crossed = CrossFromGap q nz h rho0 (N.natReal (suc k))
    hp hOne rp (NP.natRealSuccessorStrictlyPositive k) jOne qNorm lower
  B = Crossed.B
  bRead : Crossed.b ≃ B * Basel.baselTerm k
  bRead = P.≃-trans Crossed.bFactor (P.*-congˡ (BaselRead.natRealSuccessorInverseSquareIsBaselTerm k))

  majorant4 : Box (scaleC (S.fourthR h) (Row.P4 (Row.X q nz)))
    (((R.1ℝ + ((+ 6 / 1) ⋆) * B) * B) * Basel.baselTerm k)
  majorant4 = boxBudget
    (P.≃-trans (P.*-congˡ bRead) (P.≃-symm (P.*-assoc (R.1ℝ + ((+ 6 / 1) ⋆) * B) B (Basel.baselTerm k))))
    Crossed.Paid.tail4Linear

  majorant6 : Box (scaleC (S.sixthR h) (Row.P6 (Row.X q nz)))
    ((((R.1ℝ + ((+ 30 / 1) ⋆) * B) + ((+ 120 / 1) ⋆) * square B) * B) * Basel.baselTerm k)
  majorant6 = boxBudget
    (P.≃-trans (P.*-congˡ bRead)
      (P.≃-symm (P.*-assoc ((R.1ℝ + ((+ 30 / 1) ⋆) * B) + ((+ 120 / 1) ⋆) * square B) B (Basel.baselTerm k))))
    Crossed.Paid.tail6Linear
