module DASHI.Moonshine.CM163BishopHecke41ActualOrbitCoverExact where

-- SOURCE-WRITTEN / KERNEL PENDING. Original Machin exponential
-- supplies the radius shrink of the actual finite S/T orbit.
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
import Data.Rational.Unnormalised.Properties as QP
open import Relation.Nullary.Decidable.Core using (from-yes)
open import Data.Product.Base using (_,_)
import Real as R
open R using (ℝ; _≃_; _≤_; _<_; _+_; _-_; _*_; _⋆)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialPositiveOrderExact as Pos
import DASHI.Foundations.BishopExponentialNonnegativeMonotoneExact as Mono
import DASHI.Foundations.BishopExponentialSetoidCongruenceExact as Cong
import DASHI.Foundations.BishopExponentialCauchyProductExact as Product
import DASHI.Foundations.BishopNegativeExponentialGlobalUnitIntervalExact as Neg
import DASHI.Foundations.BishopMachinPiRationalWindowExact as Pi
import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as Radius
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as Disk
import DASHI.Moonshine.CM163BishopHecke41LocatedOrbitReductionExact as Reduce
import DASHI.Moonshine.CM163BishopHecke41QuantitativeRigidityExact as Rig
import DASHI.Moonshine.CM163BishopHecke41CuspContractionExact as Contract
import DASHI.Moonshine.CM163BishopHecke41UniformCuspBoundExact as Bound
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11

refHeight threshold gapBase : ℝ
refHeight = (+ 1 / 64) ⋆
threshold = (+ 19 / 10) ⋆
gapBase = (+ 61 / 192) ⋆

refPositive : R.0ℝ < refHeight
refPositive = P.p<q⇒p⋆<q⋆ 0ℚᵘ (+ 1 / 64) (from-yes (0ℚᵘ QP.<? (+ 1 / 64)))
reference : U.BishopUpperHalfPlanePoint
reference = U.bishop-upper-half-plane-point (C.complex R.0ℝ refHeight) refPositive

thresholdPos : R.0ℝ < threshold
thresholdPos = P.p<q⇒p⋆<q⋆ 0ℚᵘ (+ 19 / 10) (from-yes (0ℚᵘ QP.<? (+ 19 / 10)))
gapBaseNN : R.NonNegative gapBase
gapBaseNN = P.0≤x⇒nonNegx (P.p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ 61 / 192)
  (from-yes (0ℚᵘ QP.≤? (+ 61 / 192))))

-- Five nonnegative Taylor coefficients suffice. This is an exact
-- rational inequality, not a numerical exponential approximation.
prefixRead : Seq.SeriesOf (Exp.expTerm threshold) 5 ≃ ((+ 1533881 / 240000) ⋆)
prefixRead = let open P.ℝ-Solver in solve 0
  (((((Κ 0ℚᵘ ⊕ Κ 1ℚᵘ ⊗ Κ (+ 1 / 1))
     ⊕ (Κ 1ℚᵘ ⊗ Κ (+ 19 / 10)) ⊗ Κ (+ 1 / 1))
     ⊕ ((Κ 1ℚᵘ ⊗ Κ (+ 19 / 10)) ⊗ Κ (+ 19 / 10)) ⊗ Κ (+ 1 / 2))
     ⊕ (((Κ 1ℚᵘ ⊗ Κ (+ 19 / 10)) ⊗ Κ (+ 19 / 10)) ⊗ Κ (+ 19 / 10)) ⊗ Κ (+ 1 / 6))
     ⊕ ((((Κ 1ℚᵘ ⊗ Κ (+ 19 / 10)) ⊗ Κ (+ 19 / 10)) ⊗ Κ (+ 19 / 10)) ⊗ Κ (+ 19 / 10)) ⊗ Κ (+ 1 / 24)
     ⊜ Κ (+ 1533881 / 240000)) P.≃-refl

sixBelowExp : ((+ 6 / 1) ⋆) < Exp.bishopExp threshold
sixBelowExp = P.<-≤-trans
  (P.<-respʳ-≃ (P.≃-symm prefixRead)
    (P.p<q⇒p⋆<q⋆ (+ 6 / 1) (+ 1533881 / 240000)
      (from-yes ((+ 6 / 1) QP.<? (+ 1533881 / 240000)))))
  (Seq.xₙisIncreasing⇒xₙ≤limxₙ
    (Pos.expPartialSumsIncreasing (P.0≤x⇒nonNegx (P.<⇒≤ thresholdPos)))
    (Pos.expSeriesConvergent threshold) 5)

pi2 : ℝ
pi2 = Radius.two * Machin.bishopMachinPi

gap : U.BishopUpperHalfPlanePoint → ℝ
gap p = pi2 * (Reduce.y p - refHeight)

gapLower : ∀ p → Reduce.third ≤ Reduce.y p → threshold < gap p
gapLower p high =
  let d = Reduce.y p - refHeight
      h = P.≤-respˡ-≃ (let open P.ℝ-Solver in solve 0
            ((⊝ Κ (+ 1 / 64)) ⊕ Κ (+ 1 / 3) ⊜ Κ (+ 61 / 192)) P.≃-refl)
            (P.≤-respʳ-≃ (P.+-comm (R.- refHeight) (Reduce.y p))
              (P.+-monoʳ-≤ (R.- refHeight) high))
      piBound = P.*-monoʳ-≤-nonNeg Pi.threeBelowMachinPiNonStrict
        (P.0≤x⇒nonNegx (P.<⇒≤ Radius.twoPositive))
      six = P.≤-respˡ-≃ (let open P.ℝ-Solver in solve 0
              (Κ (+ 2 / 1) ⊗ Κ (+ 3 / 1) ⊜ Κ (+ 6 / 1)) P.≃-refl) piBound
      sixNN = P.0≤x⇒nonNegx (P.p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ 6 / 1)
        (from-yes (0ℚᵘ QP.≤? (+ 6 / 1))))
      mul = P.*-mono-≤ sixNN gapBaseNN six h
      rat = P.p<q⇒p⋆<q⋆ (+ 19 / 10) (+ 61 / 32)
        (from-yes ((+ 19 / 10) QP.<? (+ 61 / 32)))
  in P.<-≤-trans (P.<-respʳ-≃ (let open P.ℝ-Solver in solve 0
       (Κ (+ 61 / 32) ⊜ Κ (+ 6 / 1) ⊗ Κ (+ 61 / 192)) P.≃-refl) rat) mul

gapPositive : ∀ p → Reduce.third ≤ Reduce.y p → R.0ℝ < gap p
gapPositive p h = P.<-trans thresholdPos (gapLower p h)

-- Cross multiply the positive exponential lower bound. Its negative
-- partner is the original exponential, not a new reciprocal real.
gapDecay : ∀ p → Reduce.third ≤ Reduce.y p →
  Exp.bishopExp (R.- gap p) ≤ Contract.rho
gapDecay p high =
  let g = gap p
      z = Exp.bishopExp (R.- g)
      zpos = Neg.negativeExpPositive (gapPositive p high)
      expBound = P.<-≤-trans sixBelowExp
        (Mono.bishopExpMonotoneNonnegative (P.0≤x⇒nonNegx (P.<⇒≤ thresholdPos))
          (P.<⇒≤ (gapLower p high)))
      scaled = P.*-monoˡ-<-pos (P.0<x⇒posx zpos) expBound
      one = P.<-respʳ-≃ (Product.bishopExpTimesNegativeIsOne g) scaled
      rhoPos = P.0<x⇒posx (P.p<q⇒p⋆<q⋆ 0ℚᵘ (+ 1 / 6)
        (from-yes (0ℚᵘ QP.<? (+ 1 / 6))))
      small = P.*-monoʳ-<-pos rhoPos one
  in P.<⇒≤ (P.<-respˡ-≃ (let open P.ℝ-Solver in solve 1
       (λ z → Κ (+ 1 / 6) ⊗ (Κ (+ 6 / 1) ⊗ z) ⊜ z) P.≃-refl z)
       (P.<-respʳ-≃ (P.*-identityʳ Contract.rho) small))

radius : U.BishopUpperHalfPlanePoint → ℝ
radius p = Radius.machinQRadius (Reduce.y p)

radiusFactor : ∀ p → radius p ≃ (radius reference * Exp.bishopExp (R.- gap p))
radiusFactor p =
  P.≃-trans (Cong.bishopExpCongruent (let open P.ℝ-Solver in solve 3
    (λ a y h → ⊝ (a ⊗ y) ⊜ (⊝ (a ⊗ h)) ⊕ (⊝ (a ⊗ (y ⊖ h))))
    P.≃-refl pi2 (Reduce.y p) refHeight))
    (Product.bishopExpAdd (R.- (pi2 * refHeight)) (R.- gap p))

radiusNN : ∀ p → R.NonNegative (radius p)
radiusNN p = P.0≤x⇒nonNegx (P.<⇒≤ (Radius.qRadiusPositive
  (P.<-trans (P.p<q⇒p⋆<q⋆ 0ℚᵘ (+ 3 / 1) (from-yes (0ℚᵘ QP.<? (+ 3 / 1))))
    Pi.threeBelowMachinPi) (U.imaginaryPositive p)))

radiusBound : ∀ p → Reduce.third ≤ Reduce.y p →
  radius p ≤ (radius reference * Contract.rho)
radiusBound p h = P.≤-respˡ-≃ (P.≃-symm (radiusFactor p))
  (P.*-monoʳ-≤-nonNeg (gapDecay p h) (radiusNN reference))

module At (inputs : Round11.BishopCutset) where
  module R0 = Rig.At inputs
  module Ph = R0.Rm.Ph
  q = R0.q
  nz = R0.nz
  r = q reference

  normBound : ∀ p → Reduce.third ≤ Reduce.y p →
    Norm.normSqC (q p) ≤ ((Contract.rho * Contract.rho) * Norm.normSqC r)
  normBound p h =
    let b = radiusBound p h
        rr = radius reference
        rho = Contract.rho
        rearrange = let open P.ℝ-Solver in solve 2
          (λ r s → (r ⊗ s) ⊗ (r ⊗ s) ⊜ (s ⊗ s) ⊗ (r ⊗ r))
          P.≃-refl rr rho
    in P.≤-respˡ-≃ (P.≃-symm (Disk.normSquareAgreement (Ph.disk p)))
      (P.≤-respʳ-≃ (P.≃-trans rearrange
        (P.*-congˡ (P.≃-symm (Disk.normSquareAgreement (Ph.disk reference)))))
        (P.*-mono-≤ (radiusNN p) (radiusNN p) b b))

  inside : ∀ p → Reduce.third ≤ Reduce.y p → Norm.normSqC (q p) ≤ Norm.normSqC r
  inside p h = P.≤-trans (normBound p h)
    (P.≤-respʳ-≃ (P.*-identityˡ (Norm.normSqC r))
      (P.*-monoˡ-≤-nonNeg
        (P.≤-respˡ-≃ (let open P.ℝ-Solver in solve 0
          (Κ (+ 1 / 36) ⊜ Κ (+ 1 / 6) ⊗ Κ (+ 1 / 6)) P.≃-refl)
          (P.p≤q⇒p⋆≤q⋆ (+ 1 / 36) 1ℚᵘ (from-yes ((+ 1 / 36) QP.≤? 1ℚᵘ))))
        (Upper.normSquareNonnegative r)))

  small : ∀ p → Reduce.third ≤ Reduce.y p →
    Upper.BishopComplexNormSquareUpperRadius (Bound.relative (q p) r (nz reference)) Contract.rho
  small p h =
    let v = Rec.reciprocalC r (nz reference)
        nv = Norm.normSqC v
        rr = Norm.normSqC r
        s = Contract.rho * Contract.rho
        mul = P.*-monoˡ-≤-nonNeg (normBound p h) (Upper.normSquareNonnegative v)
        one = P.≃-trans (P.≃-symm (Norm.normSqMultiply r v))
          (P.≃-trans (Bound.normCong (Rec.multiplyReciprocal r (nz reference))) Norm.normSqOne)
    in record
      { radiusNonnegative = Contract.rhoNN
      ; normSqBelowRadiusSquare =
          P.≤-respˡ-≃ (P.≃-symm (Norm.normSqMultiply (q p) v))
            (P.≤-respʳ-≃ (P.≃-trans (P.*-assoc s rr nv)
              (P.≃-trans (P.*-congˡ one) (P.*-identityʳ s))) mul) }

  cover : R0.Cover reference
  cover p =
    let c = Reduce.reduce p
        v = Reduce.High.point c
        h = Reduce.High.height c
    in record { point = v ; word = Reduce.High.word c
              ; inside = inside v h ; small = small v h }

  -- The cover is now produced rather than passed as an argument.
  diagonalZero : R0.R0.R.W.UnitGate → R0.R0.R.W.DiagonalGate →
    ∀ p → C._≈C_ (R0.R0.d p) A.zeroC
  diagonalZero = R0.diagonalZero reference cover

  sliceZero : R0.R0.R.W.UnitGate → R0.R0.R.W.SliceGate →
    ∀ p → C._≈C_ (R0.R0.s p) A.zeroC
  sliceZero = R0.sliceZero reference cover
