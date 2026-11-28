module DASHI.Moonshine.JInvariantBishopCenteredDyadicTailGeometryExact where

-- Source-written, kernel pending. The tail sign is chosen by the integer
-- coordinate, not by deciding the sign of an arbitrary Bishop real.
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (ℤ; +_; -[1+_])
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Nat.Base as Nat using () renaming (_≤_ to _≤N_; _<_ to _<N_)
import Data.Nat.Properties as NP
open import Data.Rational.Unnormalised as Q using (_/_; 0ℚᵘ; 1ℚᵘ)
import Data.Rational.Unnormalised.Properties as QP
open import Relation.Nullary.Decidable.Core using (toWitness)
import Real as R
open R using (ℝ; _≃_; _≤_; _<_; _+_; _-_; _*_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopOriginalMachinAtanSmallPhaseExact as Bounds
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Analysis.BishopMachinZetaSequentialContinuityReducerExact as Eps
import DASHI.Foundations.BishopMachinPiRationalWindowExact as Pi
import DASHI.Foundations.BishopSqrtTwoThirdsMachinConstantExact as PiPos
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Foundations.BishopCubicTranslationIteratedExact as N
import DASHI.Foundations.BishopNatEmbeddingMonotoneExact as Mono
import DASHI.Foundations.BishopNegativeExponentialGlobalUnitIntervalExact as One
import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
import DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact as Codec
import DASHI.Moonshine.JInvariantBishopCenteredDyadicAddressExact as Addr
import DASHI.Moonshine.JInvariantBishopCenteredDyadicRowExact as Chart
import DASHI.Moonshine.JInvariantBishopCenteredDyadicSummandLimitExact as Leaf
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as D
import DASHI.Moonshine.JInvariantBishopDyadicRowTailMajorantExact as Tail
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as Radius
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as Disk
import DASHI.Moonshine.JInvariantBishopDyadicFourierRowExact as Row
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
import DASHI.Foundations.BishopSineCosineSetoidCongruenceExact as Trig
open Chart using (h; weight)

eighth : ℝ
eighth = (+ 1 / 8) ⋆
fiveEighth : ℝ
fiveEighth = (+ 5 / 8) ⋆
piUpper : ℝ
piUpper = (+ 22 / 7) ⋆

nn : ∀ {x} → R.0ℝ ≤ x → R.NonNegative x
nn = P.0≤x⇒nonNegx
posNN : ∀ {x} → R.0ℝ < x → R.NonNegative x
posNN p = nn (P.<⇒≤ p)

hOne : ∀ n → h n ≤ R.1ℝ
hOne n = Bounds.absUpper (Leaf.hSmall n)

-- h(suc n) * 2^n = 1/2, on the actual codec cardinal.
halfCard : ∀ n → h (suc n) * N.natReal (Codec.bitCardinality n) ≃ D.half
halfCard zero = let open P.ℝ-Solver in
  solve 0 ((Κ 1ℚᵘ ⊗ Κ (+ 1 / 2)) ⊗ Κ 1ℚᵘ ⊜ Κ (+ 1 / 2)) P.≃-refl
halfCard (suc n) =
  P.≃-trans (P.*-congˡ (N.natRealMul 2 (Codec.bitCardinality n)))
    (P.≃-trans
      (let open P.ℝ-Solver in solve 2
        (λ h c → (h ⊗ Κ (+ 1 / 2)) ⊗ (Κ (+ 2 / 1) ⊗ c) ⊜ h ⊗ c)
        P.≃-refl (h (suc n)) (N.natReal (Codec.bitCardinality n)))
      (halfCard n))

rangeBound : ∀ n J → J ≤N Codec.bitCardinality n →
  h (suc n) * N.natReal J ≤ D.half
rangeBound n J le = P.≤-respʳ-≃ (halfCard n)
  (P.*-monoˡ-≤-nonNeg (Mono.natRealMonotone le) (Leaf.hNN (suc n)))

-- Explicit depth cutoff from the existing dyadic null sequence.
smallShift : ∀ x → Σ Nat (λ d → ∀ m → d ≤N m → h m * ∣ x ∣ ≤ eighth)
smallShift x =
  let cv = Seq.xₙ→x∧x≃y⇒xₙ→y
        (Seq.xₙyₙ→x₀y₀ (R.0ℝ , Leaf.hNull)
          (∣ x ∣ , Power.constantConverges ∣ x ∣))
        (let open P.ℝ-Solver in solve 1 (λ x → Κ 0ℚᵘ ⊗ x ⊜ Κ 0ℚᵘ) P.≃-refl ∣ x ∣)
      cut = Seq.fast-ε-from-convergence (R.0ℝ , cv) eighth (Eps.reciprocalNatPositive 7)
  in proj₁ cut , λ m past → Bounds.absUpper
    (P.≤-respˡ-≃ (P.∣-∣-cong (P.≃-symm
      (let open P.ℝ-Solver in solve 1 (λ x → x ⊖ Κ 0ℚᵘ ⊜ x) P.≃-refl (h m * ∣ x ∣))))
      (P.<⇒≤ (proj₂ cut m past)))

-- Independent index cutoff: J >= 2 |x| ensures the sign of x+j is
-- determined by the signed integer j, including the boundary case.
largeIndex : ∀ x → Σ Nat (λ k → ∀ J → k ≤N J → D.two * ∣ x ∣ ≤ N.natReal J)
largeIndex x =
  let a = D.two * ∣ x ∣
      an = P.nonNegx,y⇒nonNegx*y Bounds.twoNN (P.nonNeg∣x∣ x)
      arch = P.archimedean-ℝ ∣ a ∣
  in suc (proj₁ arch) , λ J past →
    P.≤-trans (P.<⇒≤ (P.<-respˡ-≃ (P.nonNegx⇒∣x∣≃x an) (proj₂ arch)))
      (Mono.natRealMonotone past)

halfBelow : ∀ x J → D.two * ∣ x ∣ ≤ J → ∣ x ∣ ≤ D.half * J
halfBelow x J le =
  P.≤-respˡ-≃
    (let open P.ℝ-Solver in solve 1
      (λ x → x ⊜ Κ (+ 1 / 2) ⊗ (Κ (+ 2 / 1) ⊗ x)) P.≃-refl ∣ x ∣)
    (P.*-monoˡ-≤-nonNeg le Leaf.halfNN)

-- Both signed sheets reduce to one positive angle u. The argument x
-- here is x on the positive sheet and -x on the negative sheet.
module Angle (x J a : ℝ)
  (Jn : R.NonNegative J) (an : R.NonNegative a)
  (large : D.two * ∣ x ∣ ≤ J)
  (mesh : a * J ≤ D.half)
  (shiftSmall : a * ∣ x ∣ ≤ eighth) where
  v = a * (J + x)
  u = D.pi * v
  lowerX : R.- (D.half * J) ≤ x
  lowerX = Bounds.absLower (halfBelow x J large)

  halfJ : D.half * J ≤ J + x
  halfJ = P.≤-respˡ-≃
    (let open P.ℝ-Solver in solve 1
      (λ J → Κ (+ 1 / 2) ⊗ J ⊜ J ⊕ (⊝ (Κ (+ 1 / 2) ⊗ J))) P.≃-refl J)
    (P.+-mono-≤ P.≤-refl lowerX)

  lowerV : D.half * (a * J) ≤ v
  lowerV = P.≤-respˡ-≃
    (let open P.ℝ-Solver in solve 2
      (λ a J → Κ (+ 1 / 2) ⊗ (a ⊗ J) ⊜ a ⊗ (Κ (+ 1 / 2) ⊗ J)) P.≃-refl a J)
    (P.*-monoˡ-≤-nonNeg halfJ an)

  vn : R.NonNegative v
  vn = nn (P.≤-trans (P.nonNegx⇒0≤x
    (P.nonNegx,y⇒nonNegx*y Leaf.halfNN (P.nonNegx,y⇒nonNegx*y an Jn))) lowerV)

  upperV : v ≤ fiveEighth
  upperV = P.≤-respʳ-≃
    (let open P.ℝ-Solver in solve 0
      (Κ (+ 1 / 2) ⊕ Κ (+ 1 / 8) ⊜ Κ (+ 5 / 8)) P.≃-refl)
    (P.≤-respˡ-≃
      (let open P.ℝ-Solver in solve 3
        (λ a J x → a ⊗ (J ⊕ x) ⊜ a ⊗ J ⊕ a ⊗ x) P.≃-refl a J x)
      (P.+-mono-≤ mesh (P.≤-trans (P.*-monoˡ-≤-nonNeg P.x≤∣x∣ an) shiftSmall)))

  un : R.NonNegative u
  un = P.nonNegx,y⇒nonNegx*y (posNN PiPos.machinPiPositive) vn

  inside : ∣ u ∣ ≤ D.two
  inside = P.≤-respˡ-≃ (P.nonNegx⇒∣x∣≃x un)
    (P.≤-trans
      (P.*-mono-≤ (posNN PiPos.machinPiPositive) vn Pi.machinPiBelowTwentyTwoSeventhsNonStrict upperV)
      (P.≤-respˡ-≃
        (let open P.ℝ-Solver in solve 0 (Κ (+ 22 / 7) ⊗ Κ (+ 5 / 8) ⊜ Κ (+ 110 / 56)) P.≃-refl)
        (P.p≤q⇒p⋆≤q⋆ (+ 110 / 56) (+ 2 / 1) (toWitness {a? = QP._≤?_ (+ 110 / 56) (+ 2 / 1)} _))))
    -- rational upper: 22/7 * 5/8 = 110/56 < 2

  distance : a * J ≤ ((+ 2 / 3) ⋆) * u
  distance =
    let aj = a * J
        ajn = P.nonNegx,y⇒nonNegx*y an Jn
        raw = P.*-mono-≤ Bounds.threeNN
          (P.nonNegx,y⇒nonNegx*y Leaf.halfNN ajn)
          Pi.threeBelowMachinPiNonStrict lowerV
        scaled = P.*-monoˡ-≤-nonNeg raw (Bounds.ratNN (+ 2 / 3) (QP.nonNegative⁻¹ (+ 2 / 3)))
    in P.≤-respˡ-≃
      (let open P.ℝ-Solver in solve 1
        (λ aj → aj ⊜ Κ (+ 2 / 3) ⊗ (Κ (+ 3 / 1) ⊗ (Κ (+ 1 / 2) ⊗ aj)))
        P.≃-refl aj) scaled

module At (inputs : Round11.BishopCutset) (p : U.BishopUpperHalfPlanePoint) where
  module Rows = D.At inputs
  module T = Tail.At inputs
  x = C.re (U.tau p)
  y = C.im (U.tau p)
  a = Radius.qExponentMagnitude D.pi y
  ap = Radius.qExponentMagnitudePositive PiPos.machinPiPositive (U.imaginaryPositive p)
  rho0 = Radius.machinQRadius y
  rho0Positive = Radius.qRadiusPositive PiPos.machinPiPositive (U.imaginaryPositive p)
  rho0NN = posNN rho0Positive

  module Cell (m : Nat) (j : ℤ) where
    point = Leaf.scaledPoint p j m
    q = Rows.q point
    rho = Radius.machinQRadius (C.im (U.tau point))
    uRad = Radius.qExponentMagnitude D.pi (C.im (U.tau point))
    uRadPositive = Radius.qExponentMagnitudePositive PiPos.machinPiPositive (U.imaginaryPositive point)

    radialBound : uRad ≤ a
    radialBound = P.≤-respˡ-≃
      (let open P.ℝ-Solver in solve 3
        (λ pi h y → (Κ (+ 2 / 1) ⊗ pi) ⊗ (h ⊗ y) ⊜ h ⊗ ((Κ (+ 2 / 1) ⊗ pi) ⊗ y))
        P.≃-refl D.pi (h m) y)
      (P.≤-respʳ-≃ (P.*-identityˡ a)
        (P.*-monoʳ-≤-nonNeg (hOne m) (posNN ap)))

    radialFloor : rho0 ≤ rho
    radialFloor = Tail.negativeExpFloor a uRad (posNN ap) (posNN uRadPositive) radialBound

    normOne : Norm.normSqC q ≤ R.1ℝ
    normOne = P.≤-respˡ-≃ (Disk.normSquareAgreement (Rows.disk point))
      (P.≤-respʳ-≃ (P.*-identityˡ R.1ℝ)
        (Tail.squareMono (posNN (Radius.qRadiusPositive PiPos.machinPiPositive (U.imaginaryPositive point)))
          (P.<⇒≤ (Radius.qRadiusBelowOne PiPos.machinPiPositive (U.imaginaryPositive point)))))

    t = D.pi * C.re (U.tau point)
    doubleT : (D.two * D.pi) * C.re (U.tau point) ≃ t + t
    doubleT = let open P.ℝ-Solver in solve 2
      (λ pi x → (Κ (+ 2 / 1) ⊗ pi) ⊗ x ⊜ (pi ⊗ x) ⊕ (pi ⊗ x))
      P.≃-refl D.pi (C.re (U.tau point))

    phaseRead : C._≈C_ q (T.phase rho t)
    phaseRead =
      P.*-congˡ (Trig.bishopCosCongruent (Round11.concreteTermIdentification inputs) doubleT) ,
      P.*-congˡ (Trig.bishopSinCongruent (Round11.concreteTermIdentification inputs) doubleT)

    gapFromAngle : ∀ u J → R.NonNegative u → ∣ u ∣ ≤ D.two →
      (t ≃ u) ⊎ (t ≃ R.- u) →
      R.NonNegative J → h m * J ≤ ((+ 2 / 3) ⋆) * u →
      rho0 * Tail.square (h m * J) ≤ Norm.normSqC (Row.gapMinus q)
    gapFromAngle u J un inside sign Jn dist =
      P.≤-respʳ-≃ (P.≃-symm (D.normCong (D.gapCong phaseRead)))
        (T.gapLower rho rho0 t u (h m) J rho0NN radialFloor un inside sign
          (P.nonNegx,y⇒nonNegx*y (Leaf.hNN m) Jn) dist)
