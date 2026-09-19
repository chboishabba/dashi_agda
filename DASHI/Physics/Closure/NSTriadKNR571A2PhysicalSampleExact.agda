module DASHI.Physics.Closure.NSTriadKNR571A2PhysicalSampleExact where

------------------------------------------------------------------------
-- PERIODIC B / R571 A2 FULL PHYSICAL SAMPLE
--
-- This discharges the two geometric premises left by
-- NSTriadKNR571A2SameDisplacementCompilerExact from the literal centered
-- physical data:
--
--   * centre radius >= 1 follows from radius^2 = |k|^2, radius >= 0 and the
--     canonical nonzero-mode unit-square floor;
--   * centered excess >= 0 follows from the exact aligned-complement product,
--     nonnegative angular mass, and strict positivity of the centered sum.
--
-- It also proves the preferred Taylor minus remainder is exactly the absolute
-- centered excess for BOTH helicity signs.  Therefore the existing physical
-- A2 geometry now constructs the actual Gate-A curvature sample with
--
--   stepMagnitude = |y|^2,
--   transportCurvature = 4.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; Positive; NonNegative; _+_; _*_; _≤_; _<_; ∣_∣; positive; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNNestedInnerHelicityRouteSplitRound311Exact as R311
import DASHI.Physics.Closure.NSTriadKNR571HomochiralRadialIncrementSpecializationExact as Weld
import DASHI.Physics.Closure.NSTriadKNR571HomochiralPairedSecondMomentRealizationExact as Pair
import DASHI.Physics.Closure.NSTriadKNR571CenteredShiftTriangleExcessExact as Shift
import DASHI.Physics.Closure.NSTriadKNR571CenteredShiftRadiusDoublingExact as Double
import DASHI.Physics.Closure.NSTriadKNR571CenteredAlignedComplementExact as Aligned
import DASHI.Physics.Closure.NSTriadKNR571CenteredRadialDenominatorOrderExact as Order
import DASHI.Physics.Closure.NSTriadKNR571CenteredRadialProductBridgeExact as Product
import DASHI.Physics.Closure.NSTriadKNR571GateAEnvelopeCrosswalkExact as GateA
import DASHI.Physics.Closure.NSTriadKNR571RadialCurvatureBoundaryExact as Boundary
import DASHI.Physics.Closure.NSTriadKNR571A2SameDisplacementCompilerExact as Compiler
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicMultiplierTaylorDifferenceExact as Taylor

two : ℚ
two = Product.two

nonnegativeSquareRootAtLeastOne :
  (r : ℚ) →
  0ℚ ≤ r →
  1ℚ ≤ r * r →
  1ℚ ≤ r
nonnegativeSquareRootAtLeastOne r rNN oneBelowSquare
  with ℚP.≤-total 1ℚ r
... | inj₁ oneBelowR = oneBelowR
... | inj₂ rBelowOne =
  let
    instance rNNI : NonNegative r
    rNNI = nonNegative rNN

    squareBelowRRaw : r * r ≤ r * 1ℚ
    squareBelowRRaw = ℚP.*-monoˡ-≤-nonNeg r rBelowOne

    squareBelowR : r * r ≤ r
    squareBelowR =
      subst
        (r * r ≤_)
        (ℚP.*-identityʳ r)
        squareBelowRRaw
  in
  ℚP.≤-trans oneBelowSquare squareBelowR

centerRadiusAtLeastOne :
  ∀ {E I S center displacement} →
  (D : Product.CenteredRadialA2Data E I S center displacement) →
  1ℚ ≤ C3.normSquared I center →
  1ℚ ≤ Helical.modeNorm S center
centerRadiusAtLeastOne {S = S} {center = center} D unitSquare =
  let
    R = Product.radiusDoubling D
    radius = Helical.modeNorm S center
    radiusNN = Double.centerRadiusNonnegative R
    squareMeaning = Double.centerCalibration R
  in
  nonnegativeSquareRootAtLeastOne
    radius radiusNN
    (subst
      (1ℚ ≤_)
      (sym (Double.R455.modeNormSquareMeaning squareMeaning))
      unitSquare)

centeredAngularMassNonnegative :
  ∀ {E I S center displacement} →
  (D : Product.CenteredRadialA2Data E I S center displacement) →
  let p = Shift.plusMode center displacement
      q = Shift.minusMode center displacement
  in
  0ℚ ≤
    (Helical.modeNorm S p * Helical.modeNorm S q)
      * Aligned.norm
          (Aligned.differenceVector
            (Aligned.R167.normalizedDirection E S p)
            (Aligned.R167.normalizedDirection E S q))
centeredAngularMassNonnegative D =
  let
    P = Product.physicalComplement D
    radiusProductNN = Aligned.R467.radiusProductNonnegative P
    vectorNN =
      Separation.complex3NormSquaredNonnegative
        (Aligned.differenceVector
          (Aligned.R167.normalizedDirection _ _ _)
          (Aligned.R167.normalizedDirection _ _ _))
  in
  Rational.productNonnegative radiusProductNN vectorNN

centeredSumPositive :
  ∀ {E I S center displacement} →
  (D : Product.CenteredRadialA2Data E I S center displacement) →
  1ℚ ≤ Helical.modeNorm S center →
  let p = Shift.plusMode center displacement
      q = Shift.minusMode center displacement
  in
  0ℚ <
    Order.centeredSum
      (Helical.modeNorm S p)
      (Helical.modeNorm S q)
      (Helical.modeNorm S center)
centeredSumPositive D centerFloor =
  let
    P = Product.physicalComplement D
    R = Product.radiusDoubling D
    rp = Helical.modeNorm _ (Shift.plusMode _ _)
    rq = Helical.modeNorm _ (Shift.minusMode _ _)
    rk = Helical.modeNorm _ _

    rpqNN : 0ℚ ≤ rp + rq
    rpqNN =
      Rational.addNonnegative
        (Aligned.R467.radiusPNN P)
        (Aligned.R467.radiusQNN P)

    onePositive : 0ℚ < 1ℚ
    onePositive = ℚP.positive⁻¹ 1ℚ

    rkPositive : 0ℚ < rk
    rkPositive = ℚP.<-≤-trans onePositive centerFloor

    twoPositive : 0ℚ < two
    twoPositive =
      ℚP.+-mono-<-< onePositive onePositive

    twoRkPositive : 0ℚ < two * rk
    twoRkPositive =
      let
        instance twoPI : Positive two
        twoPI = positive twoPositive
        instance rkPI : Positive rk
        rkPI = positive rkPositive
        instance productPI = ℚP.pos*pos⇒pos two rk
      in
      ℚP.positive⁻¹ (two * rk)

    sumPositiveRaw : 0ℚ < (rp + rq) + two * rk
    sumPositiveRaw =
      ℚP.≤-<-trans rpqNN
        (ℚP.+-monoˡ-< (rp + rq) twoRkPositive)
  in
  subst
    (0ℚ <_)
    (solve (rp ∷ rq ∷ rk ∷ []))
    sumPositiveRaw

centeredExcessNonnegative :
  ∀ {E I S center displacement} →
  (D : Product.CenteredRadialA2Data E I S center displacement) →
  (centerFloor : 1ℚ ≤ Helical.modeNorm S center) →
  let p = Shift.plusMode center displacement
      q = Shift.minusMode center displacement
  in
  0ℚ ≤
    Order.centeredExcess
      (Helical.modeNorm S p)
      (Helical.modeNorm S q)
      (Helical.modeNorm S center)
centeredExcessNonnegative {S = S} {center = center} {displacement = displacement}
    D centerFloor =
  let
    p = Shift.plusMode center displacement
    q = Shift.minusMode center displacement
    rp = Helical.modeNorm S p
    rq = Helical.modeNorm S q
    rk = Helical.modeNorm S center
    excess = Order.centeredExcess rp rq rk
    total = Order.centeredSum rp rq rk

    productAsAngular =
      Product.centeredClearedProductIsAlignedAngularMass D

    angularNN = centeredAngularMassNonnegative D

    productNN : 0ℚ ≤ excess * total
    productNN =
      subst
        (0ℚ ≤_)
        (sym productAsAngular)
        angularNN

    totalPositive : 0ℚ < total
    totalPositive = centeredSumPositive D centerFloor

    scaledZero : 0ℚ * total ≤ excess * total
    scaledZero =
      subst
        (_≤ excess * total)
        (sym (ℚP.*-zeroˡ total))
        productNN

    instance totalPI : Positive total
    totalPI = positive totalPositive
  in
  ℚP.*-cancelʳ-≤-pos total scaledZero

preferredMinusRemainderAbsoluteIsExcess :
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (center displacement : Z3.FourierMode) →
  (excessNN :
    0ℚ ≤
      Order.centeredExcess
        (Helical.modeNorm S (Shift.plusMode center displacement))
        (Helical.modeNorm S (Shift.minusMode center displacement))
        (Helical.modeNorm S center)) →
  ∣ Taylor.minusRemainder
      (GateA.preferredRadialTaylorPair
        sign S center
        (Shift.plusMode center displacement)
        (Shift.minusMode center displacement)) ∣
  ≡
  Order.centeredExcess
    (Helical.modeNorm S (Shift.plusMode center displacement))
    (Helical.modeNorm S (Shift.minusMode center displacement))
    (Helical.modeNorm S center)
preferredMinusRemainderAbsoluteIsExcess R311.plus S center displacement excessNN =
  let
    rp = Helical.modeNorm S (Shift.plusMode center displacement)
    rm = Helical.modeNorm S (Shift.minusMode center displacement)
    rk = Helical.modeNorm S center
    excess = Order.centeredExcess rp rm rk
    raw :
      Taylor.minusRemainder
        (GateA.preferredRadialTaylorPair
          R311.plus S center
          (Shift.plusMode center displacement)
          (Shift.minusMode center displacement))
      ≡ excess
    raw = solve (rp ∷ rm ∷ rk ∷ [])
  in
  trans
    (cong ∣_∣ raw)
    (ℚP.0≤p⇒∣p∣≡p excessNN)
preferredMinusRemainderAbsoluteIsExcess R311.minus S center displacement excessNN =
  let
    rp = Helical.modeNorm S (Shift.plusMode center displacement)
    rm = Helical.modeNorm S (Shift.minusMode center displacement)
    rk = Helical.modeNorm S center
    excess = Order.centeredExcess rp rm rk
    raw :
      Taylor.minusRemainder
        (GateA.preferredRadialTaylorPair
          R311.minus S center
          (Shift.plusMode center displacement)
          (Shift.minusMode center displacement))
      ≡ - excess
    raw = solve (rp ∷ rm ∷ rk ∷ [])
  in
  trans
    (cong ∣_∣ raw)
    (trans
      (ℚP.∣-p∣≡∣p∣ excess)
      (ℚP.0≤p⇒∣p∣≡p excessNN))

record PhysicalA2SampleData
    (E : C3.IntegerEmbedding Weld.F)
    (I : C3.ModeInverseSquare Weld.F E)
    (S : Helical.HelicalModeScalars Weld.F)
    (sign : R311.HelicitySign)
    (center displacement : Z3.FourierMode) : Set₁ where
  field
    physical : Product.CenteredRadialA2Data E I S center displacement
    centerSquareAtLeastOne : 1ℚ ≤ C3.normSquared I center
    displacementSquareAtLeastOne : 1ℚ ≤ C3.normSquared I displacement

open PhysicalA2SampleData public

physicalA2CompilerData :
  ∀ {E I S sign center displacement} →
  (D : PhysicalA2SampleData E I S sign center displacement) →
  Compiler.A2SameDisplacementData
    E I S sign center displacement (C3.normSquared I displacement)
physicalA2CompilerData {I = I} {S = S} {sign = sign}
    {center = center} {displacement = displacement} D =
  let
    P = physical D
    centerFloor =
      centerRadiusAtLeastOne P (centerSquareAtLeastOne D)
    excessNN =
      centeredExcessNonnegative P centerFloor
    d = C3.normSquared I displacement
    dNN = ℚP.≤-trans (ℚP.<⇒≤ (ℚP.positive⁻¹ 1ℚ))
            (displacementSquareAtLeastOne D)

    dBelowSquare : d ≤ d * d
    dBelowSquare =
      let instance dNNI : NonNegative d
          dNNI = nonNegative dNN
          scaled : d * 1ℚ ≤ d * d
          scaled = ℚP.*-monoˡ-≤-nonNeg d (displacementSquareAtLeastOne D)
      in subst (d ≤_) (ℚP.*-identityʳ d) scaled
  in
  record
    { Compiler.physical = P
    ; Compiler.centerRadiusAtLeastOne = centerFloor
    ; Compiler.centeredExcessNonnegative = excessNN
    ; Compiler.stepMagnitudeNonnegative = dNN
    ; Compiler.displacementSquareBelowStepSquare = dBelowSquare
    ; Compiler.minusRemainderIsCenteredExcess =
        preferredMinusRemainderAbsoluteIsExcess
          sign S center displacement excessNN
    }

physicalA2GateASample :
  ∀ {E I S sign center displacement} →
  PhysicalA2SampleData E I S sign center displacement →
  Boundary.R571PreferredRadialCurvatureSample
physicalA2GateASample D =
  Compiler.compileA2SameDisplacementSample (physicalA2CompilerData D)

r571A2PhysicalGateASampleClosed : Bool
r571A2PhysicalGateASampleClosed = true

r571A2TransportCurvatureConstantIsFour : Bool
r571A2TransportCurvatureConstantIsFour = true

r571A2StepMagnitudeIsPhysicalDisplacementSquare : Bool
r571A2StepMagnitudeIsPhysicalDisplacementSquare = true

clayPromotion : Bool
clayPromotion = false

r571A2PhysicalGateASampleClosedIsTrue :
  r571A2PhysicalGateASampleClosed ≡ true
r571A2PhysicalGateASampleClosedIsTrue = refl
