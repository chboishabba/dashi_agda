module DASHI.Physics.Closure.NSTriadKNR571A1SameDisplacementExact where

------------------------------------------------------------------------
-- PERIODIC B / R571 A1 ON THE SAME LITERAL SECOND-MOMENT DISPLACEMENT
--
-- The periodic state-side theorem now uses
--
--   d(y) = |y|^2
--
-- as its displacement scalar, and the physical A2 sample uses the same d(y).
-- This owner closes A1 on that SAME coordinate.
--
-- For p = k+y and q = k, the existing R571 aligned-complement identity gives
--
--   (r_p-r_q)^2 + r_p r_q ||P-Q||^2 = |p-q|^2 = |y|^2.
--
-- The angular term is nonnegative on the literal calibrated rational carrier,
-- hence
--
--   (r_{k+y}-r_k)^2 <= |y|^2.
--
-- If y is nonzero then d(y)=|y|^2 >= 1.  Therefore d <= d^2, and the
-- repository's constructive nonnegative-square order reflection yields
--
--   |r_{k+y}-r_k| <= d(y).
--
-- The preferred Taylor linear model is exactly +/- this radial gap for the two
-- homochiral signs, so the Gate-A first-order constant is A1 = 1.  No square
-- root, frequency differentiability, shell count, fibre cardinality, or
-- cutoff-dependent constant is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer using (ℤ; _+_; _-_; _*_)
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; ∣_∣; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNIntegerFourierModeAddExact as Add
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNNestedInnerHelicityRouteSplitRound311Exact as R311
import DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedAntiParallelComplementRound467Exact as R467
import DASHI.Physics.Closure.NSTriadKNR571CenteredAlignedComplementExact as Aligned
import DASHI.Physics.Closure.NSTriadKNR571CenteredShiftTriangleExcessExact as Shift
import DASHI.Physics.Closure.NSTriadKNR571GateAEnvelopeCrosswalkExact as GateA
import DASHI.Physics.Closure.NSTriadKNR571HomochiralPairedSecondMomentRealizationExact as Pair
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicMultiplierTaylorDifferenceExact as Taylor
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanStrongCouplingLiteralQuaternionScalarBudgetExact as Strong

module RingZ = NR IntRS.ring

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- 1. The one-sided centered difference mode is literally y.
------------------------------------------------------------------------

oneStepDifferenceIsDisplacement :
  (center displacement : Z3.FourierMode) →
  Aligned.differenceMode
    (Shift.plusMode center displacement)
    center
  ≡ displacement
oneStepDifferenceIsDisplacement
    (Z3.mode kx ky kz) (Z3.mode yx yy yz) =
  Add.modeExt
    (RingZ.solve 2
      (λ k y → (((k + y) - k) , y))
      refl kx yx)
    (RingZ.solve 2
      (λ k y → (((k + y) - k) , y))
      refl ky yy)
    (RingZ.solve 2
      (λ k y → (((k + y) - k) , y))
      refl kz yz)

------------------------------------------------------------------------
-- 2. Aligned complement drops its nonnegative angular mass.
------------------------------------------------------------------------

radialGapSquareBelowDifferenceSquare :
  ∀ {E I S p q output} →
  (D : R467.PhysicalNormalizedComplementData E I S p q output) →
  (Helical.modeNorm S p - Helical.modeNorm S q)
    * (Helical.modeNorm S p - Helical.modeNorm S q)
  ≤ C3.normSquared I (Aligned.differenceMode p q)
radialGapSquareBelowDifferenceSquare {E} {I} {S} {p} {q} D =
  let
    rp = Helical.modeNorm S p
    rq = Helical.modeNorm S q
    radial = (rp - rq) * (rp - rq)
    angular =
      (rp * rq)
        * L2.complex3NormSquared
            (Aligned.differenceVector
              (R167.normalizedDirection E S p)
              (R167.normalizedDirection E S q))

    angularNN : 0ℚ ≤ angular
    angularNN =
      Rational.productNonnegative
        (R467.radiusProductNonnegative D)
        (Separation.complex3NormSquaredNonnegative
          (Aligned.differenceVector
            (R167.normalizedDirection E S p)
            (R167.normalizedDirection E S q)))

    raised : radial ≤ radial + angular
    raised =
      subst
        (λ lower → lower ≤ radial + angular)
        (ℚP.+-identityʳ radial)
        (ℚP.+-monoʳ-≤ radial angularNN)
  in
  subst
    (radial ≤_)
    (Aligned.physicalNormalizedAlignedComplementIdentity D)
    raised

oneStepRadialGapSquareBelowDisplacementSquare :
  ∀ {E I S center displacement output} →
  (D : R467.PhysicalNormalizedComplementData E I S
    (Shift.plusMode center displacement) center output) →
  (Helical.modeNorm S (Shift.plusMode center displacement)
      - Helical.modeNorm S center)
    * (Helical.modeNorm S (Shift.plusMode center displacement)
      - Helical.modeNorm S center)
  ≤ C3.normSquared I displacement
oneStepRadialGapSquareBelowDisplacementSquare
    {I = I} {center = center} {displacement = displacement} D =
  subst
    (λ mode →
      (Helical.modeNorm _ (Shift.plusMode center displacement)
        - Helical.modeNorm _ center)
      * (Helical.modeNorm _ (Shift.plusMode center displacement)
        - Helical.modeNorm _ center)
      ≤ C3.normSquared I mode)
    (oneStepDifferenceIsDisplacement center displacement)
    (radialGapSquareBelowDifferenceSquare D)

------------------------------------------------------------------------
-- 3. Since d=|y|^2 >= 1, square control implies |radial gap| <= d.
------------------------------------------------------------------------

absoluteRadialGapBelowSquaredDisplacement :
  ∀ {E I S center displacement output} →
  (D : R467.PhysicalNormalizedComplementData E I S
    (Shift.plusMode center displacement) center output) →
  1ℚ ≤ C3.normSquared I displacement →
  ∣ Helical.modeNorm S (Shift.plusMode center displacement)
      - Helical.modeNorm S center ∣
  ≤ C3.normSquared I displacement
absoluteRadialGapBelowSquaredDisplacement
    {I = I} {S = S} {center = center} {displacement = displacement}
    D oneBelowD =
  let
    gap =
      Helical.modeNorm S (Shift.plusMode center displacement)
        - Helical.modeNorm S center
    d = C3.normSquared I displacement

    gapSquareBelowD : gap * gap ≤ d
    gapSquareBelowD =
      oneStepRadialGapSquareBelowDisplacementSquare D

    dNN : 0ℚ ≤ d
    dNN =
      ℚP.≤-trans
        (ℚP.<⇒≤ (ℚP.positive⁻¹ 1ℚ))
        oneBelowD

    dBelowSquare : d ≤ d * d
    dBelowSquare =
      let
        instance dNNI = nonNegative dNN
        scaled : d * 1ℚ ≤ d * d
        scaled = ℚP.*-monoˡ-≤-nonNeg d oneBelowD
      in
      subst
        (d ≤_)
        (ℚP.*-identityʳ d)
        scaled

    absSquare : ∣ gap ∣ * ∣ gap ∣ ≡ gap * gap
    absSquare = Schur.absoluteSquareExact gap

    squareBound : ∣ gap ∣ * ∣ gap ∣ ≤ d * d
    squareBound =
      subst
        (λ lower → lower ≤ d * d)
        (sym absSquare)
        (ℚP.≤-trans gapSquareBelowD dBelowSquare)
  in
  Strong.nonnegativeSquareReflectsOrder
    ∣ gap ∣ d
    (ℚP.0≤∣p∣ gap)
    dNN
    squareBound

------------------------------------------------------------------------
-- 4. The preferred homochiral Taylor linear model has the same magnitude.
------------------------------------------------------------------------

preferredLinearMagnitudeIsRadialGap :
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars F) →
  (center displacement : Z3.FourierMode) →
  ∣ GateA.preferredLinearModel
      sign S center (Shift.plusMode center displacement) ∣
  ≡
  ∣ Helical.modeNorm S (Shift.plusMode center displacement)
      - Helical.modeNorm S center ∣
preferredLinearMagnitudeIsRadialGap
    R311.plus S center displacement =
  cong ∣_∣
    (solve
      ( Helical.modeNorm S (Shift.plusMode center displacement)
      ∷ Helical.modeNorm S center
      ∷ []))
preferredLinearMagnitudeIsRadialGap
    R311.minus S center displacement =
  let
    gap =
      Helical.modeNorm S (Shift.plusMode center displacement)
        - Helical.modeNorm S center
    signed :
      GateA.preferredLinearModel
        R311.minus S center (Shift.plusMode center displacement)
      ≡ - gap
    signed =
      solve
        ( Helical.modeNorm S (Shift.plusMode center displacement)
        ∷ Helical.modeNorm S center
        ∷ [])
  in
  trans
    (cong ∣_∣ signed)
    (ℚP.∣-p∣≡∣p∣ gap)

preferredLinearIncrementMagnitudeBound :
  ∀ {E I S sign center displacement output} →
  (D : R467.PhysicalNormalizedComplementData E I S
    (Shift.plusMode center displacement) center output) →
  1ℚ ≤ C3.normSquared I displacement →
  ∣ Taylor.linearIncrement
      (GateA.preferredRadialTaylorPair
        sign S center
        (Shift.plusMode center displacement)
        (Shift.minusMode center displacement)) ∣
  ≤ C3.normSquared I displacement
preferredLinearIncrementMagnitudeBound
    {I = I} {S = S} {sign = sign}
    {center = center} {displacement = displacement}
    D oneBelowD =
  subst
    (_≤ C3.normSquared I displacement)
    (sym
      (trans
        (cong ∣_∣
          (GateA.preferredLinearIncrementIsPlusRadialDifference
            sign S center
            (Shift.plusMode center displacement)
            (Shift.minusMode center displacement)))
        (preferredLinearMagnitudeIsRadialGap
          sign S center displacement)))
    (absoluteRadialGapBelowSquaredDisplacement D oneBelowD)

------------------------------------------------------------------------
-- 5. Status.
------------------------------------------------------------------------

r571A1SameSquaredDisplacementClosed : Bool
r571A1SameSquaredDisplacementClosed = true

r571A1TransportGradientConstantIsOne : Bool
r571A1TransportGradientConstantIsOne = true

r571A1UsesFrequencyDifferentiability : Bool
r571A1UsesFrequencyDifferentiability = false

r571A1UsesSquareRootAxiom : Bool
r571A1UsesSquareRootAxiom = false

r571A1UsesCutoffDependentConstant : Bool
r571A1UsesCutoffDependentConstant = false

r571A1SameSquaredDisplacementClosedIsTrue :
  r571A1SameSquaredDisplacementClosed ≡ true
r571A1SameSquaredDisplacementClosedIsTrue = refl
