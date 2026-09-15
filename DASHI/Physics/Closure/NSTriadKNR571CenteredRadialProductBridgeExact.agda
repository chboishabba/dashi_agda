module DASHI.Physics.Closure.NSTriadKNR571CenteredRadialProductBridgeExact where

------------------------------------------------------------------------
-- R571 GATE-A / A2 LITERAL CENTERED PRODUCT BRIDGE
--
-- This owner composes the already-written same-object geometry:
--
--   R467/R455 literal normalized radii,
--   R571 aligned P-Q complement,
--   centered p=k+y, q=k-y,
--   scalar radius doubling r_(2k)=2 r_k,
--   division-free radial-denominator order compiler.
--
-- It proves on that literal rational carrier
--
--   (r_p+r_q-2r_k)(r_p+r_q+2r_k)
--     = r_p r_q ||P-Q||^2
--     <= 4 |y|^2,
--
-- and therefore
--
--   r_k (r_p+r_q-2r_k) <= 4 |y|^2.
--
-- No division, annular lower bound, square-root axiom, shell count, Schur
-- majorant or spacetime estimate enters.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalOrderedTransferSquaredMajorantRound96Exact as R96
import DASHI.Physics.Closure.NSTriadKNMHDRadiusReciprocalToNormalizedDirectionRound464Exact as R464
import DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedAntiParallelComplementRound467Exact as R467
import DASHI.Physics.Closure.NSTriadKNR571RadialCurvatureSquareGapExact as SquareGap
import DASHI.Physics.Closure.NSTriadKNR571CenteredShiftTriangleExcessExact as CenteredShift
import DASHI.Physics.Closure.NSTriadKNR571CenteredShiftRadiusDoublingExact as RadiusDouble
import DASHI.Physics.Closure.NSTriadKNR571CenteredAlignedComplementExact as Aligned
import DASHI.Physics.Closure.NSTriadKNR571CenteredRadialDenominatorOrderExact as Order
import DASHI.Physics.Plasma.MHDMagneticVectorPotentialHelicalObserverExact as MHD

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 1ℚ + 1ℚ

four : ℚ
four = two * two

square : ℚ → ℚ
square value = value * value

norm : C3.Complex3 F → ℚ
norm = L2.complex3NormSquared

rawCross : C3.Complex3 F → C3.Complex3 F → ℚ
rawCross = R179.realHermitianCross

------------------------------------------------------------------------
-- 1. Expose the two exact scalar identities hidden inside the aligned proof.
------------------------------------------------------------------------

scaledNormalizedDifferenceIsAngularNumerator :
  ∀ {E I S p q k} →
  (D : R467.PhysicalNormalizedComplementData E I S p q k) →
  (Helical.modeNorm S p * Helical.modeNorm S q)
    * norm
        (Aligned.differenceVector
          (R167.normalizedDirection E S p)
          (R167.normalizedDirection E S q))
  ≡ SquareGap.angularDefectNumerator
      (Helical.modeNorm S p)
      (Helical.modeNorm S q)
      (rawCross (C3.modeVector E p) (C3.modeVector E q))
scaledNormalizedDifferenceIsAngularNumerator {E} {I} {S} {p} {q} D =
  let
    rp = Helical.modeNorm S p
    rq = Helical.modeNorm S q
    ip = Helical.inverseModeNorm S p
    iq = Helical.inverseModeNorm S q
    dot = rawCross (C3.modeVector E p) (C3.modeVector E q)

    polarization = Aligned.normalizedDifferencePolarization D

    regroup :
      (rp * rq) * (two - two * (ip * iq * dot))
      ≡ two * (rp * rq) - two * ((rp * ip) * (rq * iq) * dot)
    regroup = solve (rp ∷ rq ∷ ip ∷ iq ∷ dot ∷ [])

    cancelP :
      two * ((rp * ip) * (rq * iq) * dot)
      ≡ two * (1ℚ * (rq * iq) * dot)
    cancelP =
      cong
        (λ x → two * (x * (rq * iq) * dot))
        (MHD.radiusInverse (R467.reciprocalP D))

    cancelQ :
      two * (1ℚ * (rq * iq) * dot)
      ≡ two * (1ℚ * 1ℚ * dot)
    cancelQ =
      cong
        (λ x → two * (1ℚ * x * dot))
        (MHD.radiusInverse (R467.reciprocalQ D))
  in
  trans
    (cong ((rp * rq) *_) polarization)
    (trans
      regroup
      (trans
        (cong
          (two * (rp * rq) -_)
          (trans cancelP cancelQ))
        (solve (rp ∷ rq ∷ dot ∷ []))))

resonantRadiusSquarePolarization :
  ∀ {E I S p q k} →
  (D : R467.PhysicalNormalizedComplementData E I S p q k) →
  square (Helical.modeNorm S k)
  ≡ square (Helical.modeNorm S p)
      + square (Helical.modeNorm S q)
      + two * rawCross (C3.modeVector E p) (C3.modeVector E q)
resonantRadiusSquarePolarization {E} {I} {S} {p} {q} {k} D =
  trans
    (R464.modeNormSquareMeaning (R467.squareK D))
    (trans
      (R467.resonantRawNormPolarization D)
      (cong₂
        (λ p2 q2 → p2 + q2
          + two * rawCross (C3.modeVector E p) (C3.modeVector E q))
        (sym (R464.modeNormSquareMeaning (R467.squareP D)))
        (sym (R464.modeNormSquareMeaning (R467.squareQ D)))))

triangleExcessProductIsAlignedAngularMass :
  ∀ {E I S p q k} →
  (D : R467.PhysicalNormalizedComplementData E I S p q k) →
  SquareGap.triangleExcess
      (Helical.modeNorm S p) (Helical.modeNorm S q) (Helical.modeNorm S k)
    * SquareGap.triangleSum
      (Helical.modeNorm S p) (Helical.modeNorm S q) (Helical.modeNorm S k)
  ≡
  (Helical.modeNorm S p * Helical.modeNorm S q)
    * norm
        (Aligned.differenceVector
          (R167.normalizedDirection E S p)
          (R167.normalizedDirection E S q))
triangleExcessProductIsAlignedAngularMass {E} {I} {S} {p} {q} {k} D =
  let
    rp = Helical.modeNorm S p
    rq = Helical.modeNorm S q
    rk = Helical.modeNorm S k
    dot = rawCross (C3.modeVector E p) (C3.modeVector E q)
  in
  trans
    (SquareGap.triangleExcessTimesSumIsAngularDefectNumerator
      rp rq rk dot (resonantRadiusSquarePolarization D))
    (sym (scaledNormalizedDifferenceIsAngularNumerator D))

------------------------------------------------------------------------
-- 2. Centered same-object specialization and cleared-product budget.
------------------------------------------------------------------------

record CenteredRadialA2Data
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (center displacement : Z3.FourierMode) : Set where
  constructor centered-radial-a2-data
  field
    physicalComplement :
      R467.PhysicalNormalizedComplementData E I S
        (CenteredShift.plusMode center displacement)
        (CenteredShift.minusMode center displacement)
        (CenteredShift.doubledCenter center)
    radiusDoubling : RadiusDouble.CenteredShiftRadiusDoublingData E I S center

open CenteredRadialA2Data public

centeredClearedProductIsAlignedAngularMass :
  ∀ {E I S center displacement} →
  (D : CenteredRadialA2Data E I S center displacement) →
  let p = CenteredShift.plusMode center displacement
      q = CenteredShift.minusMode center displacement
      rP = Helical.modeNorm S p
      rQ = Helical.modeNorm S q
      rK = Helical.modeNorm S center
  in
  Order.centeredExcess rP rQ rK * Order.centeredSum rP rQ rK
  ≡
  (rP * rQ)
    * norm
        (Aligned.differenceVector
          (R167.normalizedDirection E S p)
          (R167.normalizedDirection E S q))
centeredClearedProductIsAlignedAngularMass {E} {I} {S} {center} {displacement} D =
  let
    p = CenteredShift.plusMode center displacement
    q = CenteredShift.minusMode center displacement
    rP = Helical.modeNorm S p
    rQ = Helical.modeNorm S q
    rK = Helical.modeNorm S center
    r2K = Helical.modeNorm S (CenteredShift.doubledCenter center)

    doubled = RadiusDouble.centeredShiftRadiusDoubles (radiusDoubling D)

    excessMeaning :
      Order.centeredExcess rP rQ rK
      ≡ SquareGap.triangleExcess rP rQ r2K
    excessMeaning =
      trans
        (solve (rP ∷ rQ ∷ rK ∷ []))
        (cong (λ x → rP + rQ - x) (sym doubled))

    sumMeaning :
      Order.centeredSum rP rQ rK
      ≡ SquareGap.triangleSum rP rQ r2K
    sumMeaning =
      trans
        (solve (rP ∷ rQ ∷ rK ∷ []))
        (cong (λ x → rP + rQ + x) (sym doubled))
  in
  trans
    (cong₂ _*_ excessMeaning sumMeaning)
    (triangleExcessProductIsAlignedAngularMass (physicalComplement D))

centeredClearedProductBelowFourDisplacementSquare :
  ∀ {E I S center displacement} →
  (D : CenteredRadialA2Data E I S center displacement) →
  let p = CenteredShift.plusMode center displacement
      q = CenteredShift.minusMode center displacement
      rP = Helical.modeNorm S p
      rQ = Helical.modeNorm S q
      rK = Helical.modeNorm S center
  in
  Order.centeredExcess rP rQ rK * Order.centeredSum rP rQ rK
  ≤ four * C3.normSquared I displacement
centeredClearedProductBelowFourDisplacementSquare {E} {I} {S} {center} {displacement} D =
  subst
    (_≤ four * C3.normSquared I displacement)
    (sym (centeredClearedProductIsAlignedAngularMass D))
    (Aligned.centeredAlignedAngularSecondMomentPayment (physicalComplement D))

centeredFourDisplacementSquareNonnegative :
  ∀ {E I} (displacement : Z3.FourierMode) →
  0ℚ ≤ four * C3.normSquared I displacement
centeredFourDisplacementSquareNonnegative {E} {I} displacement =
  Rational.productNonnegative
    (Rational.productNonnegative
      (Rational.addNonnegative Rational.oneNonnegative Rational.oneNonnegative)
      (Rational.addNonnegative Rational.oneNonnegative Rational.oneNonnegative))
    (R96.modeNormSquaredNonnegative E I displacement)

centeredRadialProductBudget :
  ∀ {E I S center displacement} →
  (D : CenteredRadialA2Data E I S center displacement) →
  let p = CenteredShift.plusMode center displacement
      q = CenteredShift.minusMode center displacement
  in
  Order.CenteredRadialProductBudget
centeredRadialProductBudget {E} {I} {S} {center} {displacement} D =
  let
    p = CenteredShift.plusMode center displacement
    q = CenteredShift.minusMode center displacement
    P = physicalComplement D
    R = radiusDoubling D
  in
  Order.centered-radial-product-budget
    (Helical.modeNorm S p)
    (Helical.modeNorm S q)
    (Helical.modeNorm S center)
    (four * C3.normSquared I displacement)
    (R467.radiusPNN P)
    (R467.radiusQNN P)
    (RadiusDouble.centerRadiusNonnegative R)
    (centeredFourDisplacementSquareNonnegative displacement)
    (centeredClearedProductBelowFourDisplacementSquare D)

centeredRadialCurvaturePayment :
  ∀ {E I S center displacement} →
  (D : CenteredRadialA2Data E I S center displacement) →
  let p = CenteredShift.plusMode center displacement
      q = CenteredShift.minusMode center displacement
      rP = Helical.modeNorm S p
      rQ = Helical.modeNorm S q
      rK = Helical.modeNorm S center
  in
  rK * Order.centeredExcess rP rQ rK
  ≤ four * C3.normSquared I displacement
centeredRadialCurvaturePayment D =
  Order.centeredRadialCurvatureFromClearedProduct
    (centeredRadialProductBudget D)

------------------------------------------------------------------------
-- Status / firewall.
------------------------------------------------------------------------

r571A2LiteralCenteredProductBridgeClosed : Bool
r571A2LiteralCenteredProductBridgeClosed = true

r571A2DivisionFreeRadialCurvaturePaymentClosed : Bool
r571A2DivisionFreeRadialCurvaturePaymentClosed = true

r571A2UsesAnnularLowerBound : Bool
r571A2UsesAnnularLowerBound = false

r571A2UsesRadiusDivision : Bool
r571A2UsesRadiusDivision = false

r571A2UsesSquareRootAxiom : Bool
r571A2UsesSquareRootAxiom = false

r571A2ClosesR568 : Bool
r571A2ClosesR568 = false

r571A2LiteralCenteredProductBridgeClosedIsTrue :
  r571A2LiteralCenteredProductBridgeClosed ≡ true
r571A2LiteralCenteredProductBridgeClosedIsTrue = refl

r571A2DivisionFreeRadialCurvaturePaymentClosedIsTrue :
  r571A2DivisionFreeRadialCurvaturePaymentClosed ≡ true
r571A2DivisionFreeRadialCurvaturePaymentClosedIsTrue = refl

r571A2UsesAnnularLowerBoundIsFalse :
  r571A2UsesAnnularLowerBound ≡ false
r571A2UsesAnnularLowerBoundIsFalse = refl

r571A2UsesRadiusDivisionIsFalse :
  r571A2UsesRadiusDivision ≡ false
r571A2UsesRadiusDivisionIsFalse = refl
