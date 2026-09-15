module DASHI.Physics.Closure.NSTriadKNR571CenteredAlignedComplementExact where

------------------------------------------------------------------------
-- R571 GATE-A / A2 CENTERED ALIGNED COMPLEMENT
--
-- Timestamp: 2026-09-15 AEST.
--
-- R467 proves the anti-parallel normalized complement
--
--   (r_p-r_q)^2 + r_p r_q ||P+Q||^2 = |p+q|^2.
--
-- This owner mirrors that proof on the SAME literal rational normalized
-- direction carrier and proves the aligned complement
--
--   (r_p-r_q)^2 + r_p r_q ||P-Q||^2 = |p-q|^2.
--
-- For the centered pair
--
--   p = k+y,
--   q = k-y,
--
-- we additionally prove p-q = 2y, hence
--
--   r_p r_q ||P-Q||^2 <= 4 |y|^2.
--
-- No square root, helical-basis angular formula, shell count, Schur step or
-- spacetime estimate is introduced.  This pays the aligned angular
-- second-moment leaf of A2; the ordered radial denominator / final uniform
-- curvature transport remain outside this owner.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer using (ℤ; _+_; _-_; _*_)
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNIntegerFourierModeAddExact as Add
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalOrderedTransferSquaredMajorantRound96Exact as R96
import DASHI.Physics.Closure.NSTriadKNRationalNormalizedDirectionUnitRound455Exact as R455
import DASHI.Physics.Closure.NSTriadKNMHDRadiusReciprocalToNormalizedDirectionRound464Exact as R464
import DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedAntiParallelComplementRound467Exact as R467
import DASHI.Physics.Closure.NSTriadKNR571CenteredShiftTriangleExcessExact as CenteredShift
import DASHI.Physics.Closure.NSTriadKNR571CenteredShiftRadiusDoublingExact as RadiusDouble
import DASHI.Physics.Plasma.MHDMagneticVectorPotentialHelicalObserverExact as MHD

module RingZ = NR IntRS.ring

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 1ℚ + 1ℚ

four : ℚ
four = two * two

norm : C3.Complex3 F → ℚ
norm = L2.complex3NormSquared

square : ℚ → ℚ
square x = x * x

rawCross : C3.Complex3 F → C3.Complex3 F → ℚ
rawCross = R179.realHermitianCross

differenceMode : Z3.FourierMode → Z3.FourierMode → Z3.FourierMode
differenceMode p q = Z3.addMode p (Z3.negateMode q)

differenceVector : C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
differenceVector u v = C3.complex3Add u (C3.complex3Negate v)

------------------------------------------------------------------------
-- 1. Generic exact difference polarization.
------------------------------------------------------------------------

differencePolarization :
  (u v : C3.Complex3 F) →
  norm (differenceVector u v)
  ≡ norm u + norm v - two * rawCross u v
differencePolarization
    (C3.complex3
      (C3.complex ux uxi) (C3.complex uy uyi) (C3.complex uz uzi))
    (C3.complex3
      (C3.complex vx vxi) (C3.complex vy vyi) (C3.complex vz vzi)) =
  solve
    ( ux ∷ uxi ∷ uy ∷ uyi ∷ uz ∷ uzi
    ∷ vx ∷ vxi ∷ vy ∷ vyi ∷ vz ∷ vzi ∷ [])

differenceModeVectorMeaning :
  (E : C3.IntegerEmbedding F) →
  (p q : Z3.FourierMode) →
  C3.modeVector E (differenceMode p q)
  ≡ differenceVector (C3.modeVector E p) (C3.modeVector E q)
differenceModeVectorMeaning E p q =
  trans
    (Algebra.modeVectorAdd E p (Z3.negateMode q))
    (cong
      (C3.complex3Add (C3.modeVector E p))
      (C3.modeVectorNegation E q))

rawDifferenceNormPolarization :
  ∀ {E I S p q k} →
  (D : R467.PhysicalNormalizedComplementData E I S p q k) →
  C3.normSquared I (differenceMode p q)
  ≡ C3.normSquared I p + C3.normSquared I q
      - two * rawCross (C3.modeVector E p) (C3.modeVector E q)
rawDifferenceNormPolarization {E} {I} {p = p} {q = q} D =
  trans
    (sym (R96.modeVectorNormSquaredMeaning E I (differenceMode p q)))
    (trans
      (cong norm (differenceModeVectorMeaning E p q))
      (trans
        (differencePolarization (C3.modeVector E p) (C3.modeVector E q))
        (cong₂
          (λ p2 q2 → p2 + q2
            - two * rawCross (C3.modeVector E p) (C3.modeVector E q))
          (R96.modeVectorNormSquaredMeaning E I p)
          (R96.modeVectorNormSquaredMeaning E I q))))

normalizedDifferencePolarization :
  ∀ {E I S p q k} →
  (D : R467.PhysicalNormalizedComplementData E I S p q k) →
  norm
    (differenceVector
      (R167.normalizedDirection E S p)
      (R167.normalizedDirection E S q))
  ≡ two
      - two *
        (Helical.inverseModeNorm S p * Helical.inverseModeNorm S q
          * rawCross (C3.modeVector E p) (C3.modeVector E q))
normalizedDifferencePolarization {E} {I} {S} {p} {q} D =
  trans
    (differencePolarization
      (R167.normalizedDirection E S p)
      (R167.normalizedDirection E S q))
    (trans
      (cong₂
        (λ p2 q2 → p2 + q2
          - two * rawCross
              (R167.normalizedDirection E S p)
              (R167.normalizedDirection E S q))
        (R455.normalizedDirectionUnit E I S p (R467.r455P D))
        (R455.normalizedDirectionUnit E I S q (R467.r455Q D)))
      (trans
        (cong
          (λ c → 1ℚ + 1ℚ - two * c)
          (R467.normalizedCrossMeaning D))
        (solve
          ( Helical.inverseModeNorm S p
          ∷ Helical.inverseModeNorm S q
          ∷ rawCross (C3.modeVector E p) (C3.modeVector E q)
          ∷ []))))

------------------------------------------------------------------------
-- 2. Literal aligned normalized-complement identity.
------------------------------------------------------------------------

physicalNormalizedAlignedComplementIdentity :
  ∀ {E I S p q k} →
  (D : R467.PhysicalNormalizedComplementData E I S p q k) →
  square (Helical.modeNorm S p - Helical.modeNorm S q)
    + (Helical.modeNorm S p * Helical.modeNorm S q)
      * norm
          (differenceVector
            (R167.normalizedDirection E S p)
            (R167.normalizedDirection E S q))
  ≡ C3.normSquared I (differenceMode p q)
physicalNormalizedAlignedComplementIdentity {E} {I} {S} {p} {q} D =
  let
    rp = Helical.modeNorm S p
    rq = Helical.modeNorm S q
    ip = Helical.inverseModeNorm S p
    iq = Helical.inverseModeNorm S q
    dot = rawCross (C3.modeVector E p) (C3.modeVector E q)

    angular = normalizedDifferencePolarization D

    regroupProduct :
      (rp * rq) * (two - two * (ip * iq * dot))
      ≡ two * (rp * rq) - two * ((rp * ip) * (rq * iq) * dot)
    regroupProduct = solve (rp ∷ rq ∷ ip ∷ iq ∷ dot ∷ [])

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

    normalizeCancelled :
      two * (1ℚ * 1ℚ * dot) ≡ two * dot
    normalizeCancelled = solve (dot ∷ [])

    cancelProduct :
      (rp * rq) * (two - two * (ip * iq * dot))
      ≡ two * (rp * rq) - two * dot
    cancelProduct =
      trans regroupProduct
        (cong
          (two * (rp * rq) -_)
          (trans cancelP (trans cancelQ normalizeCancelled)))

    rawDifference = rawDifferenceNormPolarization D

    radiiToRaw :
      C3.normSquared I (differenceMode p q)
      ≡ square rp + square rq - two * dot
    radiiToRaw =
      trans rawDifference
        (cong₂
          (λ p2 q2 → p2 + q2 - two * dot)
          (sym (R464.modeNormSquareMeaning (R467.squareP D)))
          (sym (R464.modeNormSquareMeaning (R467.squareQ D))))

    algebra :
      square (rp - rq) + (two * (rp * rq) - two * dot)
      ≡ square rp + square rq - two * dot
    algebra = solve (rp ∷ rq ∷ dot ∷ [])
  in
  trans
    (cong
      (λ angularMass → square (rp - rq) + (rp * rq) * angularMass)
      angular)
    (trans
      (cong (square (rp - rq) +_) cancelProduct)
      (trans algebra (sym radiiToRaw)))

scaledNormalizedAlignedDefectBelowDifferenceSquare :
  ∀ {E I S p q k} →
  (D : R467.PhysicalNormalizedComplementData E I S p q k) →
  (Helical.modeNorm S p * Helical.modeNorm S q)
    * norm
        (differenceVector
          (R167.normalizedDirection E S p)
          (R167.normalizedDirection E S q))
  ≤ C3.normSquared I (differenceMode p q)
scaledNormalizedAlignedDefectBelowDifferenceSquare {E = E} {S = S} {p = p} {q = q} D =
  let
    rp = Helical.modeNorm S p
    rq = Helical.modeNorm S q
    radial = square (rp - rq)
    angular = (rp * rq) * norm
      (differenceVector
        (R167.normalizedDirection E S p)
        (R167.normalizedDirection E S q))
    radialNN : 0ℚ ≤ radial
    radialNN = Rational.squareNonnegative (rp - rq)
    raised : angular ≤ radial + angular
    raised =
      subst
        (λ lower → lower ≤ radial + angular)
        (sym (ℚP.+-identityˡ angular))
        (ℚP.+-mono-≤ radialNN ℚP.≤-refl)
  in
  subst
    (angular ≤_)
    (physicalNormalizedAlignedComplementIdentity D)
    raised

------------------------------------------------------------------------
-- 3. Centered shift p=k+y, q=k-y gives p-q=2y and the exact 4|y|² payment.
------------------------------------------------------------------------

centeredDifferenceIsDoubledDisplacement :
  (center displacement : Z3.FourierMode) →
  differenceMode
    (CenteredShift.plusMode center displacement)
    (CenteredShift.minusMode center displacement)
  ≡ CenteredShift.doubledCenter displacement
centeredDifferenceIsDoubledDisplacement
    (Z3.mode kx ky kz) (Z3.mode yx yy yz) =
  Add.modeExt
    (RingZ.solve 2
      (λ k y → (((k + y) - (k - y)) , y + y))
      refl kx yx)
    (RingZ.solve 2
      (λ k y → (((k + y) - (k - y)) , y + y))
      refl ky yy)
    (RingZ.solve 2
      (λ k y → (((k + y) - (k - y)) , y + y))
      refl kz yz)

centeredDifferenceNormSquaredScalesByFour :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (center displacement : Z3.FourierMode) →
  C3.normSquared I
    (differenceMode
      (CenteredShift.plusMode center displacement)
      (CenteredShift.minusMode center displacement))
  ≡ four * C3.normSquared I displacement
centeredDifferenceNormSquaredScalesByFour E I center displacement =
  trans
    (cong (C3.normSquared I)
      (centeredDifferenceIsDoubledDisplacement center displacement))
    (RadiusDouble.doubledModeNormSquaredMeaning E I displacement)

centeredAlignedAngularSecondMomentPayment :
  ∀ {E I S center displacement} →
  (D : R467.PhysicalNormalizedComplementData E I S
    (CenteredShift.plusMode center displacement)
    (CenteredShift.minusMode center displacement)
    (CenteredShift.doubledCenter center)) →
  let p = CenteredShift.plusMode center displacement
      q = CenteredShift.minusMode center displacement
  in
  (Helical.modeNorm S p * Helical.modeNorm S q)
    * norm
        (differenceVector
          (R167.normalizedDirection E S p)
          (R167.normalizedDirection E S q))
  ≤ four * C3.normSquared I displacement
centeredAlignedAngularSecondMomentPayment
    {E} {I} {S} {center} {displacement} D =
  let
    p = CenteredShift.plusMode center displacement
    q = CenteredShift.minusMode center displacement
    angular =
      (Helical.modeNorm S p * Helical.modeNorm S q)
        * norm
            (differenceVector
              (R167.normalizedDirection E S p)
              (R167.normalizedDirection E S q))
  in
  subst
    (angular ≤_)
    (centeredDifferenceNormSquaredScalesByFour E I center displacement)
    (scaledNormalizedAlignedDefectBelowDifferenceSquare D)

------------------------------------------------------------------------
-- Status / firewall.
------------------------------------------------------------------------

r571A2LiteralAlignedComplementIdentityClosed : Bool
r571A2LiteralAlignedComplementIdentityClosed = true

r571A2CenteredAlignedAngularSecondMomentPaymentClosed : Bool
r571A2CenteredAlignedAngularSecondMomentPaymentClosed = true

r571A2UsesR467R455LiteralCarrier : Bool
r571A2UsesR467R455LiteralCarrier = true

r571A2UsesSquareRootAxiom : Bool
r571A2UsesSquareRootAxiom = false

r571A2OrderedRadialDenominatorPaymentClosed : Bool
r571A2OrderedRadialDenominatorPaymentClosed = false

r571A2UniformCurvatureEstimateClosed : Bool
r571A2UniformCurvatureEstimateClosed = false

r571A2ClosesR568 : Bool
r571A2ClosesR568 = false

r571A2LiteralAlignedComplementIdentityClosedIsTrue :
  r571A2LiteralAlignedComplementIdentityClosed ≡ true
r571A2LiteralAlignedComplementIdentityClosedIsTrue = refl

r571A2CenteredAlignedAngularSecondMomentPaymentClosedIsTrue :
  r571A2CenteredAlignedAngularSecondMomentPaymentClosed ≡ true
r571A2CenteredAlignedAngularSecondMomentPaymentClosedIsTrue = refl

r571A2UsesSquareRootAxiomIsFalse :
  r571A2UsesSquareRootAxiom ≡ false
r571A2UsesSquareRootAxiomIsFalse = refl

r571A2UniformCurvatureEstimateClosedIsFalse :
  r571A2UniformCurvatureEstimateClosed ≡ false
r571A2UniformCurvatureEstimateClosedIsFalse = refl
