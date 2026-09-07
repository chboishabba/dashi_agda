module DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedAntiParallelComplementRound467Exact where

------------------------------------------------------------------------
-- ROUND467 / LITERAL NORMALIZED DIRECTIONS -> HH COMPLEMENT GEOMETRY
--
-- This owner closes the same-object geometry seam shared by R177 and R431.
-- No helical-basis angular formula is imported.  Instead we use only:
--
--   * literal Fourier mode-vector additivity;
--   * R179 exact rational C3 polarization;
--   * R455 unit norm of normalized directions;
--   * R464 square calibration;
--   * the existing MHD reciprocal-radius law.
--
-- For p+q=k, with
--
--   P = p / r_p,  Q = q / r_q,
--
-- we prove exactly
--
--   (r_p-r_q)^2 + r_p r_q ||P+Q||^2 = r_k^2.
--
-- Hence, because the radial-gap square is nonnegative,
--
--   r_p r_q ||P+Q||^2 <= r_k^2.
--
-- This is precisely the previously uninhabited normalized-defect geometry
-- required by R431 and the complement field required by R177.  No square root,
-- scalar cancellation from a vector equality, angle partition, or external
-- Waleffe-coordinate formula is used here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNHHAntiParallelQuadraticKernelNormRound174Exact as R174
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalOrderedTransferSquaredMajorantRound96Exact as R96
import DASHI.Physics.Closure.NSTriadKNRationalNormalizedDirectionUnitRound455Exact as R455
import DASHI.Physics.Closure.NSTriadKNMHDRadiusReciprocalToNormalizedDirectionRound464Exact as R464
import DASHI.Physics.Plasma.MHDMagneticVectorPotentialHelicalObserverExact as MHD

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 1ℚ + 1ℚ

norm : C3.Complex3 F → ℚ
norm = L2.complex3NormSquared

square : ℚ → ℚ
square x = x * x

rawCross : C3.Complex3 F → C3.Complex3 F → ℚ
rawCross = R179.realHermitianCross

realHermitianCrossRealScale :
  (a b : ℚ) (u v : C3.Complex3 F) →
  rawCross
    (C3.complex3Scale (C3.realEmbed F a) u)
    (C3.complex3Scale (C3.realEmbed F b) v)
  ≡ a * b * rawCross u v
realHermitianCrossRealScale a b
    (C3.complex3
      (C3.complex ux uxi) (C3.complex uy uyi) (C3.complex uz uzi))
    (C3.complex3
      (C3.complex vx vxi) (C3.complex vy vyi) (C3.complex vz vzi)) =
  solve
    ( a ∷ b
    ∷ ux ∷ uxi ∷ uy ∷ uyi ∷ uz ∷ uzi
    ∷ vx ∷ vxi ∷ vy ∷ vyi ∷ vz ∷ vzi ∷ [])

record PhysicalNormalizedComplementData
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (p q k : Z3.FourierMode) : Set where
  constructor physical-normalized-complement-data
  field
    resonance : Z3.Resonance p q k
    squareP : R464.RationalModeSquareCalibration E I S p
    squareQ : R464.RationalModeSquareCalibration E I S q
    squareK : R464.RationalModeSquareCalibration E I S k
    reciprocalP : MHD.ModeRadiusCalibration S p
    reciprocalQ : MHD.ModeRadiusCalibration S q
    reciprocalK : MHD.ModeRadiusCalibration S k

    radiusPNN : 0ℚ ≤ Helical.modeNorm S p
    radiusQNN : 0ℚ ≤ Helical.modeNorm S q
    radiusKNN : 0ℚ ≤ Helical.modeNorm S k

open PhysicalNormalizedComplementData public

r455P :
  ∀ {E I S p q k} →
  PhysicalNormalizedComplementData E I S p q k →
  R455.RationalModeRadiusCalibration E I S p
r455P {E} {I} {S} {p} D =
  R464.mhdReciprocalAndSquareBuildR455 E I S p
    (squareP D) (reciprocalP D)

r455Q :
  ∀ {E I S p q k} →
  PhysicalNormalizedComplementData E I S p q k →
  R455.RationalModeRadiusCalibration E I S q
r455Q {E} {I} {S} {q} D =
  R464.mhdReciprocalAndSquareBuildR455 E I S q
    (squareQ D) (reciprocalQ D)

r455K :
  ∀ {E I S p q k} →
  PhysicalNormalizedComplementData E I S p q k →
  R455.RationalModeRadiusCalibration E I S k
r455K {E} {I} {S} {k} D =
  R464.mhdReciprocalAndSquareBuildR455 E I S k
    (squareK D) (reciprocalK D)

resonantRawNormPolarization :
  ∀ {E I S p q k} →
  (D : PhysicalNormalizedComplementData E I S p q k) →
  C3.normSquared I k
  ≡ C3.normSquared I p + C3.normSquared I q
      + two * rawCross (C3.modeVector E p) (C3.modeVector E q)
resonantRawNormPolarization {E} {I} {p = p} {q = q} {k = k} D =
  trans
    (sym (R96.modeVectorNormSquaredMeaning E I k))
    (trans
      (cong norm
        (trans
          (cong (C3.modeVector E) (sym (Z3.Resonance.closes (resonance D))))
          (Algebra.modeVectorAdd E p q)))
      (trans
        (R179.complex3Polarization (C3.modeVector E p) (C3.modeVector E q))
        (cong₂
          (λ p2 q2 → p2 + q2
            + two * rawCross (C3.modeVector E p) (C3.modeVector E q))
          (R96.modeVectorNormSquaredMeaning E I p)
          (R96.modeVectorNormSquaredMeaning E I q))))

normalizedCrossMeaning :
  ∀ {E I S p q k} →
  (D : PhysicalNormalizedComplementData E I S p q k) →
  rawCross
    (R167.normalizedDirection E S p)
    (R167.normalizedDirection E S q)
  ≡ Helical.inverseModeNorm S p * Helical.inverseModeNorm S q
      * rawCross (C3.modeVector E p) (C3.modeVector E q)
normalizedCrossMeaning {E} {S} {p} {q} D =
  realHermitianCrossRealScale
    (Helical.inverseModeNorm S p)
    (Helical.inverseModeNorm S q)
    (C3.modeVector E p)
    (C3.modeVector E q)

normalizedDefectPolarization :
  ∀ {E I S p q k} →
  (D : PhysicalNormalizedComplementData E I S p q k) →
  norm
    (C3.complex3Add
      (R167.normalizedDirection E S p)
      (R167.normalizedDirection E S q))
  ≡ two
      + two *
        (Helical.inverseModeNorm S p * Helical.inverseModeNorm S q
          * rawCross (C3.modeVector E p) (C3.modeVector E q))
normalizedDefectPolarization {E} {I} {S} {p} {q} D =
  trans
    (R179.complex3Polarization
      (R167.normalizedDirection E S p)
      (R167.normalizedDirection E S q))
    (trans
      (cong₂
        (λ p2 q2 → p2 + q2
          + two * rawCross
              (R167.normalizedDirection E S p)
              (R167.normalizedDirection E S q))
        (R455.normalizedDirectionUnit E I S p (r455P D))
        (R455.normalizedDirectionUnit E I S q (r455Q D)))
      (trans
        (cong
          (λ c → 1ℚ + 1ℚ + two * c)
          (normalizedCrossMeaning D))
        (solve
          ( Helical.inverseModeNorm S p
          ∷ Helical.inverseModeNorm S q
          ∷ rawCross (C3.modeVector E p) (C3.modeVector E q)
          ∷ []))))

physicalNormalizedComplementIdentity :
  ∀ {E I S p q k} →
  (D : PhysicalNormalizedComplementData E I S p q k) →
  square (Helical.modeNorm S p - Helical.modeNorm S q)
    + (Helical.modeNorm S p * Helical.modeNorm S q)
      * norm
          (C3.complex3Add
            (R167.normalizedDirection E S p)
            (R167.normalizedDirection E S q))
  ≡ square (Helical.modeNorm S k)
physicalNormalizedComplementIdentity {E} {I} {S} {p} {q} {k} D =
  let
    rp = Helical.modeNorm S p
    rq = Helical.modeNorm S q
    rk = Helical.modeNorm S k
    ip = Helical.inverseModeNorm S p
    iq = Helical.inverseModeNorm S q
    dot = rawCross (C3.modeVector E p) (C3.modeVector E q)

    angular = normalizedDefectPolarization D

    cancelProduct :
      (rp * rq)
        * (two + two * (ip * iq * dot))
      ≡ two * (rp * rq) + two * dot
    cancelProduct
      rewrite MHD.radiusInverse (reciprocalP D)
            | MHD.radiusInverse (reciprocalQ D) =
      solve (rp ∷ rq ∷ ip ∷ iq ∷ dot ∷ [])

    rawCosine = resonantRawNormPolarization D

    radiiToRaw :
      square rk
      ≡ square rp + square rq + two * dot
    radiiToRaw =
      trans
        (R464.modeNormSquareMeaning (squareK D))
        (trans rawCosine
          (cong₂
            (λ p2 q2 → p2 + q2 + two * dot)
            (sym (R464.modeNormSquareMeaning (squareP D)))
            (sym (R464.modeNormSquareMeaning (squareQ D)))))

    algebra :
      square (rp - rq) + (two * (rp * rq) + two * dot)
      ≡ square rp + square rq + two * dot
    algebra = solve (rp ∷ rq ∷ dot ∷ [])
  in
  trans
    (cong
      (λ angularMass → square (rp - rq) + (rp * rq) * angularMass)
      angular)
    (trans
      (cong (square (rp - rq) +_) cancelProduct)
      (trans algebra (sym radiiToRaw)))

scaledNormalizedDefectBelowOutputSquare :
  ∀ {E I S p q k} →
  (D : PhysicalNormalizedComplementData E I S p q k) →
  (Helical.modeNorm S p * Helical.modeNorm S q)
    * norm
        (C3.complex3Add
          (R167.normalizedDirection E S p)
          (R167.normalizedDirection E S q))
  ≤ square (Helical.modeNorm S k)
scaledNormalizedDefectBelowOutputSquare {S = S} {p = p} {q = q} D =
  let
    rp = Helical.modeNorm S p
    rq = Helical.modeNorm S q
    radial = square (rp - rq)
    angular = (rp * rq) * norm
      (C3.complex3Add
        (R167.normalizedDirection _ S p)
        (R167.normalizedDirection _ S q))
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
    (physicalNormalizedComplementIdentity D)
    raised

radiusProductNonnegative :
  ∀ {E I S p q k} →
  (D : PhysicalNormalizedComplementData E I S p q k) →
  0ℚ ≤ Helical.modeNorm S p * Helical.modeNorm S q
radiusProductNonnegative D =
  R96.productNonnegative (radiusPNN D) (radiusQNN D)

outputRadiusSquareNonnegative :
  ∀ {E I S p q k} →
  (D : PhysicalNormalizedComplementData E I S p q k) →
  0ℚ ≤ square (Helical.modeNorm S k)
outputRadiusSquareNonnegative D =
  Rational.squareNonnegative _

round467LiteralNormalizedComplementIdentityClosed : Bool
round467LiteralNormalizedComplementIdentityClosed = true

round467R431ScaledNormalizedDefectBoundClosed : Bool
round467R431ScaledNormalizedDefectBoundClosed = true

round467UsesR232ExternalHelicalBasisFormula : Bool
round467UsesR232ExternalHelicalBasisFormula = false

round467SquareRootUsed : Bool
round467SquareRootUsed = false

round467ContainsPostulate : Bool
round467ContainsPostulate = false

round467PackageAClosed : Bool
round467PackageAClosed = false

round467ClayPromotion : Bool
round467ClayPromotion = false

round467UsesR232ExternalHelicalBasisFormulaIsFalse :
  round467UsesR232ExternalHelicalBasisFormula ≡ false
round467UsesR232ExternalHelicalBasisFormulaIsFalse = refl

round467SquareRootUsedIsFalse : round467SquareRootUsed ≡ false
round467SquareRootUsedIsFalse = refl

round467ContainsPostulateIsFalse : round467ContainsPostulate ≡ false
round467ContainsPostulateIsFalse = refl
