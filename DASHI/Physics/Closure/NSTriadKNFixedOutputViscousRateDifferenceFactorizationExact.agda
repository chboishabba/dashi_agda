module DASHI.Physics.Closure.NSTriadKNFixedOutputViscousRateDifferenceFactorizationExact where

------------------------------------------------------------------------
-- FIXED-OUTPUT VISCOUS RATE DIFFERENCE = CENTERED-FREQUENCY DEFECT
--
-- On one output fibre p+q=k, the physical viscous cell rate is
--
--   lambda(p,q) = nu (|p|^2 + |q|^2).
--
-- The exact parallelogram identity gives
--
--   2 (|p|^2 + |q|^2) = |p+q|^2 + |p-q|^2.
--
-- Therefore for two incidences alpha,beta with the SAME output,
--
--   2 (lambda_alpha - lambda_beta)
--     = nu ( |p_alpha-q_alpha|^2 - |p_beta-q_beta|^2 ).
--
-- This is the correct division-free coordinate for the R229/R414 coherent
-- covariance: the dangerous rate difference is not an opaque positive number;
-- it is a centered-frequency multiplier difference.  Coordinatewise the final
-- difference of squares factors again as
--
--   (dA-dB)(dA+dB).
--
-- No inequality, absolute value, square root, cardinality factor, or Clay
-- promotion is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 1ℚ + 1ℚ

------------------------------------------------------------------------
-- Centered p-q Euclidean square on the rational lattice.
------------------------------------------------------------------------

centeredSquare :
  (E : C3.IntegerEmbedding F) →
  Z3.FourierMode → Z3.FourierMode → ℚ
centeredSquare E (Z3.mode px py pz) (Z3.mode qx qy qz) =
    Rational.square (C3.embedInteger E px - C3.embedInteger E qx)
  + Rational.square (C3.embedInteger E py - C3.embedInteger E qy)
  + Rational.square (C3.embedInteger E pz - C3.embedInteger E qz)

inputSquareMass :
  (I : C3.ModeInverseSquare F E) →
  Z3.FourierMode → Z3.FourierMode → ℚ
inputSquareMass I p q = C3.normSquared I p + C3.normSquared I q

------------------------------------------------------------------------
-- Exact rational parallelogram law.
------------------------------------------------------------------------

inputParallelogram :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (p q : Z3.FourierMode) →
  two * inputSquareMass I p q
  ≡ C3.normSquared I (Z3.addMode p q) + centeredSquare E p q
inputParallelogram E I (Z3.mode px py pz) (Z3.mode qx qy qz)
  rewrite C3.normSquaredMeaning I (Z3.mode px py pz)
        | C3.normSquaredMeaning I (Z3.mode qx qy qz)
        | C3.normSquaredMeaning I
            (Z3.addMode (Z3.mode px py pz) (Z3.mode qx qy qz))
        | C3.embedAdd E px qx
        | C3.embedAdd E py qy
        | C3.embedAdd E pz qz =
  solve
    ( C3.embedInteger E px ∷ C3.embedInteger E py ∷ C3.embedInteger E pz
    ∷ C3.embedInteger E qx ∷ C3.embedInteger E qy ∷ C3.embedInteger E qz
    ∷ [])

incidenceParallelogram :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (tau : Physical.PhysicalTriadIncidence) →
  two * inputSquareMass I (Physical.p tau) (Physical.q tau)
  ≡ C3.normSquared I (Physical.k tau)
      + centeredSquare E (Physical.p tau) (Physical.q tau)
incidenceParallelogram E I tau =
  trans
    (inputParallelogram E I (Physical.p tau) (Physical.q tau))
    (cong (_+ centeredSquare E (Physical.p tau) (Physical.q tau))
      (cong (C3.normSquared I) (Physical.resonance tau)))

------------------------------------------------------------------------
-- Same-output cancellation of the common |k|^2 term.
------------------------------------------------------------------------

fixedOutputInputSquareDifference :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Physical.k alpha ≡ Physical.k beta →
  two *
    ( inputSquareMass I (Physical.p alpha) (Physical.q alpha)
    - inputSquareMass I (Physical.p beta) (Physical.q beta))
  ≡
    centeredSquare E (Physical.p alpha) (Physical.q alpha)
    - centeredSquare E (Physical.p beta) (Physical.q beta)
fixedOutputInputSquareDifference E I alpha beta sameOutput =
  let
    Sa = inputSquareMass I (Physical.p alpha) (Physical.q alpha)
    Sb = inputSquareMass I (Physical.p beta) (Physical.q beta)
    Ca = centeredSquare E (Physical.p alpha) (Physical.q alpha)
    Cb = centeredSquare E (Physical.p beta) (Physical.q beta)
    Ka = C3.normSquared I (Physical.k alpha)
    Kb = C3.normSquared I (Physical.k beta)

    pa : two * Sa ≡ Ka + Ca
    pa = incidenceParallelogram E I alpha

    pb : two * Sb ≡ Kb + Cb
    pb = incidenceParallelogram E I beta

    sameK : Ka ≡ Kb
    sameK = cong (C3.normSquared I) sameOutput
  in
  rewrite pa | pb | sameK =
    solve (Kb ∷ Ca ∷ Cb ∷ [])

------------------------------------------------------------------------
-- Physical viscosity scaling.
------------------------------------------------------------------------

viscousCellRate :
  (nu : ℚ) →
  (I : C3.ModeInverseSquare F E) →
  Physical.PhysicalTriadIncidence → ℚ
viscousCellRate nu I tau =
  nu * inputSquareMass I (Physical.p tau) (Physical.q tau)

fixedOutputViscousRateDifference :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (nu : ℚ)
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Physical.k alpha ≡ Physical.k beta →
  two *
    (viscousCellRate nu I alpha - viscousCellRate nu I beta)
  ≡ nu *
    ( centeredSquare E (Physical.p alpha) (Physical.q alpha)
    - centeredSquare E (Physical.p beta) (Physical.q beta))
fixedOutputViscousRateDifference E I nu alpha beta sameOutput =
  let
    Sa = inputSquareMass I (Physical.p alpha) (Physical.q alpha)
    Sb = inputSquareMass I (Physical.p beta) (Physical.q beta)
    centered =
      centeredSquare E (Physical.p alpha) (Physical.q alpha)
      - centeredSquare E (Physical.p beta) (Physical.q beta)
    base : two * (Sa - Sb) ≡ centered
    base = fixedOutputInputSquareDifference E I alpha beta sameOutput
  in
  trans
    (solve (nu ∷ Sa ∷ Sb ∷ []))
    (trans
      (cong (nu *_) base)
      refl)

------------------------------------------------------------------------
-- Factor the centered-square defect into first-order coordinate differences.
------------------------------------------------------------------------

centeredX :
  (E : C3.IntegerEmbedding F) →
  Z3.FourierMode → Z3.FourierMode → ℚ
centeredX E p q = C3.embedInteger E (Z3.kx p) - C3.embedInteger E (Z3.kx q)

centeredY :
  (E : C3.IntegerEmbedding F) →
  Z3.FourierMode → Z3.FourierMode → ℚ
centeredY E p q = C3.embedInteger E (Z3.ky p) - C3.embedInteger E (Z3.ky q)

centeredZ :
  (E : C3.IntegerEmbedding F) →
  Z3.FourierMode → Z3.FourierMode → ℚ
centeredZ E p q = C3.embedInteger E (Z3.kz p) - C3.embedInteger E (Z3.kz q)

centeredSquareDifferenceFactors :
  (E : C3.IntegerEmbedding F)
  (pa qa pb qb : Z3.FourierMode) →
  centeredSquare E pa qa - centeredSquare E pb qb
  ≡
      (centeredX E pa qa - centeredX E pb qb)
      * (centeredX E pa qa + centeredX E pb qb)
    + (centeredY E pa qa - centeredY E pb qb)
      * (centeredY E pa qa + centeredY E pb qb)
    + (centeredZ E pa qa - centeredZ E pb qb)
      * (centeredZ E pa qa + centeredZ E pb qb)
centeredSquareDifferenceFactors E pa qa pb qb =
  solve
    ( centeredX E pa qa ∷ centeredX E pb qb
    ∷ centeredY E pa qa ∷ centeredY E pb qb
    ∷ centeredZ E pa qa ∷ centeredZ E pb qb
    ∷ [])

fixedOutputViscousRateWorkDifferenceFactor :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (nu workA workB : ℚ)
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Physical.k alpha ≡ Physical.k beta →
  two *
    ((viscousCellRate nu I alpha - viscousCellRate nu I beta)
      * (workA - workB))
  ≡
    nu *
      ( centeredSquare E (Physical.p alpha) (Physical.q alpha)
      - centeredSquare E (Physical.p beta) (Physical.q beta))
      * (workA - workB)
fixedOutputViscousRateWorkDifferenceFactor
    E I nu workA workB alpha beta sameOutput =
  let
    rateA = viscousCellRate nu I alpha
    rateB = viscousCellRate nu I beta
    centered =
      centeredSquare E (Physical.p alpha) (Physical.q alpha)
      - centeredSquare E (Physical.p beta) (Physical.q beta)
    base : two * (rateA - rateB) ≡ nu * centered
    base = fixedOutputViscousRateDifference E I nu alpha beta sameOutput
  in
  trans
    (solve (rateA ∷ rateB ∷ workA ∷ workB ∷ []))
    (cong (_* (workA - workB)) base)

------------------------------------------------------------------------
-- Trust boundary.
------------------------------------------------------------------------

fixedOutputRateDifferenceFactorizationClosed : Bool
fixedOutputRateDifferenceFactorizationClosed = true

fixedOutputRateDifferenceIsCenteredMultiplierDefect : Bool
fixedOutputRateDifferenceIsCenteredMultiplierDefect = true

rateDifferenceFactorizationUsesAbsoluteValue : Bool
rateDifferenceFactorizationUsesAbsoluteValue = false

rateDifferenceFactorizationUsesCardinality : Bool
rateDifferenceFactorizationUsesCardinality = false

quantitativeCovariancePaymentClosedHere : Bool
quantitativeCovariancePaymentClosedHere = false

clayPromotion : Bool
clayPromotion = false

fixedOutputRateDifferenceFactorizationClosedIsTrue :
  fixedOutputRateDifferenceFactorizationClosed ≡ true
fixedOutputRateDifferenceFactorizationClosedIsTrue = refl

rateDifferenceFactorizationUsesAbsoluteValueIsFalse :
  rateDifferenceFactorizationUsesAbsoluteValue ≡ false
rateDifferenceFactorizationUsesAbsoluteValueIsFalse = refl

rateDifferenceFactorizationUsesCardinalityIsFalse :
  rateDifferenceFactorizationUsesCardinality ≡ false
rateDifferenceFactorizationUsesCardinalityIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
