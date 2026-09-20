module DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredToInputLaplacianCovarianceExact where

------------------------------------------------------------------------
-- PERIODIC B / CENTERED-SQUARE COVARIANCE = 2 * INPUT-LAPLACIAN COVARIANCE
--
-- On one literal fixed-output fibre p+q=k, the exact parallelogram law gives
--
--   C_tau = |p_tau-q_tau|^2
--   S_tau = |p_tau|^2 + |q_tau|^2
--
-- and for any two incidences alpha,beta with the SAME output,
--
--   C_alpha - C_beta = 2 (S_alpha - S_beta).
--
-- Therefore the COMPLETE signed covariance, before any absolute value, obeys
--
--   sum_{alpha<beta} (C_alpha-C_beta)(w_alpha-w_beta)
--
--     = 2 sum_{alpha<beta} (S_alpha-S_beta)(w_alpha-w_beta).
--
-- This is stronger than the local absolute/M2 route for the physical endgame:
-- the common output Laplacian has cancelled exactly and the entire covariance
-- is one input-Laplacian covariance functional.  No pair-count estimate,
-- positivity observer, Taylor remainder, or cutoff factor is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; refl; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Cov
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredCovarianceFactorExact as Centered
import DASHI.Physics.Closure.NSTriadKNFixedOutputViscousRateDifferenceFactorizationExact as Rate

F : C3.RealField _
F = Rational.rationalRealField

inputMass :
  {E : C3.IntegerEmbedding F} →
  (I : C3.ModeInverseSquare F E) →
  Physical.PhysicalTriadIncidence → ℚ
inputMass I tau =
  Rate.inputSquareMass I (Physical.p tau) (Physical.q tau)

inputMassAgainstHead :
  {E : C3.IntegerEmbedding F} →
  (I : C3.ModeInverseSquare F E) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence → ℚ
inputMassAgainstHead I work head [] = 0ℚ
inputMassAgainstHead I work head (x ∷ xs) =
    (inputMass I head - inputMass I x) * (work head - work x)
  + inputMassAgainstHead I work head xs

inputMassPairDifferenceWorkSum :
  {E : C3.IntegerEmbedding F} →
  (I : C3.ModeInverseSquare F E) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  List Physical.PhysicalTriadIncidence → ℚ
inputMassPairDifferenceWorkSum I work [] = 0ℚ
inputMassPairDifferenceWorkSum I work (x ∷ xs) =
  inputMassAgainstHead I work x xs
  + inputMassPairDifferenceWorkSum I work xs

centeredPairIsTwiceInputMassPair :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Physical.k alpha ≡ Physical.k beta →
  ( Rate.centeredSquare E (Physical.p alpha) (Physical.q alpha)
  - Rate.centeredSquare E (Physical.p beta) (Physical.q beta))
    * (work alpha - work beta)
  ≡
  Rate.two *
    ((inputMass I alpha - inputMass I beta) * (work alpha - work beta))
centeredPairIsTwiceInputMassPair E I work alpha beta sameOutput =
  let
    base :
      Rate.two * (inputMass I alpha - inputMass I beta)
      ≡
      Rate.centeredSquare E (Physical.p alpha) (Physical.q alpha)
      - Rate.centeredSquare E (Physical.p beta) (Physical.q beta)
    base =
      Rate.fixedOutputInputSquareDifference E I alpha beta sameOutput
  in
  trans
    (cong₂ _*_
      (sym base)
      refl)
    (solve
      ( inputMass I alpha
      ∷ inputMass I beta
      ∷ work alpha
      ∷ work beta
      ∷ []))

againstHeadCenteredIsTwiceInputMass :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  {output : Z3.FourierMode} →
  (head : Physical.PhysicalTriadIncidence) →
  (xs : List Physical.PhysicalTriadIncidence) →
  Centered.OutputHomogeneous output (head ∷ xs) →
  Centered.centeredAgainstHead E work head xs
  ≡ Rate.two * inputMassAgainstHead I work head xs
againstHeadCenteredIsTwiceInputMass E I work head [] homogeneous =
  solve []
againstHeadCenteredIsTwiceInputMass E I work {output} head (x ∷ xs) homogeneous =
  let
    sameOutput : Physical.k head ≡ Physical.k x
    sameOutput = Centered.pairSameOutput homogeneous x (Cube.here refl)

    headPart =
      centeredPairIsTwiceInputMassPair
        E I work head x sameOutput

    tailHom : Centered.OutputHomogeneous output (head ∷ xs)
    tailHom .head (Cube.here refl) =
      homogeneous head (Cube.here refl)
    tailHom tau (Cube.there member) =
      homogeneous tau (Cube.there (Cube.there member))

    tailPart =
      againstHeadCenteredIsTwiceInputMass
        E I work head xs tailHom
  in
  trans
    (cong₂ _+_ headPart tailPart)
    (solve
      ( inputMass I head
      ∷ inputMass I x
      ∷ work head
      ∷ work x
      ∷ inputMassAgainstHead I work head xs
      ∷ []))

centeredCovarianceIsTwiceInputMassCovariance :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  {output : Z3.FourierMode} →
  (items : List Physical.PhysicalTriadIncidence) →
  Centered.OutputHomogeneous output items →
  Centered.centeredPairDifferenceWorkSum E work items
  ≡ Rate.two * inputMassPairDifferenceWorkSum I work items
centeredCovarianceIsTwiceInputMassCovariance E I work [] homogeneous =
  solve []
centeredCovarianceIsTwiceInputMassCovariance
    E I work {output} (head ∷ xs) homogeneous =
  let
    headPart =
      againstHeadCenteredIsTwiceInputMass
        E I work head xs homogeneous
    tailPart =
      centeredCovarianceIsTwiceInputMassCovariance
        E I work xs (Centered.tailHomogeneous homogeneous)
  in
  trans
    (cong₂ _+_ headPart tailPart)
    (solve
      ( inputMassAgainstHead I work head xs
      ∷ inputMassPairDifferenceWorkSum I work xs
      ∷ []))

literalFixedOutputCenteredCovarianceIsTwiceInputMassCovariance :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  Centered.centeredPairDifferenceWorkSum E work
      (Output.physicalOutputFiber cutoff output)
  ≡
  Rate.two *
    inputMassPairDifferenceWorkSum I work
      (Output.physicalOutputFiber cutoff output)
literalFixedOutputCenteredCovarianceIsTwiceInputMassCovariance
    E I work cutoff output =
  centeredCovarianceIsTwiceInputMassCovariance
    E I work
    (Output.physicalOutputFiber cutoff output)
    (Centered.literalOutputFibreHomogeneous cutoff output)

------------------------------------------------------------------------
-- Relation to the physical viscous-rate covariance.
--
-- Since lambda_tau = nu S_tau, the physical rate covariance is just nu times
-- the input-Laplacian covariance.  Combining with the preceding theorem gives
-- the same centered-square identity without any new estimate.
------------------------------------------------------------------------

viscousRatePairIsViscosityTimesInputMassPair :
  {E : C3.IntegerEmbedding F} →
  (I : C3.ModeInverseSquare F E) →
  (nu : ℚ) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  ((nu * inputMass I alpha) - (nu * inputMass I beta))
    * (work alpha - work beta)
  ≡
  nu * ((inputMass I alpha - inputMass I beta)
    * (work alpha - work beta))
viscousRatePairIsViscosityTimesInputMassPair I nu work alpha beta =
  solve
    ( nu
    ∷ inputMass I alpha
    ∷ inputMass I beta
    ∷ work alpha
    ∷ work beta
    ∷ [])

centeredToInputLaplacianCovarianceClosed : Bool
centeredToInputLaplacianCovarianceClosed = true

commonOutputLaplacianCancelsBeforeObservation : Bool
commonOutputLaplacianCancelsBeforeObservation = true

centeredToInputLaplacianAddsCardinalityFactor : Bool
centeredToInputLaplacianAddsCardinalityFactor = false

quantitativeInputLaplacianCovariancePaymentClosedHere : Bool
quantitativeInputLaplacianCovariancePaymentClosedHere = false

clayPromotion : Bool
clayPromotion = false
