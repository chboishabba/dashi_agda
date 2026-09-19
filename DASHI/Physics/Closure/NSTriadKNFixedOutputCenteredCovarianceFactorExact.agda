module DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredCovarianceFactorExact where

------------------------------------------------------------------------
-- LITERAL FIXED-OUTPUT COVARIANCE -> CENTERED MULTIPLIER COMMUTATOR
--
-- R229/Rd1b2 leaves the signed finite covariance functional
--
--   sum_{alpha<beta}
--     (lambda_alpha-lambda_beta) (w_alpha-w_beta),
--
-- on one literal physical output fibre.
--
-- The fixed-output rate factorization proves pairwise
--
--   2 (lambda_alpha-lambda_beta)
--     = nu (C_alpha-C_beta),
--
-- where C_alpha = |p_alpha-q_alpha|^2.
--
-- This module sums that identity on the actual physicalOutputFiber, using its
-- theorem that every listed incidence has the same output.  Hence
--
--   2 * rateWorkCovariance
--     = nu * centeredMultiplierWorkCovariance.
--
-- No inequality, absolute value, cardinality factor, or positivity observer is
-- introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Cov
import DASHI.Physics.Closure.NSTriadKNFixedOutputViscousRateDifferenceFactorizationExact as Rate

F : C3.RealField _
F = Rational.rationalRealField

centeredAgainstHead :
  (E : C3.IntegerEmbedding F) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence → ℚ
centeredAgainstHead E work head [] = 0ℚ
centeredAgainstHead E work head (x ∷ xs) =
    ( Rate.centeredSquare E (Physical.p head) (Physical.q head)
    - Rate.centeredSquare E (Physical.p x) (Physical.q x))
    * (work head - work x)
  + centeredAgainstHead E work head xs

centeredPairDifferenceWorkSum :
  (E : C3.IntegerEmbedding F) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  List Physical.PhysicalTriadIncidence → ℚ
centeredPairDifferenceWorkSum E work [] = 0ℚ
centeredPairDifferenceWorkSum E work (x ∷ xs) =
  centeredAgainstHead E work x xs
  + centeredPairDifferenceWorkSum E work xs

modalViscousRate :
  {E : C3.IntegerEmbedding F} →
  (nu : ℚ) →
  (I : C3.ModeInverseSquare F E) →
  Z3.FourierMode → ℚ
modalViscousRate nu I mode = nu * C3.normSquared I mode

cellRateMeaning :
  {E : C3.IntegerEmbedding F} →
  (nu : ℚ) →
  (I : C3.ModeInverseSquare F E) →
  (tau : Physical.PhysicalTriadIncidence) →
  Cov.cellRate (modalViscousRate nu I) tau
  ≡ Rate.viscousCellRate nu I tau
cellRateMeaning nu I tau =
  solve
    ( nu
    ∷ C3.normSquared I (Physical.p tau)
    ∷ C3.normSquared I (Physical.q tau)
    ∷ [])

pairFactor :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (nu : ℚ) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  (head x : Physical.PhysicalTriadIncidence) →
  Physical.k head ≡ Physical.k x →
  Rate.two *
    ((Cov.cellRate (modalViscousRate nu I) head
      - Cov.cellRate (modalViscousRate nu I) x)
      * (work head - work x))
  ≡
    nu *
      (( Rate.centeredSquare E (Physical.p head) (Physical.q head)
       - Rate.centeredSquare E (Physical.p x) (Physical.q x))
       * (work head - work x))
pairFactor E I nu work head x sameOutput
  rewrite cellRateMeaning nu I head
        | cellRateMeaning nu I x =
  trans
    (Rate.fixedOutputViscousRateWorkDifferenceFactor
      E I nu (work head) (work x) head x sameOutput)
    (solve
      ( nu
      ∷ Rate.centeredSquare E (Physical.p head) (Physical.q head)
      ∷ Rate.centeredSquare E (Physical.p x) (Physical.q x)
      ∷ work head ∷ work x ∷ []))

OutputHomogeneous :
  Z3.FourierMode →
  List Physical.PhysicalTriadIncidence → Set
OutputHomogeneous output items =
  (tau : Physical.PhysicalTriadIncidence) →
  tau Cube.∈ items →
  Physical.k tau ≡ output

tailHomogeneous :
  ∀ {output head xs} →
  OutputHomogeneous output (head ∷ xs) →
  OutputHomogeneous output xs
tailHomogeneous homogeneous tau member =
  homogeneous tau (Cube.there member)

headOutput :
  ∀ {output head xs} →
  OutputHomogeneous output (head ∷ xs) →
  Physical.k head ≡ output
headOutput homogeneous = homogeneous _ (Cube.here refl)

memberOutput :
  ∀ {output head xs} →
  OutputHomogeneous output (head ∷ xs) →
  (x : Physical.PhysicalTriadIncidence) →
  x Cube.∈ xs →
  Physical.k x ≡ output
memberOutput homogeneous x member =
  homogeneous x (Cube.there member)

pairSameOutput :
  ∀ {output head xs} →
  OutputHomogeneous output (head ∷ xs) →
  (x : Physical.PhysicalTriadIncidence) →
  x Cube.∈ xs →
  Physical.k head ≡ Physical.k x
pairSameOutput homogeneous x member =
  trans
    (headOutput homogeneous)
    (sym (memberOutput homogeneous x member))

againstHeadFactor :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (nu : ℚ) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  {output : Z3.FourierMode} →
  (head : Physical.PhysicalTriadIncidence) →
  (xs : List Physical.PhysicalTriadIncidence) →
  OutputHomogeneous output (head ∷ xs) →
  Rate.two *
    Cov.pairAgainstHead
      (Cov.cellRate (modalViscousRate nu I)) work head xs
  ≡
    nu * centeredAgainstHead E work head xs
againstHeadFactor E I nu work head [] homogeneous = solve []
againstHeadFactor E I nu work {output} head (x ∷ xs) homogeneous =
  let
    sameOutput : Physical.k head ≡ Physical.k x
    sameOutput = pairSameOutput homogeneous x (Cube.here refl)

    headPair =
      pairFactor E I nu work head x sameOutput

    tailHom : OutputHomogeneous output (head ∷ xs)
    tailHom .head (Cube.here refl) =
      homogeneous head (Cube.here refl)
    tailHom tau (Cube.there member) =
      homogeneous tau (Cube.there (Cube.there member))

    tail =
      againstHeadFactor E I nu work head xs tailHom
  in
  trans
    (solve
      ( Cov.cellRate (modalViscousRate nu I) head
      ∷ Cov.cellRate (modalViscousRate nu I) x
      ∷ work head ∷ work x
      ∷ Cov.pairAgainstHead
          (Cov.cellRate (modalViscousRate nu I)) work head xs
      ∷ []))
    (trans
      (cong₂ _+_ headPair tail)
      (solve
        ( nu
        ∷ Rate.centeredSquare E (Physical.p head) (Physical.q head)
        ∷ Rate.centeredSquare E (Physical.p x) (Physical.q x)
        ∷ work head ∷ work x
        ∷ centeredAgainstHead E work head xs
        ∷ [])))

pairSumFactor :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (nu : ℚ) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  {output : Z3.FourierMode} →
  (items : List Physical.PhysicalTriadIncidence) →
  OutputHomogeneous output items →
  Rate.two *
    Cov.pairDifferenceWorkSum
      (Cov.cellRate (modalViscousRate nu I)) work items
  ≡
    nu * centeredPairDifferenceWorkSum E work items
pairSumFactor E I nu work [] homogeneous = solve []
pairSumFactor E I nu work {output} (head ∷ xs) homogeneous =
  let
    headPart =
      againstHeadFactor E I nu work head xs homogeneous

    tailPart =
      pairSumFactor E I nu work xs (tailHomogeneous homogeneous)
  in
  trans
    (solve
      ( Cov.pairAgainstHead
          (Cov.cellRate (modalViscousRate nu I)) work head xs
      ∷ Cov.pairDifferenceWorkSum
          (Cov.cellRate (modalViscousRate nu I)) work xs
      ∷ []))
    (trans
      (cong₂ _+_ headPart tailPart)
      (solve
        (nu ∷ centeredAgainstHead E work head xs
          ∷ centeredPairDifferenceWorkSum E work xs ∷ [])))

literalOutputFibreHomogeneous :
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  OutputHomogeneous output (Output.physicalOutputFiber cutoff output)
literalOutputFibreHomogeneous cutoff output tau member =
  Output.physicalOutputFiberSound member

literalFixedOutputCenteredCovarianceFactor :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (nu : ℚ) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  Rate.two *
    Cov.pairDifferenceWorkSum
      (Cov.cellRate (modalViscousRate nu I)) work
      (Output.physicalOutputFiber cutoff output)
  ≡
    nu *
      centeredPairDifferenceWorkSum E work
        (Output.physicalOutputFiber cutoff output)
literalFixedOutputCenteredCovarianceFactor E I nu work cutoff output =
  pairSumFactor E I nu work
    (Output.physicalOutputFiber cutoff output)
    (literalOutputFibreHomogeneous cutoff output)

------------------------------------------------------------------------
-- First-order partner-displacement form.
------------------------------------------------------------------------

firstOrderAgainstHead :
  (E : C3.IntegerEmbedding F) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence → ℚ
firstOrderAgainstHead E work head [] = 0ℚ
firstOrderAgainstHead E work head (x ∷ xs) =
    Rate.firstOrderCenteredDefect E head x * (work head - work x)
  + firstOrderAgainstHead E work head xs

firstOrderPairDifferenceWorkSum :
  (E : C3.IntegerEmbedding F) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  List Physical.PhysicalTriadIncidence → ℚ
firstOrderPairDifferenceWorkSum E work [] = 0ℚ
firstOrderPairDifferenceWorkSum E work (x ∷ xs) =
  firstOrderAgainstHead E work x xs
  + firstOrderPairDifferenceWorkSum E work xs

centeredPairFactorFirstOrder :
  (E : C3.IntegerEmbedding F) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Physical.k alpha ≡ Physical.k beta →
  ( Rate.centeredSquare E (Physical.p alpha) (Physical.q alpha)
  - Rate.centeredSquare E (Physical.p beta) (Physical.q beta))
    * (work alpha - work beta)
  ≡
    Rate.two
      * (Rate.firstOrderCenteredDefect E alpha beta
          * (work alpha - work beta))
centeredPairFactorFirstOrder E work alpha beta sameOutput =
  let
    base =
      Rate.fixedOutputCenteredSquareDifferenceIsFirstOrder
        E alpha beta sameOutput
  in
  trans
    (cong
      (λ centeredDefect → centeredDefect * (work alpha - work beta))
      base)
    (solve
      ( Rate.firstOrderCenteredDefect E alpha beta
      ∷ work alpha ∷ work beta ∷ []))

centeredAgainstHeadFirstOrder :
  (E : C3.IntegerEmbedding F) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  {output : Z3.FourierMode} →
  (head : Physical.PhysicalTriadIncidence) →
  (xs : List Physical.PhysicalTriadIncidence) →
  OutputHomogeneous output (head ∷ xs) →
  centeredAgainstHead E work head xs
  ≡ Rate.two * firstOrderAgainstHead E work head xs
centeredAgainstHeadFirstOrder E work head [] homogeneous = solve []
centeredAgainstHeadFirstOrder E work {output} head (x ∷ xs) homogeneous =
  let
    sameOutput =
      pairSameOutput homogeneous x (Cube.here refl)

    headPart =
      centeredPairFactorFirstOrder E work head x sameOutput

    tailHom : OutputHomogeneous output (head ∷ xs)
    tailHom .head (Cube.here refl) =
      homogeneous head (Cube.here refl)
    tailHom tau (Cube.there member) =
      homogeneous tau (Cube.there (Cube.there member))

    tailPart =
      centeredAgainstHeadFirstOrder E work head xs tailHom
  in
  trans
    (cong₂ _+_ headPart tailPart)
    (solve
      ( Rate.firstOrderCenteredDefect E head x
      ∷ work head ∷ work x
      ∷ firstOrderAgainstHead E work head xs
      ∷ []))

centeredPairSumFirstOrder :
  (E : C3.IntegerEmbedding F) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  {output : Z3.FourierMode} →
  (items : List Physical.PhysicalTriadIncidence) →
  OutputHomogeneous output items →
  centeredPairDifferenceWorkSum E work items
  ≡ Rate.two * firstOrderPairDifferenceWorkSum E work items
centeredPairSumFirstOrder E work [] homogeneous = solve []
centeredPairSumFirstOrder E work {output} (head ∷ xs) homogeneous =
  let
    headPart =
      centeredAgainstHeadFirstOrder E work head xs homogeneous
    tailPart =
      centeredPairSumFirstOrder E work xs (tailHomogeneous homogeneous)
  in
  trans
    (cong₂ _+_ headPart tailPart)
    (solve
      ( firstOrderAgainstHead E work head xs
      ∷ firstOrderPairDifferenceWorkSum E work xs
      ∷ []))

literalFixedOutputFirstOrderCovarianceFactor :
  (E : C3.IntegerEmbedding F) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  centeredPairDifferenceWorkSum E work
      (Output.physicalOutputFiber cutoff output)
  ≡
    Rate.two *
      firstOrderPairDifferenceWorkSum E work
        (Output.physicalOutputFiber cutoff output)
literalFixedOutputFirstOrderCovarianceFactor E work cutoff output =
  centeredPairSumFirstOrder E work
    (Output.physicalOutputFiber cutoff output)
    (literalOutputFibreHomogeneous cutoff output)

literalFixedOutputCenteredCovarianceFactorClosed : Bool
literalFixedOutputCenteredCovarianceFactorClosed = true

genericRateSeparationStillMandatory : Bool
genericRateSeparationStillMandatory = false

centeredMultiplierDifferenceIsCanonicalCovarianceCoordinate : Bool
centeredMultiplierDifferenceIsCanonicalCovarianceCoordinate = true

quantitativeCenteredCovarianceEstimateClosed : Bool
quantitativeCenteredCovarianceEstimateClosed = false

clayPromotion : Bool
clayPromotion = false

literalFixedOutputCenteredCovarianceFactorClosedIsTrue :
  literalFixedOutputCenteredCovarianceFactorClosed ≡ true
literalFixedOutputCenteredCovarianceFactorClosedIsTrue = refl

genericRateSeparationStillMandatoryIsFalse :
  genericRateSeparationStillMandatory ≡ false
genericRateSeparationStillMandatoryIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
