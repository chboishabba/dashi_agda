module DASHI.Physics.Closure.NSTriadKNFixedOutputCrossGradientCovarianceExact where

------------------------------------------------------------------------
-- PERIODIC B / CENTERED-SQUARE COVARIANCE = CROSS-GRADIENT COVARIANCE
--
-- On a literal resonant triad p+q=k,
--
--   |p-q|^2 = |k|^2 - 4 (p . q).
--
-- Hence on ONE fixed output fibre the common |k|^2 term cancels before any
-- absolute value:
--
--   C_alpha - C_beta
--     = -4 ((p_alpha.q_alpha) - (p_beta.q_beta)).
--
-- Therefore the complete signed coherent covariance is exactly -4 times the
-- covariance of the one-derivative-on-each-input cross multiplier p.q.
--
-- This is the correct analytic normal form for the remaining physical B
-- payment.  It introduces no pair count, no shell count, no positivity
-- observer, no square root, and no Taylor/M2 remainder.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Cov
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredCovarianceFactorExact as Centered
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredMultiplierVectorCovarianceExact as Vector
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputViscousRateDifferenceFactorizationExact as Rate
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224

F : C3.RealField _
F = Rational.rationalRealField

two four : ℚ
two = 1ℚ + 1ℚ
four = two * two

crossDot :
  (E : C3.IntegerEmbedding F) →
  Z3.FourierMode → Z3.FourierMode → ℚ
crossDot E p q =
    C3.embedInteger E (Z3.kx p) * C3.embedInteger E (Z3.kx q)
  + C3.embedInteger E (Z3.ky p) * C3.embedInteger E (Z3.ky q)
  + C3.embedInteger E (Z3.kz p) * C3.embedInteger E (Z3.kz q)

centeredSquareIsInputSquaresMinusTwiceCross :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (p q : Z3.FourierMode) →
  Rate.centeredSquare E p q
  ≡ C3.normSquared I p + C3.normSquared I q - two * crossDot E p q
centeredSquareIsInputSquaresMinusTwiceCross
    E I (Z3.mode px py pz) (Z3.mode qx qy qz)
  rewrite C3.normSquaredMeaning I (Z3.mode px py pz)
        | C3.normSquaredMeaning I (Z3.mode qx qy qz) =
  solve
    ( C3.embedInteger E px ∷ C3.embedInteger E py ∷ C3.embedInteger E pz
    ∷ C3.embedInteger E qx ∷ C3.embedInteger E qy ∷ C3.embedInteger E qz
    ∷ [])

addModeSquareIsInputSquaresPlusTwiceCross :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (p q : Z3.FourierMode) →
  C3.normSquared I (Z3.addMode p q)
  ≡ C3.normSquared I p + C3.normSquared I q + two * crossDot E p q
addModeSquareIsInputSquaresPlusTwiceCross
    E I (Z3.mode px py pz) (Z3.mode qx qy qz)
  rewrite C3.normSquaredMeaning I
            (Z3.addMode (Z3.mode px py pz) (Z3.mode qx qy qz))
        | C3.normSquaredMeaning I (Z3.mode px py pz)
        | C3.normSquaredMeaning I (Z3.mode qx qy qz)
        | C3.embedAdd E px qx
        | C3.embedAdd E py qy
        | C3.embedAdd E pz qz =
  solve
    ( C3.embedInteger E px ∷ C3.embedInteger E py ∷ C3.embedInteger E pz
    ∷ C3.embedInteger E qx ∷ C3.embedInteger E qy ∷ C3.embedInteger E qz
    ∷ [])

incidenceCenteredSquareIsOutputMinusFourCross :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (tau : Physical.PhysicalTriadIncidence) →
  Rate.centeredSquare E (Physical.p tau) (Physical.q tau)
  ≡ C3.normSquared I (Physical.k tau)
      - four * crossDot E (Physical.p tau) (Physical.q tau)
incidenceCenteredSquareIsOutputMinusFourCross E I tau =
  let
    p = Physical.p tau
    q = Physical.q tau
    input =
      centeredSquareIsInputSquaresMinusTwiceCross E I p q
    output =
      addModeSquareIsInputSquaresPlusTwiceCross E I p q
    resonance :
      C3.normSquared I (Z3.addMode p q)
      ≡ C3.normSquared I (Physical.k tau)
    resonance = cong (C3.normSquared I) (Physical.resonance tau)
  in
  trans input
    (trans
      (solve
        ( C3.normSquared I p
        ∷ C3.normSquared I q
        ∷ crossDot E p q
        ∷ []))
      (trans
        (cong
          (λ outputSquare →
            outputSquare - four * crossDot E p q)
          (trans output resonance))
        refl))

fixedOutputCenteredDifferenceIsNegativeFourCrossDifference :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Physical.k alpha ≡ Physical.k beta →
  Rate.centeredSquare E (Physical.p alpha) (Physical.q alpha)
    - Rate.centeredSquare E (Physical.p beta) (Physical.q beta)
  ≡
  (- four) *
    ( crossDot E (Physical.p alpha) (Physical.q alpha)
    - crossDot E (Physical.p beta) (Physical.q beta))
fixedOutputCenteredDifferenceIsNegativeFourCrossDifference
    E I alpha beta sameOutput =
  let
    ca = crossDot E (Physical.p alpha) (Physical.q alpha)
    cb = crossDot E (Physical.p beta) (Physical.q beta)
    ka = C3.normSquared I (Physical.k alpha)
    kb = C3.normSquared I (Physical.k beta)
    aMeaning = incidenceCenteredSquareIsOutputMinusFourCross E I alpha
    bMeaning = incidenceCenteredSquareIsOutputMinusFourCross E I beta
    sameK : ka ≡ kb
    sameK = cong (C3.normSquared I) sameOutput
  in
  trans
    (cong₂ _-_ aMeaning bMeaning)
    (trans
      (cong
        (λ outputSquare →
          (outputSquare - four * ca) - (kb - four * cb))
        sameK)
      (solve (kb ∷ four ∷ ca ∷ cb ∷ [])))

crossAgainstHead :
  (E : C3.IntegerEmbedding F) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence → ℚ
crossAgainstHead E work head [] = 0ℚ
crossAgainstHead E work head (x ∷ xs) =
    ( crossDot E (Physical.p head) (Physical.q head)
    - crossDot E (Physical.p x) (Physical.q x))
      * (work head - work x)
  + crossAgainstHead E work head xs

crossPairDifferenceWorkSum :
  (E : C3.IntegerEmbedding F) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  List Physical.PhysicalTriadIncidence → ℚ
crossPairDifferenceWorkSum E work [] = 0ℚ
crossPairDifferenceWorkSum E work (x ∷ xs) =
  crossAgainstHead E work x xs
  + crossPairDifferenceWorkSum E work xs

againstHeadCenteredIsNegativeFourCross :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  {output : Z3.FourierMode} →
  (head : Physical.PhysicalTriadIncidence) →
  (xs : List Physical.PhysicalTriadIncidence) →
  Centered.OutputHomogeneous output (head ∷ xs) →
  Centered.centeredAgainstHead E work head xs
  ≡ (- four) * crossAgainstHead E work head xs
againstHeadCenteredIsNegativeFourCross E I work head [] homogeneous =
  solve []
againstHeadCenteredIsNegativeFourCross
    E I work {output} head (x ∷ xs) homogeneous =
  let
    sameOutput : Physical.k head ≡ Physical.k x
    sameOutput =
      Centered.pairSameOutput homogeneous x (Cube.here refl)

    headPart =
      cong
        (_* (work head - work x))
        (fixedOutputCenteredDifferenceIsNegativeFourCrossDifference
          E I head x sameOutput)

    tailHom : Centered.OutputHomogeneous output (head ∷ xs)
    tailHom .head (Cube.here refl) =
      homogeneous head (Cube.here refl)
    tailHom tau (Cube.there member) =
      homogeneous tau (Cube.there (Cube.there member))

    tailPart =
      againstHeadCenteredIsNegativeFourCross
        E I work head xs tailHom
  in
  trans
    (cong₂ _+_ headPart tailPart)
    (solve
      ( four
      ∷ crossDot E (Physical.p head) (Physical.q head)
      ∷ crossDot E (Physical.p x) (Physical.q x)
      ∷ work head
      ∷ work x
      ∷ crossAgainstHead E work head xs
      ∷ []))

centeredCovarianceIsNegativeFourCrossCovariance :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  {output : Z3.FourierMode} →
  (items : List Physical.PhysicalTriadIncidence) →
  Centered.OutputHomogeneous output items →
  Centered.centeredPairDifferenceWorkSum E work items
  ≡ (- four) * crossPairDifferenceWorkSum E work items
centeredCovarianceIsNegativeFourCrossCovariance E I work [] homogeneous =
  solve []
centeredCovarianceIsNegativeFourCrossCovariance
    E I work {output} (head ∷ xs) homogeneous =
  let
    headPart =
      againstHeadCenteredIsNegativeFourCross
        E I work head xs homogeneous
    tailPart =
      centeredCovarianceIsNegativeFourCrossCovariance
        E I work xs (Centered.tailHomogeneous homogeneous)
  in
  trans
    (cong₂ _+_ headPart tailPart)
    (solve
      ( four
      ∷ crossAgainstHead E work head xs
      ∷ crossPairDifferenceWorkSum E work xs
      ∷ []))

literalFixedOutputCenteredCovarianceIsNegativeFourCrossCovariance :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  Centered.centeredPairDifferenceWorkSum E work
      (Output.physicalOutputFiber cutoff output)
  ≡
  (- four) *
    crossPairDifferenceWorkSum E work
      (Output.physicalOutputFiber cutoff output)
literalFixedOutputCenteredCovarianceIsNegativeFourCrossCovariance
    E I work cutoff output =
  centeredCovarianceIsNegativeFourCrossCovariance
    E I work
    (Output.physicalOutputFiber cutoff output)
    (Centered.literalOutputFibreHomogeneous cutoff output)

crossGradientResidual :
  (E : C3.IntegerEmbedding F) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence →
  C3.Complex3 F
crossGradientResidual E value items =
  Vector.centeredMultiplierResidual
    (λ tau → crossDot E (Physical.p tau) (Physical.q tau))
    value items

literalFixedOutputCenteredResidualWorkIsNegativeFourCrossGradientWork :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  let
    items = Output.physicalOutputFiber cutoff output
    mixed = R224.foldVector value items
    centeredResidual =
      Vector.centeredMultiplierResidual
        (Vector.centeredFrequencyMultiplier E) value items
    crossResidual = crossGradientResidual E value items
  in
  Work.coherentWork mixed centeredResidual
  ≡ (- four) * Work.coherentWork mixed crossResidual
literalFixedOutputCenteredResidualWorkIsNegativeFourCrossGradientWork
    E I value cutoff output =
  let
    items = Output.physicalOutputFiber cutoff output
    mixed = R224.foldVector value items
    centeredWork = Cov.cellWork mixed value
    centeredPair =
      Centered.centeredPairDifferenceWorkSum E centeredWork items
    crossPair =
      crossPairDifferenceWorkSum E centeredWork items

    centeredMeaning :
      centeredPair
      ≡ Work.coherentWork mixed
          (Vector.centeredMultiplierResidual
            (Vector.centeredFrequencyMultiplier E) value items)
    centeredMeaning =
      Vector.pairDifferenceIsCenteredMultiplierWork
        (Vector.centeredFrequencyMultiplier E) value items

    crossMeaning :
      crossPair
      ≡ Work.coherentWork mixed
          (crossGradientResidual E value items)
    crossMeaning =
      Vector.pairDifferenceIsCenteredMultiplierWork
        (λ tau → crossDot E (Physical.p tau) (Physical.q tau))
        value items

    pairRelation :
      centeredPair ≡ (- four) * crossPair
    pairRelation =
      literalFixedOutputCenteredCovarianceIsNegativeFourCrossCovariance
        E I centeredWork cutoff output
  in
  trans
    (sym centeredMeaning)
    (trans pairRelation
      (cong ((- four) *_) crossMeaning))

crossGradientNormalFormClosed : Bool
crossGradientNormalFormClosed = true

crossGradientNormalFormIntroducesAbsoluteValue : Bool
crossGradientNormalFormIntroducesAbsoluteValue = false

crossGradientNormalFormAddsCardinalityFactor : Bool
crossGradientNormalFormAddsCardinalityFactor = false

crossGradientQuantitativePaymentClosedHere : Bool
crossGradientQuantitativePaymentClosedHere = false

clayPromotion : Bool
clayPromotion = false
