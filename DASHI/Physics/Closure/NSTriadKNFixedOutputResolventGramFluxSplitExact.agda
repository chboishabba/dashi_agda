module DASHI.Physics.Closure.NSTriadKNFixedOutputResolventGramFluxSplitExact where

------------------------------------------------------------------------
-- FIXED-OUTPUT WEIGHTED R290 FLUX = COMMON RESOLVENT GRAM - CENTERED DEFECT
--
-- On one literal output fibre the preceding exact rate decomposition gives
--
--   w_ab - w_k
--     = - w_ab w_k s_ab,
--
-- where
--
--   w_ab = 1 / (lambda_alpha + lambda_beta),
--   w_k  = 1 / (nu |k|^2),
--   s_ab = (nu/2)(C_alpha + C_beta),
--   C_tau = |p_tau-q_tau|^2.
--
-- Multiplying by the SAME R290 Gram scalar yields
--
--   w_ab g_ab
--     = w_k g_ab - w_ab w_k s_ab g_ab.
--
-- This file sums that identity on R396's fibre-local positive pair
-- enumeration.  Therefore the exact weighted R397/R448 endpoint flux splits
-- into:
--
--   common output resolvent * unweighted R390/R396 Gram debt
--     minus
--   one centered-frequency resolvent correction.
--
-- The correction is the precise remaining difference between the R229
-- centered-covariance coordinate and the R503 resolvent Gram coordinate.
-- No sign, absolute value, cardinality estimate, integration, or Clay
-- promotion is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Rational using (Positive)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNFixedOutputResolventCenteredDefectExact as Defect

F : C3.RealField _
F = Rational.rationalRealField

module FixedOutputSplit
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode)
    (outputPositive :
      Positive
        (Defect.PhysicalResolventDefect.outputPairHeatRate
          physicalSystem S output)) where

  module Pair = R389.DoubleMixedPair physicalSystem S
  module Local = R396.LocalEnumerate physicalSystem S
  module D = Defect.PhysicalResolventDefect physicalSystem S

  OutputHomogeneous :
    List Physical.PhysicalTriadIncidence → Set
  OutputHomogeneous items =
    (tau : Physical.PhysicalTriadIncidence) →
    tau R396.OccursIn items →
    Physical.k tau ≡ output

  tailHomogeneous :
    ∀ {head rest} →
    OutputHomogeneous (head ∷ rest) →
    OutputHomogeneous rest
  tailHomogeneous homogeneous tau member =
    homogeneous tau (R396.there member)

  headOutput :
    ∀ {head rest} →
    OutputHomogeneous (head ∷ rest) →
    Physical.k head ≡ output
  headOutput homogeneous =
    homogeneous _ R396.here

  pairCorrection :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Positive (D.physicalPairRate alpha beta) →
    ℚ
  pairCorrection alpha beta positive =
    D.pairResolvent alpha beta positive
      * D.outputResolvent output
      * D.pairCenteredResidual alpha beta
      * R291.gram (Pair.physicalDoubleMixedPair alpha beta)

  headCorrection :
    (alpha : Physical.PhysicalTriadIncidence) →
    (rest : List Physical.PhysicalTriadIncidence) →
    ((beta : Physical.PhysicalTriadIncidence) →
      beta R396.OccursIn rest →
      Positive (D.physicalPairRate alpha beta)) →
    ℚ
  headCorrection alpha [] positive = 0ℚ
  headCorrection alpha (beta ∷ rest) positive =
    pairCorrection alpha beta (positive beta R396.here)
    + headCorrection alpha rest
        (λ gamma member → positive gamma (R396.there member))

  allCorrection :
    (items : List Physical.PhysicalTriadIncidence) →
    Local.PairRatePositiveOn items →
    ℚ
  allCorrection [] Local.positiveNil = 0ℚ
  allCorrection (alpha ∷ rest)
      (Local.positiveCons headPositive tailPositive) =
    headCorrection alpha rest headPositive
      + allCorrection rest tailPositive

  pairWeightedFluxSplit :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (alphaOutput : Physical.k alpha ≡ output) →
    (betaOutput : Physical.k beta ≡ output) →
    (positive : Positive (D.physicalPairRate alpha beta)) →
    let pair = Pair.pairRatePositiveBuildsR290 alpha beta positive
    in
    R290.weightedGramFlux pair
    ≡
      D.outputResolvent output * R290.gram pair
      - pairCorrection alpha beta positive
  pairWeightedFluxSplit
      alpha beta alphaOutput betaOutput positive =
    let
      pair = Pair.pairRatePositiveBuildsR290 alpha beta positive
      w = D.pairResolvent alpha beta positive
      w0 = D.outputResolvent output
      s = D.pairCenteredResidual alpha beta
      g = R290.gram pair

      defect :
        w - w0 ≡ 0ℚ - w * w0 * s
      defect =
        D.fixedOutputResolventCenteredDefect
          output alpha beta alphaOutput betaOutput
          outputPositive positive

      weightMeaning :
        R290.resolventWeight pair ≡ w
      weightMeaning = refl

      gramMeaning :
        R290.gram pair
        ≡ R291.gram (Pair.physicalDoubleMixedPair alpha beta)
      gramMeaning = refl
    in
    trans
      (cong (λ selected → selected * R290.gram pair) weightMeaning)
      (trans
        (cong (λ selected → selected * g)
          (trans
            (solve (w ∷ w0 ∷ []))
            defect))
        (trans
          (solve (w ∷ w0 ∷ s ∷ g ∷ []))
          (cong
            (λ selected →
              w0 * g - w * w0 * s * selected)
            gramMeaning)))

  headWeightedFluxSplit :
    (alpha : Physical.PhysicalTriadIncidence) →
    (rest : List Physical.PhysicalTriadIncidence) →
    (positive :
      (beta : Physical.PhysicalTriadIncidence) →
      beta R396.OccursIn rest →
      Positive (D.physicalPairRate alpha beta)) →
    Physical.k alpha ≡ output →
    OutputHomogeneous rest →
    R385.sumWeightedFlux
      (Local.headR290Pairs alpha rest positive)
    ≡
      D.outputResolvent output
        * R385.sumGram (Local.headR290Pairs alpha rest positive)
      - headCorrection alpha rest positive
  headWeightedFluxSplit alpha [] positive alphaOutput restHom =
    solve (D.outputResolvent output ∷ [])
  headWeightedFluxSplit
      alpha (beta ∷ rest) positive alphaOutput restHom =
    let
      betaOutput = restHom beta R396.here
      head =
        pairWeightedFluxSplit
          alpha beta alphaOutput betaOutput
          (positive beta R396.here)
      tail =
        headWeightedFluxSplit
          alpha rest
          (λ gamma member → positive gamma (R396.there member))
          alphaOutput
          (λ gamma member → restHom gamma (R396.there member))
    in
    trans
      (cong₂ _+_ head tail)
      (solve
        ( D.outputResolvent output
        ∷ R290.gram
            (Pair.pairRatePositiveBuildsR290
              alpha beta (positive beta R396.here))
        ∷ pairCorrection alpha beta (positive beta R396.here)
        ∷ R385.sumGram
            (Local.headR290Pairs alpha rest
              (λ gamma member → positive gamma (R396.there member)))
        ∷ headCorrection alpha rest
            (λ gamma member → positive gamma (R396.there member))
        ∷ []))

  sumWeightedFluxAppend :
    (left right : List R290.DampedGramPair) →
    R385.sumWeightedFlux (left ++ right)
    ≡ R385.sumWeightedFlux left + R385.sumWeightedFlux right
  sumWeightedFluxAppend [] right = refl
  sumWeightedFluxAppend (pair ∷ rest) right
    rewrite sumWeightedFluxAppend rest right = refl

  sumGramAppend :
    (left right : List R290.DampedGramPair) →
    R385.sumGram (left ++ right)
    ≡ R385.sumGram left + R385.sumGram right
  sumGramAppend [] right = refl
  sumGramAppend (pair ∷ rest) right
    rewrite sumGramAppend rest right = refl

  allWeightedFluxSplit :
    (items : List Physical.PhysicalTriadIncidence) →
    (positive : Local.PairRatePositiveOn items) →
    OutputHomogeneous items →
    R385.sumWeightedFlux (Local.allR290Pairs items positive)
    ≡
      D.outputResolvent output
        * R385.sumGram (Local.allR290Pairs items positive)
      - allCorrection items positive
  allWeightedFluxSplit [] Local.positiveNil homogeneous =
    solve (D.outputResolvent output ∷ [])
  allWeightedFluxSplit
      (alpha ∷ rest)
      (Local.positiveCons headPositive tailPositive)
      homogeneous =
    let
      headPairs = Local.headR290Pairs alpha rest headPositive
      tailPairs = Local.allR290Pairs rest tailPositive
      head =
        headWeightedFluxSplit
          alpha rest headPositive
          (headOutput homogeneous)
          (tailHomogeneous homogeneous)
      tail =
        allWeightedFluxSplit
          rest tailPositive (tailHomogeneous homogeneous)
      fluxAppend = sumWeightedFluxAppend headPairs tailPairs
      gramAppend = sumGramAppend headPairs tailPairs
    in
    trans fluxAppend
      (trans
        (cong₂ _+_ head tail)
        (trans
          (solve
            ( D.outputResolvent output
            ∷ R385.sumGram headPairs
            ∷ R385.sumGram tailPairs
            ∷ headCorrection alpha rest headPositive
            ∷ allCorrection rest tailPositive
            ∷ []))
          (cong
            (λ totalGram →
              D.outputResolvent output * totalGram
                - (headCorrection alpha rest headPositive
                  + allCorrection rest tailPositive))
            (sym gramAppend))))

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

fixedOutputWeightedFluxCommonResolventSplitClosed : Bool
fixedOutputWeightedFluxCommonResolventSplitClosed = true

sameR396LocalPairEnumerationUsed : Bool
sameR396LocalPairEnumerationUsed = true

centeredResolventCorrectionAnalyticallyPaid : Bool
centeredResolventCorrectionAnalyticallyPaid = false

weightedFluxEqualsCommonResolventTimesGramWithoutCorrection : Bool
weightedFluxEqualsCommonResolventTimesGramWithoutCorrection = false

clayPromotion : Bool
clayPromotion = false

fixedOutputWeightedFluxCommonResolventSplitClosedIsTrue :
  fixedOutputWeightedFluxCommonResolventSplitClosed ≡ true
fixedOutputWeightedFluxCommonResolventSplitClosedIsTrue = refl

sameR396LocalPairEnumerationUsedIsTrue :
  sameR396LocalPairEnumerationUsed ≡ true
sameR396LocalPairEnumerationUsedIsTrue = refl

centeredResolventCorrectionAnalyticallyPaidIsFalse :
  centeredResolventCorrectionAnalyticallyPaid ≡ false
centeredResolventCorrectionAnalyticallyPaidIsFalse = refl

weightedFluxEqualsCommonResolventTimesGramWithoutCorrectionIsFalse :
  weightedFluxEqualsCommonResolventTimesGramWithoutCorrection ≡ false
weightedFluxEqualsCommonResolventTimesGramWithoutCorrectionIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
