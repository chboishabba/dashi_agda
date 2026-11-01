module DASHI.Physics.Closure.NSTriadKNFixedOutputResolventCenteredDefectExact where

------------------------------------------------------------------------
-- FIXED-OUTPUT R290 RESOLVENT DEFECT = CENTERED-FREQUENCY DEFECT
--
-- On one physical output fibre p+q=k, the literal mixed-cell decay rate is
--
--   lambda_tau = (nu/2)|k|^2 + (nu/2) C_tau,
--   C_tau = |p_tau-q_tau|^2.
--
-- Hence for one unordered R290 pair alpha,beta,
--
--   Lambda_ab = lambda_alpha + lambda_beta
--             = nu |k|^2 + (nu/2)(C_alpha+C_beta).
--
-- With positive pair rate and positive output rate, the constructive rational
-- reciprocal law gives the exact resolvent defect
--
--   1/Lambda_ab - 1/(nu|k|^2)
--     = - (1/Lambda_ab)(1/(nu|k|^2))
--         (nu/2)(C_alpha+C_beta).
--
-- Thus the varying R290/R503 resolvent and the R229 centered-covariance lane
-- are driven by the SAME centered-frequency multiplier.  This is an identity,
-- not an estimate: no absolute value, shell count, cutoff factor, or Clay
-- promotion is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
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
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Cov
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredCovarianceFactorExact as Centered
import DASHI.Physics.Closure.NSTriadKNFixedOutputViscousRateDifferenceFactorizationExact as Rate
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalOutputRateNormalFormExact as OutputRate
import DASHI.Physics.Closure.NSTriadKNCyclicResolventDefectFactorizationBidiExact as ReciprocalDefect
import DASHI.Physics.YangMills.BalabanClayGate4RationalPositiveMassReciprocalExact as Reciprocal

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalResolventDefect
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module Pair = R389.DoubleMixedPair physicalSystem S

  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem
  nu = Field30.viscosity physicalSystem

  cellRate : Physical.PhysicalTriadIncidence → ℚ
  cellRate = Pair.D.Pair.cellRate

  cellRateIsLiteralViscous :
    (tau : Physical.PhysicalTriadIncidence) →
    cellRate tau
    ≡ Cov.cellRate (Centered.modalViscousRate nu I) tau
  cellRateIsLiteralViscous tau = refl

  outputPairHeatRate : Z3.FourierMode → ℚ
  outputPairHeatRate output =
    OutputRate.outputHeatRate nu I output
      + OutputRate.outputHeatRate nu I output

  pairCenteredResidual :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  pairCenteredResidual alpha beta =
    OutputRate.halfViscosity nu
      * ( Rate.centeredSquare E
            (Physical.p alpha) (Physical.q alpha)
        + Rate.centeredSquare E
            (Physical.p beta) (Physical.q beta))

  physicalPairRate :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  physicalPairRate alpha beta =
    R291.pairRate (Pair.physicalDoubleMixedPair alpha beta)

  physicalPairRateSplitsAtOutput :
    (output : Z3.FourierMode) →
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    Physical.k beta ≡ output →
    physicalPairRate alpha beta
    ≡ outputPairHeatRate output + pairCenteredResidual alpha beta
  physicalPairRateSplitsAtOutput output alpha beta alphaOutput betaOutput =
    let
      common = OutputRate.outputHeatRate nu I output
      centeredA =
        Rate.centeredSquare E
          (Physical.p alpha) (Physical.q alpha)
      centeredB =
        Rate.centeredSquare E
          (Physical.p beta) (Physical.q beta)
      halfNu = OutputRate.halfViscosity nu

      alphaSplit :
        cellRate alpha ≡ common + halfNu * centeredA
      alphaSplit =
        trans
          (cellRateIsLiteralViscous alpha)
          (OutputRate.cellRateSplitsAtPhysicalOutput
            E I nu output alpha alphaOutput)

      betaSplit :
        cellRate beta ≡ common + halfNu * centeredB
      betaSplit =
        trans
          (cellRateIsLiteralViscous beta)
          (OutputRate.cellRateSplitsAtPhysicalOutput
            E I nu output beta betaOutput)
    in
    trans
      (cong₂ _+_ alphaSplit betaSplit)
      (solve (common ∷ halfNu ∷ centeredA ∷ centeredB ∷ []))

  outputResolvent : Z3.FourierMode → ℚ
  outputResolvent output =
    Reciprocal.safeRationalReciprocal (outputPairHeatRate output)

  pairResolvent :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Positive (physicalPairRate alpha beta) →
    ℚ
  pairResolvent alpha beta pairPositive =
    R290.resolventWeight
      (Pair.pairRatePositiveBuildsR290 alpha beta pairPositive)

  pairResolventMeaning :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (pairPositive : Positive (physicalPairRate alpha beta)) →
    pairResolvent alpha beta pairPositive
    ≡ Reciprocal.safeRationalReciprocal (physicalPairRate alpha beta)
  pairResolventMeaning alpha beta pairPositive = refl

  fixedOutputResolventCenteredDefect :
    (output : Z3.FourierMode) →
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (alphaOutput : Physical.k alpha ≡ output) →
    (betaOutput : Physical.k beta ≡ output) →
    (outputPositive : Positive (outputPairHeatRate output)) →
    (pairPositive : Positive (physicalPairRate alpha beta)) →
    pairResolvent alpha beta pairPositive - outputResolvent output
    ≡
    0ℚ
      - pairResolvent alpha beta pairPositive
          * outputResolvent output
          * pairCenteredResidual alpha beta
  fixedOutputResolventCenteredDefect
      output alpha beta alphaOutput betaOutput
      outputPositive pairPositive =
    let
      pairRate = physicalPairRate alpha beta
      common = outputPairHeatRate output
      residual = pairCenteredResidual alpha beta

      reciprocalDefect :
        Reciprocal.safeRationalReciprocal pairRate
          - Reciprocal.safeRationalReciprocal common
        ≡
        Reciprocal.safeRationalReciprocal pairRate
          * Reciprocal.safeRationalReciprocal common
          * (common - pairRate)
      reciprocalDefect =
        ReciprocalDefect.reciprocalDifferenceFactorization
          common pairRate outputPositive pairPositive

      rateSplit :
        pairRate ≡ common + residual
      rateSplit =
        physicalPairRateSplitsAtOutput
          output alpha beta alphaOutput betaOutput

      exposeResidual :
        Reciprocal.safeRationalReciprocal pairRate
          * Reciprocal.safeRationalReciprocal common
          * (common - pairRate)
        ≡
        0ℚ
          - Reciprocal.safeRationalReciprocal pairRate
              * Reciprocal.safeRationalReciprocal common
              * residual
      exposeResidual
        rewrite rateSplit =
        solve
          ( Reciprocal.safeRationalReciprocal pairRate
          ∷ Reciprocal.safeRationalReciprocal common
          ∷ common ∷ residual ∷ [])
    in
    trans
      (cong
        (λ pairWeight →
          pairWeight - outputResolvent output)
        (pairResolventMeaning alpha beta pairPositive))
      (trans reciprocalDefect
        (trans exposeResidual
          (cong
            (λ pairWeight →
              0ℚ - pairWeight * outputResolvent output * residual)
            (sym (pairResolventMeaning alpha beta pairPositive)))))

------------------------------------------------------------------------
-- Trust boundary.
------------------------------------------------------------------------

physicalPairRateOutputCenteredSplitClosed : Bool
physicalPairRateOutputCenteredSplitClosed = true

fixedOutputResolventCenteredDefectClosed : Bool
fixedOutputResolventCenteredDefectClosed = true

resolventVariationUsesSameCenteredMultiplierAsCovariance : Bool
resolventVariationUsesSameCenteredMultiplierAsCovariance = true

resolventCenteredDefectAnalyticPaymentClosed : Bool
resolventCenteredDefectAnalyticPaymentClosed = false

clayPromotion : Bool
clayPromotion = false

physicalPairRateOutputCenteredSplitClosedIsTrue :
  physicalPairRateOutputCenteredSplitClosed ≡ true
physicalPairRateOutputCenteredSplitClosedIsTrue = refl

fixedOutputResolventCenteredDefectClosedIsTrue :
  fixedOutputResolventCenteredDefectClosed ≡ true
fixedOutputResolventCenteredDefectClosedIsTrue = refl

resolventVariationUsesSameCenteredMultiplierAsCovarianceIsTrue :
  resolventVariationUsesSameCenteredMultiplierAsCovariance ≡ true
resolventVariationUsesSameCenteredMultiplierAsCovarianceIsTrue = refl

resolventCenteredDefectAnalyticPaymentClosedIsFalse :
  resolventCenteredDefectAnalyticPaymentClosed ≡ false
resolventCenteredDefectAnalyticPaymentClosedIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
