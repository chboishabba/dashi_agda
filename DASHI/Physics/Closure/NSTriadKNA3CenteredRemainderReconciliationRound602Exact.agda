{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNA3CenteredRemainderReconciliationRound602Exact where

------------------------------------------------------------------------
-- ROUND602 / R601 CENTERED NONLINEAR REMAINDER = TWICE THE R598 MISMATCH
--
-- R601 has reduced the remaining dynamic comparison to the literal full-square
--
--   C_ab =
--     2 R K_ab N_ab
--       + (n (r_a+r_b) - 2 R) G_ab.
--
-- The first term is exactly the R538 symmetric weighted nonlinear remainder,
--
--   K_ab N_ab,
--
-- while R600 already proves
--
--   Full((2 R - n (r_a+r_b)) G_ab) = 32 A3.
--
-- Hence exact finite linearity gives
--
--   Full(C)
--     = 2 R Full(KN) - 32 A3.
--
-- R596 moreover identifies the SAME full weighted nonlinear remainder with
-- the R567 forcing full square:
--
--   Full(KN) = 4 ForcingFull.
--
-- Therefore
--
--   Full(C)
--     = 2 * ( R * (4 ForcingFull) - 4 * (4 A3) ),
--
-- i.e. R601 introduces no independent analytic coordinate: it is exactly
-- twice the already-isolated R598 mismatch.  No estimate, absolute value,
-- positivity argument, or spacetime input is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; Positive; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorOnlyRound567Exact as R567
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedFullSquareRateCancellationExact as Cauchy
import DASHI.Physics.Closure.NSTriadKNR567CauchyGramFluxNormalFormRound596Exact as R596
import DASHI.Physics.Closure.NSTriadKNA3CauchyFluxTangentMismatchRound598Exact as R598
import DASHI.Physics.Closure.NSTriadKNA3CenteredCauchyPairNormalFormRound600Exact as R600
import DASHI.Physics.Closure.NSTriadKNA3CenteredCauchyNonlinearRemainderRound601Exact as R601
import DASHI.Physics.Closure.NSTriadKNA3CenteredKernelNormalFormExact as Kernel

F : C3.RealField _
F = Rational.rationalRealField

module FixedOutput
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (P : R225.PhysicalFixedOutputHelicityData
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S L H
      (Audit.velocityAt (Field30.finiteSystem physicalSystem)))
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output) where

  module R = R601.FixedOutput
    physicalSystem S L H P viscosityPositive output outputNonzero
  module Base = R600.FixedOutput physicalSystem S L H P output
  module C = R596.FixedOutput
    physicalSystem S viscosityPositive output outputNonzero
  module Mismatch = R598.FixedOutput
    physicalSystem S L H P viscosityPositive output outputNonzero

  weightedNonlinearPair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  weightedNonlinearPair = C.Swap.symmetricWeightedRemainder

  staticCenteredPair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  staticCenteredPair =
    R600.centeredStaticPair
      Base.n Base.rateTotal Base.rate Base.gram

  decomposedR601Pair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  decomposedR601Pair alpha beta =
    (R539.two * Base.rateTotal) * weightedNonlinearPair alpha beta
      + (0ℚ - 1ℚ) * staticCenteredPair alpha beta

  r601PointwiseIsWeightedMinusStatic :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    R.centeredDynamicRemainderPair alpha beta
    ≡ decomposedR601Pair alpha beta
  r601PointwiseIsWeightedMinusStatic alpha beta =
    solve
      ( Base.n
      ∷ Base.rateTotal
      ∷ Base.rate alpha
      ∷ Base.rate beta
      ∷ C.Swap.pairResolvent alpha beta
      ∷ R.nonlinearRemainder alpha beta
      ∷ Base.gram alpha beta
      ∷ [])

  r601FullIsWeightedMinusStatic :
    R543.fullSquareSum R.centeredDynamicRemainderPair R.fibre
    ≡
    (R539.two * Base.rateTotal)
      * R543.fullSquareSum weightedNonlinearPair R.fibre
      + (0ℚ - 1ℚ)
        * R543.fullSquareSum staticCenteredPair R.fibre
  r601FullIsWeightedMinusStatic =
    trans
      (Cauchy.fullSquareCongruent
        R.centeredDynamicRemainderPair
        decomposedR601Pair
        r601PointwiseIsWeightedMinusStatic
        R.fibre)
      (R600.fullSquareLinearCombination
        (R539.two * Base.rateTotal)
        (0ℚ - 1ℚ)
        weightedNonlinearPair
        staticCenteredPair
        R.fibre)

  r601FullIsWeightedMinusA3 :
    R543.fullSquareSum R.centeredDynamicRemainderPair R.fibre
    ≡
    (R539.two * Base.rateTotal)
      * R543.fullSquareSum weightedNonlinearPair R.fibre
      - R539.two * ((Kernel.four * Kernel.four) * Base.A3.signedA3)
  r601FullIsWeightedMinusA3 =
    trans
      r601FullIsWeightedMinusStatic
      (trans
        (cong₂ _+_
          refl
          (cong ((0ℚ - 1ℚ) *_) Base.centeredStaticFullSquare))
        (solve
          ( Base.rateTotal
          ∷ R543.fullSquareSum weightedNonlinearPair R.fibre
          ∷ Kernel.four
          ∷ Base.A3.signedA3
          ∷ [])))

  weightedNonlinearFullIsFourForcingFull :
    R543.fullSquareSum weightedNonlinearPair R.fibre
    ≡
    R567.four567 * Mismatch.forcingFull
  weightedNonlinearFullIsFourForcingFull =
    trans
      C.literalFullSquareNormalForm
      (sym C.fourForcingFullIsGramPlusFlux)

  r601FullIsTwiceR598Mismatch :
    R543.fullSquareSum R.centeredDynamicRemainderPair R.fibre
    ≡
    R539.two *
      ( Base.rateTotal * (Kernel.four * Mismatch.forcingFull)
        - Kernel.four * (Kernel.four * Base.A3.signedA3) )
  r601FullIsTwiceR598Mismatch =
    trans
      r601FullIsWeightedMinusA3
      (trans
        (cong
          (λ weighted →
            (R539.two * Base.rateTotal) * weighted
              - R539.two
                * ((Kernel.four * Kernel.four) * Base.A3.signedA3))
          weightedNonlinearFullIsFourForcingFull)
        (let
          fourAgreement : R567.four567 ≡ Kernel.four
          fourAgreement = Mismatch.four567IsA3Four
        in
        trans
          (cong
            (λ four567 →
              (R539.two * Base.rateTotal)
                * (four567 * Mismatch.forcingFull)
                - R539.two
                  * ((Kernel.four * Kernel.four) * Base.A3.signedA3))
            fourAgreement)
          (solve
            ( Base.rateTotal
            ∷ Kernel.four
            ∷ Mismatch.forcingFull
            ∷ Base.A3.signedA3
            ∷ []))))

------------------------------------------------------------------------
-- Status / canonical interpretation.
------------------------------------------------------------------------

round602R601ResidualReducesToR538WeightedRemainder : Bool
round602R601ResidualReducesToR538WeightedRemainder = true

round602R538WeightedRemainderFullIsR567ForcingFull : Bool
round602R538WeightedRemainderFullIsR567ForcingFull = true

round602R601ResidualIsTwiceR598Mismatch : Bool
round602R601ResidualIsTwiceR598Mismatch = true

round602IntroducesEstimate : Bool
round602IntroducesEstimate = false

round602IntroducesIndependentAnalyticLeaf : Bool
round602IntroducesIndependentAnalyticLeaf = false

round602R598MismatchPaid : Bool
round602R598MismatchPaid = false

round602R601ResidualReducesToR538WeightedRemainderIsTrue :
  round602R601ResidualReducesToR538WeightedRemainder ≡ true
round602R601ResidualReducesToR538WeightedRemainderIsTrue = refl

round602R538WeightedRemainderFullIsR567ForcingFullIsTrue :
  round602R538WeightedRemainderFullIsR567ForcingFull ≡ true
round602R538WeightedRemainderFullIsR567ForcingFullIsTrue = refl

round602R601ResidualIsTwiceR598MismatchIsTrue :
  round602R601ResidualIsTwiceR598Mismatch ≡ true
round602R601ResidualIsTwiceR598MismatchIsTrue = refl

round602IntroducesEstimateIsFalse :
  round602IntroducesEstimate ≡ false
round602IntroducesEstimateIsFalse = refl

round602IntroducesIndependentAnalyticLeafIsFalse :
  round602IntroducesIndependentAnalyticLeaf ≡ false
round602IntroducesIndependentAnalyticLeafIsFalse = refl

round602R598MismatchPaidIsFalse :
  round602R598MismatchPaid ≡ false
round602R598MismatchPaidIsFalse = refl
