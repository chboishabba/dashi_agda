{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA1Equation51JetGaussianInteractionSplitRound108Exact where

------------------------------------------------------------------------
-- ROUND108 A1 BIDI WELD
--
-- Backward from the literal CMP109 (5.42) consumer, the only coordinate used is
-- the NEGATIVE mixed coefficient of the off-diagonal two-jet.  Forward from the
-- finite Ward/five-channel calculation, the physical jet splits into Gaussian
-- and normalized-interaction pieces.  Therefore the source weld need not assert
-- one opaque equality
--
--      jet beta = finite evaluator.
--
-- It is enough to prove, on the SAME history/shell,
--
--      fullJet = gaussianJet + interactionJet,
--      mixed gaussianJet    = - betaZ,
--      mixed interactionJet = - betaInt.
--
-- Additivity of the two-jet then gives beta = betaZ + betaInt exactly.  This is
-- the source-native decomposition needed by the existing Round103 Eq.(5.1)
-- carrier and Round102 history-uniform two-sided certificate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _+_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109MixedDerivativeBetaExtractionExact as Jet
import DASHI.Physics.YangMills.BalabanA1HistoryUniformTwoSidedBetaRound102Exact as Cert

record Equation51GaussianInteractionJetSplit (History Cell : Set) : Set₁ where
  field
    certificate : Cert.HistoryUniformTwoSidedBetaData History Cell
    history : History
    jetData : Jet.CMP109OffDiagonalSecondJetData

    gaussianJet interactionJet : Jet.OffDiagonalTwoJet

    fullJetSplits :
      Jet.fullOffDiagonalTwoJet jetData
      ≡ Jet.addTwoJet gaussianJet interactionJet

    gaussianMixedIsNegativeBetaZ :
      Jet.mixedDerivativeCoefficient gaussianJet
      ≡ - Cert.betaZ certificate history

    interactionMixedIsNegativeBetaInt :
      Jet.mixedDerivativeCoefficient interactionJet
      ≡ - Cert.Five.betaInt
          (Cert.AbsFive.lowerData (Cert.interaction certificate history))

open Equation51GaussianInteractionJetSplit public

negativeMixedCoefficientIsFiniteEvaluator :
  ∀ {History Cell}
    (dataSet : Equation51GaussianInteractionJetSplit History Cell) →
  - Jet.mixedDerivativeCoefficient (Jet.fullOffDiagonalTwoJet (jetData dataSet))
  ≡ Cert.beta (certificate dataSet) (history dataSet)
negativeMixedCoefficientIsFiniteEvaluator dataSet =
  let
    cert = certificate dataSet
    h = history dataSet
    g = gaussianJet dataSet
    i = interactionJet dataSet
    betaI = Cert.Five.betaInt
      (Cert.AbsFive.lowerData (Cert.interaction cert h))

    splitMixed :
      Jet.mixedDerivativeCoefficient (Jet.fullOffDiagonalTwoJet (jetData dataSet))
      ≡ Jet.mixedDerivativeCoefficient g + Jet.mixedDerivativeCoefficient i
    splitMixed = cong Jet.mixedDerivativeCoefficient (fullJetSplits dataSet)

    identifyMixed :
      Jet.mixedDerivativeCoefficient g + Jet.mixedDerivativeCoefficient i
      ≡ (- Cert.betaZ cert h) + (- betaI)
    identifyMixed = cong₂ _+_
      (gaussianMixedIsNegativeBetaZ dataSet)
      (interactionMixedIsNegativeBetaInt dataSet)

    arithmetic :
      - ((- Cert.betaZ cert h) + (- betaI))
      ≡ Cert.betaZ cert h + betaI
    arithmetic = ℚRing.solve-∀ (Cert.betaZ cert h) betaI
  in
  trans
    (cong -_ splitMixed)
    (trans
      (cong -_ identifyMixed)
      (trans arithmetic (sym (Cert.betaExact cert h))))

jetBetaIsFiniteEvaluator :
  ∀ {History Cell}
    (dataSet : Equation51GaussianInteractionJetSplit History Cell) →
  Jet.beta (jetData dataSet)
  ≡ Cert.beta (certificate dataSet) (history dataSet)
jetBetaIsFiniteEvaluator dataSet =
  trans
    (sym (Jet.cmp109MixedDerivativeExtractsBeta (jetData dataSet)))
    (negativeMixedCoefficientIsFiniteEvaluator dataSet)

round108A1GaussianInteractionJetSplitLevel : ProofLevel
round108A1GaussianInteractionJetSplitLevel = machineChecked

-- Physical leaves after this algebraic compression:
--   (1) identify the Gaussian Eq.(5.1) mixed jet (including W+Q+R, with Q/R
--       killed by the existing Lorentz-diagonal Fourier theorem) with -betaZ;
--   (2) identify the normalized interaction mixed jet with the SAME five-channel
--       betaInt already used by the quartic Cauchy certificate.
-- No third equality asserting their sum equals beta is needed.
literalCMP109GaussianMixedJetIdentificationRound108Level : ProofLevel
literalCMP109GaussianMixedJetIdentificationRound108Level = conditional

literalCMP109FiveChannelInteractionMixedJetIdentificationRound108Level : ProofLevel
literalCMP109FiveChannelInteractionMixedJetIdentificationRound108Level = conditional
