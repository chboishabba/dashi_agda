{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA1Equation51JetGaussianInteractionSplitRound108Exact where

------------------------------------------------------------------------
-- ROUND108 A1 BIDI WELD
--
-- The frozen CMP109 consumer only uses the negative MIXED coefficient of the
-- off-diagonal two-jet.  Do not require equality of unused jet coordinates.
-- It is enough to identify, on the same history/shell,
--
--   mixed(full physical jet) = mixed(gaussian jet) + mixed(interaction jet),
--   mixed(gaussian jet)      = - betaZ,
--   mixed(interaction jet)   = - betaInt.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (_+_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109MixedDerivativeBetaExtractionExact as Jet
import DASHI.Physics.YangMills.BalabanA1HistoryUniformTwoSidedBetaRound102Exact as Cert
import DASHI.Physics.YangMills.BalabanYM4FiveChannelQuarticBetaAdapterExact as Five
import DASHI.Physics.YangMills.BalabanYM4FiveChannelQuarticAbsoluteBetaRound102Exact as AbsFive

record Equation51GaussianInteractionJetSplit (History Cell : Set) : Set₁ where
  field
    certificate : Cert.HistoryUniformTwoSidedBetaData History Cell
    history : History
    jetData : Jet.CMP109OffDiagonalSecondJetData

    gaussianJet interactionJet : Jet.OffDiagonalTwoJet

    fullMixedSplits :
      Jet.mixedDerivativeCoefficient (Jet.fullOffDiagonalTwoJet jetData)
      ≡ Jet.mixedDerivativeCoefficient gaussianJet
          + Jet.mixedDerivativeCoefficient interactionJet

    gaussianMixedIsNegativeBetaZ :
      Jet.mixedDerivativeCoefficient gaussianJet
      ≡ - Cert.betaZ certificate history

    interactionMixedIsNegativeBetaInt :
      Jet.mixedDerivativeCoefficient interactionJet
      ≡ - Five.betaInt
          (AbsFive.lowerData (Cert.interaction certificate history))

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
    betaI = Five.betaInt
      (AbsFive.lowerData (Cert.interaction cert h))

    identifyMixed :
      Jet.mixedDerivativeCoefficient (gaussianJet dataSet)
        + Jet.mixedDerivativeCoefficient (interactionJet dataSet)
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
    (cong -_ (fullMixedSplits dataSet))
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

literalCMP109MixedGaussianInteractionDecompositionRound108Level : ProofLevel
literalCMP109MixedGaussianInteractionDecompositionRound108Level = conditional

literalCMP109GaussianMixedJetIdentificationRound108Level : ProofLevel
literalCMP109GaussianMixedJetIdentificationRound108Level = conditional

literalCMP109FiveChannelInteractionMixedJetIdentificationRound108Level : ProofLevel
literalCMP109FiveChannelInteractionMixedJetIdentificationRound108Level = conditional
