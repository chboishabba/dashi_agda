{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA1FiveChannelEvaluatorBidiRound117Exact where

------------------------------------------------------------------------
-- ROUND117 A1 BIDI: DO NOT LEAVE THE FIVE-CHANNEL EVALUATOR AS A SECOND WELD
--
-- Backward consumer: Round103 needs
--
--   Jet.beta jet = certificate.beta history.
--
-- Forward source/certificate: the certificate already stores the exact split
--
--   beta = betaZ + betaInt,
--
-- where betaInt is definitionally the nested sum of the five physical channels
-- determinant / interaction / chart / gauge / localization.
--
-- Consequently the only A1 equality still needed on this side is that the SAME
-- physical two-jet has coefficient betaZ + betaInt.  The final
-- `jetBetaIsCertifiedEvaluator` field is theorem-generated, not another source
-- hypothesis.  This keeps Eq.(5.42) and the five-channel decomposition on one
-- coefficient and prevents double counting the interaction debt.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (-_)
import Data.Nat.Base as ℕ
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCutoffBetaLaw as BetaLaw
import DASHI.Physics.YangMills.BalabanCMP109MixedDerivativeBetaExtractionExact as Jet
import DASHI.Physics.YangMills.BalabanA1HistoryUniformTwoSidedBetaRound102Exact as Cert
import DASHI.Physics.YangMills.BalabanYM4FiveChannelQuarticBetaAdapterExact as Five
import DASHI.Physics.YangMills.BalabanYM4FiveChannelQuarticAbsoluteBetaRound102Exact as AbsFive
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Real
import DASHI.Physics.YangMills.BalabanA1Equation51FiveChannelSameObjectRound103Exact as A1

record A1ReducedSameObjectInputs (History Cell : Set) : Set₁ where
  field
    embedding : Real.OrderedRationalRealEmbedding
    certificate : Cert.HistoryUniformTwoSidedBetaData History Cell
    historyWitness : History
    dynamics : (K : Nat) → BetaLaw.BalabanCutoffCouplingDynamics K
    historyForShell : ∀ K k → k ℕ.< K → History
    jetData : ∀ K k → k ℕ.< K → Jet.CMP109OffDiagonalSecondJetData

    -- Literal Eq.(5.1)/(5.42) mixed-jet binding.  This remains the true source
    -- coordinate weld: the cutoff vacuum-polarisation coefficient and the
    -- physical two-jet are the same object in the declared embedding.
    actualDerivativeIsEmbeddedNegativeMixedJet :
      ∀ K k (k<K : k ℕ.< K) →
      BetaLaw.negativeOffDiagonalSecondMomentumDerivative
        (BetaLaw.vacuumPolarisationCoefficient (dynamics K)) k
      ≡ Real.embed embedding
          (- Jet.mixedDerivativeCoefficient
              (Jet.fullOffDiagonalTwoJet (jetData K k k<K)))

    -- The SAME two-jet is split into the Gaussian coefficient betaZ plus the
    -- physical five-channel finite-g evaluator.  Unlike the old Round103
    -- `jetBetaIsCertifiedEvaluator`, this premise stops at the actual source
    -- decomposition and lets `Cert.betaExact` perform the final identification.
    jetBetaIsGaussianPlusFiveChannel :
      ∀ K k (k<K : k ℕ.< K) →
      let history = historyForShell K k k<K
          physical = AbsFive.lowerData (Cert.interaction certificate history)
      in
      Jet.beta (jetData K k k<K)
      ≡ Cert.betaZ certificate history + Five.betaInt physical

open A1ReducedSameObjectInputs public

jetBetaIsCertifiedEvaluator :
  ∀ {History Cell}
    (dataSet : A1ReducedSameObjectInputs History Cell)
    K k (k<K : k ℕ.< K) →
  Jet.beta (jetData dataSet K k k<K)
  ≡ Cert.beta (certificate dataSet) (historyForShell dataSet K k k<K)
jetBetaIsCertifiedEvaluator dataSet K k k<K =
  let
    history = historyForShell dataSet K k k<K
    split = jetBetaIsGaussianPlusFiveChannel dataSet K k k<K
    certificateSplit = Cert.betaExact (certificate dataSet) history
  in
  trans split (sym certificateSplit)

asEquation51FiveChannelSameObjectData :
  ∀ {History Cell} →
  A1ReducedSameObjectInputs History Cell →
  A1.Equation51FiveChannelSameObjectData History Cell
asEquation51FiveChannelSameObjectData dataSet = record
  { A1.Equation51FiveChannelSameObjectData.embedding = embedding dataSet
  ; A1.Equation51FiveChannelSameObjectData.certificate = certificate dataSet
  ; A1.Equation51FiveChannelSameObjectData.historyWitness = historyWitness dataSet
  ; A1.Equation51FiveChannelSameObjectData.dynamics = dynamics dataSet
  ; A1.Equation51FiveChannelSameObjectData.historyForShell = historyForShell dataSet
  ; A1.Equation51FiveChannelSameObjectData.jetData = jetData dataSet
  ; A1.Equation51FiveChannelSameObjectData.actualDerivativeIsEmbeddedNegativeMixedJet =
      actualDerivativeIsEmbeddedNegativeMixedJet dataSet
  ; A1.Equation51FiveChannelSameObjectData.jetBetaIsCertifiedEvaluator =
      jetBetaIsCertifiedEvaluator dataSet
  }

a1FiveChannelEvaluatorDerivedLevel : ProofLevel
a1FiveChannelEvaluatorDerivedLevel = machineChecked

a1ReducedInputsToEquation542CompilerLevel : ProofLevel
a1ReducedInputsToEquation542CompilerLevel = machineChecked

-- Honest physical leaf after the reduction: instantiate one physical two-jet
-- whose Gaussian part is the constrained W/Q/R trace-log coefficient and whose
-- finite-g part is exactly the five declared channel sum.  Eq.(5.42) extraction
-- and the certificate evaluator equality are then downstream theorems.
literalA1PhysicalJetGaussianFiveChannelSplitLevel : ProofLevel
literalA1PhysicalJetGaussianFiveChannelSplitLevel = conditional
