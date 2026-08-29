{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA1Equation51FiveChannelSameObjectRound103Exact where

------------------------------------------------------------------------
-- ROUND103 A1: EXPOSE THE TWO SOURCE-NATIVE SAME-OBJECT EQUALITIES
--
-- Instead of one opaque
--
--   finiteEvaluator = exact CMP109 (5.42) scalar,
--
-- factor it through CMP109's published Sect.5 two-jet:
--
--   actual mixed derivative
--      = embed(- mixed coefficient of literal Eq.(5.1) off-diagonal two-jet),
--
--   beta of that Ward/transverse two-jet
--      = history-uniform finite Gaussian + five-channel evaluator.
--
-- The existing mixed-jet theorem then proves the composite equality consumed by
-- Round102's rational-certificate-to-literal-CMP109 adapter.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCutoffBetaLaw as BetaLaw
import DASHI.Physics.YangMills.BalabanCMP109MixedDerivativeBetaExtractionExact as Jet
import DASHI.Physics.YangMills.BalabanA1HistoryUniformTwoSidedBetaRound102Exact as Cert
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Real
import DASHI.Physics.YangMills.BalabanRationalCertificateFamilyToLiteralCMP109BoundsRound102Exact as Family

record Equation51FiveChannelSameObjectData (History Cell : Set) : Set₁ where
  field
    embedding : Real.OrderedRationalRealEmbedding
    certificate : Cert.HistoryUniformTwoSidedBetaData History Cell
    historyWitness : History

    dynamics : (K : Nat) → BetaLaw.BalabanCutoffCouplingDynamics K
    historyForShell : ∀ K k → k ℕ.< K → History

    -- Literal CMP109 off-diagonal two-jet after Ward/symmetry reduction.
    jetData : ∀ K k → k ℕ.< K → Jet.CMP109OffDiagonalSecondJetData

    -- Eq.(5.1)/(5.39--5.42) source-coordinate equality: the actual real mixed
    -- derivative is the embedding of the negative mixed two-jet coefficient.
    actualDerivativeIsEmbeddedNegativeMixedJet :
      ∀ K k (k<K : k ℕ.< K) →
      BetaLaw.negativeOffDiagonalSecondMomentumDerivative
        (BetaLaw.vacuumPolarisationCoefficient (dynamics K)) k
      ≡ Real.embed embedding
          (- Jet.mixedDerivativeCoefficient
              (Jet.fullOffDiagonalTwoJet (jetData K k k<K)))

    -- Finite Ward/Gaussian/five-channel evaluator is the beta coefficient in the
    -- SAME jet, uniformly over the generated admitted history.
    jetBetaIsCertifiedEvaluator :
      ∀ K k (k<K : k ℕ.< K) →
      Jet.beta (jetData K k k<K)
      ≡ Cert.beta certificate (historyForShell K k k<K)

open Equation51FiveChannelSameObjectData public

mixedDerivativeExact :
  ∀ {History Cell}
    (dataSet : Equation51FiveChannelSameObjectData History Cell)
    K k (k<K : k ℕ.< K) →
  BetaLaw.negativeOffDiagonalSecondMomentumDerivative
    (BetaLaw.vacuumPolarisationCoefficient (dynamics dataSet K)) k
  ≡ Real.embed (embedding dataSet)
      (Cert.beta (certificate dataSet) (historyForShell dataSet K k k<K))
mixedDerivativeExact dataSet K k k<K =
  let
    jet = jetData dataSet K k k<K
    actual = actualDerivativeIsEmbeddedNegativeMixedJet dataSet K k k<K
    extraction = Jet.cmp109MixedDerivativeExtractsBeta jet
    evaluator = jetBetaIsCertifiedEvaluator dataSet K k k<K
  in
  trans actual
    (trans
      (cong (Real.embed (embedding dataSet)) extraction)
      (cong (Real.embed (embedding dataSet)) evaluator))

asLiteralCMP109RationalCertificateFamily :
  ∀ {History Cell} →
  Equation51FiveChannelSameObjectData History Cell →
  Family.LiteralCMP109RationalCertificateFamily History Cell
asLiteralCMP109RationalCertificateFamily dataSet = record
  { Family.LiteralCMP109RationalCertificateFamily.embedding = embedding dataSet
  ; Family.LiteralCMP109RationalCertificateFamily.certificate = certificate dataSet
  ; Family.LiteralCMP109RationalCertificateFamily.historyWitness = historyWitness dataSet
  ; Family.LiteralCMP109RationalCertificateFamily.dynamics = dynamics dataSet
  ; Family.LiteralCMP109RationalCertificateFamily.historyForShell = historyForShell dataSet
  ; Family.LiteralCMP109RationalCertificateFamily.mixedDerivativeExact =
      mixedDerivativeExact dataSet
  }

a1Equation51FiveChannelSameObjectCompilerLevel : ProofLevel
a1Equation51FiveChannelSameObjectCompilerLevel = machineChecked

-- The two remaining source equalities are now individually inspectable:
-- (i) Eq.(5.1) polarization -> literal off-diagonal two-jet/mixed momentum jet;
-- (ii) Ward/constrained-Gaussian + five-channel evaluator -> beta of that SAME jet.
literalCMP109Equation51OffDiagonalJetIdentificationLevel : ProofLevel
literalCMP109Equation51OffDiagonalJetIdentificationLevel = conditional

literalWardFiveChannelEvaluatorIsJetBetaLevel : ProofLevel
literalWardFiveChannelEvaluatorIsJetBetaLevel = conditional
