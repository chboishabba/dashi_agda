{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA1Equation51SplitToLiteralCMP109Round108Exact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (-_)
import Data.Nat.Base as ℕ

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCutoffBetaLaw as BetaLaw
import DASHI.Physics.YangMills.BalabanCMP109MixedDerivativeBetaExtractionExact as Jet
import DASHI.Physics.YangMills.BalabanA1HistoryUniformTwoSidedBetaRound102Exact as Cert
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Real
import DASHI.Physics.YangMills.BalabanA1Equation51FiveChannelSameObjectRound103Exact as R103
import DASHI.Physics.YangMills.BalabanA1Equation51JetGaussianInteractionSplitRound108Exact as Split

------------------------------------------------------------------------
-- The Round103 consumer asked for jetBetaIsCertifiedEvaluator directly.
-- Round108 constructs that field from the finer Gaussian/interaction split.
------------------------------------------------------------------------

record Equation51SplitLiteralFamily (History Cell : Set) : Set₁ where
  field
    embedding : Real.OrderedRationalRealEmbedding
    certificate : Cert.HistoryUniformTwoSidedBetaData History Cell
    historyWitness : History
    dynamics : (K : Nat) → BetaLaw.BalabanCutoffCouplingDynamics K
    historyForShell : ∀ K k → k ℕ.< K → History

    splitData : ∀ K k (k<K : k ℕ.< K) →
      Split.Equation51GaussianInteractionJetSplit History Cell

    splitUsesFamilyCertificate : ∀ K k (k<K : k ℕ.< K) →
      Split.certificate (splitData K k k<K) ≡ certificate

    splitUsesPhysicalHistory : ∀ K k (k<K : k ℕ.< K) →
      Split.history (splitData K k k<K) ≡ historyForShell K k k<K

    actualDerivativeIsEmbeddedNegativeMixedJet :
      ∀ K k (k<K : k ℕ.< K) →
      BetaLaw.negativeOffDiagonalSecondMomentumDerivative
        (BetaLaw.vacuumPolarisationCoefficient (dynamics K)) k
      ≡ Real.embed embedding
          (- Jet.mixedDerivativeCoefficient
              (Jet.fullOffDiagonalTwoJet
                (Split.jetData (splitData K k k<K))))

open Equation51SplitLiteralFamily public

jetBetaIsFamilyEvaluator :
  ∀ {History Cell}
    (dataSet : Equation51SplitLiteralFamily History Cell)
    K k (k<K : k ℕ.< K) →
  Jet.beta (Split.jetData (splitData dataSet K k k<K))
  ≡ Cert.beta (certificate dataSet) (historyForShell dataSet K k k<K)
jetBetaIsFamilyEvaluator dataSet K k k<K
  rewrite splitUsesFamilyCertificate dataSet K k k<K
        | splitUsesPhysicalHistory dataSet K k k<K =
  Split.jetBetaIsFiniteEvaluator (splitData dataSet K k k<K)

asRound103SameObjectData :
  ∀ {History Cell} →
  Equation51SplitLiteralFamily History Cell →
  R103.Equation51FiveChannelSameObjectData History Cell
asRound103SameObjectData dataSet = record
  { R103.Equation51FiveChannelSameObjectData.embedding = embedding dataSet
  ; R103.Equation51FiveChannelSameObjectData.certificate = certificate dataSet
  ; R103.Equation51FiveChannelSameObjectData.historyWitness = historyWitness dataSet
  ; R103.Equation51FiveChannelSameObjectData.dynamics = dynamics dataSet
  ; R103.Equation51FiveChannelSameObjectData.historyForShell = historyForShell dataSet
  ; R103.Equation51FiveChannelSameObjectData.jetData =
      λ K k k<K → Split.jetData (splitData dataSet K k k<K)
  ; R103.Equation51FiveChannelSameObjectData.actualDerivativeIsEmbeddedNegativeMixedJet =
      actualDerivativeIsEmbeddedNegativeMixedJet dataSet
  ; R103.Equation51FiveChannelSameObjectData.jetBetaIsCertifiedEvaluator =
      jetBetaIsFamilyEvaluator dataSet
  }

round108A1SplitToLiteralCMP109CompilerLevel : ProofLevel
round108A1SplitToLiteralCMP109CompilerLevel = machineChecked

-- Remaining A1 source leaves are now local component identifications rather than
-- a whole-beta equality: Gaussian mixed jet, normalized interaction mixed jet,
-- and the literal Eq.(5.1) derivative-to-two-jet coordinate identification.
round108A1LiteralComponentInstantiationLevel : ProofLevel
round108A1LiteralComponentInstantiationLevel = conditional
