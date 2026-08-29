{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact where

------------------------------------------------------------------------
-- ROUND102 A REPRESENTATION BRIDGE
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; _≤_; _<_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; _≤ℝ_; _<ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanA1HistoryUniformTwoSidedBetaRound102Exact as Cert
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaLowerRemainderExact as Beta

record OrderedRationalRealEmbedding : Set₁ where
  field
    embed : ℚ → ℝ
    orderPreserving : ∀ {a b} → a ≤ b → embed a ≤ℝ embed b
    strictOrderPreserving : ∀ {a b} → a < b → embed a <ℝ embed b

open OrderedRationalRealEmbedding public

record LiteralRealBetaFromRationalCertificate
    {History Cell : Set}
    (embedding : OrderedRationalRealEmbedding)
    (certificate : Cert.HistoryUniformTwoSidedBetaData History Cell) : Set₁ where
  field
    historyForShell : History
    literalMixedDerivative : ℝ
    literalMixedDerivativeExact :
      literalMixedDerivative
      ≡ embed embedding (Cert.beta certificate historyForShell)

open LiteralRealBetaFromRationalCertificate public

realLowerSlope :
  ∀ {History Cell}
    (embedding : OrderedRationalRealEmbedding)
    (certificate : Cert.HistoryUniformTwoSidedBetaData History Cell) → ℝ
realLowerSlope embedding certificate =
  embed embedding (Beta.half * Cert.gaussianFloor certificate)

realUpperSlope :
  ∀ {History Cell}
    (embedding : OrderedRationalRealEmbedding)
    (certificate : Cert.HistoryUniformTwoSidedBetaData History Cell) → ℝ
realUpperSlope embedding certificate =
  embed embedding
    (Cert.gaussianCeiling certificate
      + Beta.half * Cert.gaussianFloor certificate)

literalMixedDerivativeRealLower :
  ∀ {History Cell}
    {embedding : OrderedRationalRealEmbedding}
    {certificate : Cert.HistoryUniformTwoSidedBetaData History Cell}
    (dataSet : LiteralRealBetaFromRationalCertificate embedding certificate) →
  realLowerSlope embedding certificate ≤ℝ literalMixedDerivative dataSet
literalMixedDerivativeRealLower {embedding = embedding} {certificate = certificate} dataSet =
  subst
    (λ right → realLowerSlope embedding certificate ≤ℝ right)
    (sym (literalMixedDerivativeExact dataSet))
    (orderPreserving embedding
      (Cert.halfFloorBelowBeta certificate (historyForShell dataSet)))

literalMixedDerivativeRealUpper :
  ∀ {History Cell}
    {embedding : OrderedRationalRealEmbedding}
    {certificate : Cert.HistoryUniformTwoSidedBetaData History Cell}
    (dataSet : LiteralRealBetaFromRationalCertificate embedding certificate) →
  literalMixedDerivative dataSet ≤ℝ realUpperSlope embedding certificate
literalMixedDerivativeRealUpper {embedding = embedding} {certificate = certificate} dataSet =
  subst
    (λ left → left ≤ℝ realUpperSlope embedding certificate)
    (sym (literalMixedDerivativeExact dataSet))
    (orderPreserving embedding
      (Cert.betaBelowGaussianCeilingPlusHalfFloor certificate (historyForShell dataSet)))

rationalCertificateToRealBetaSlopeLevel : ProofLevel
rationalCertificateToRealBetaSlopeLevel = machineChecked

orderedRationalRealEmbeddingLevel : ProofLevel
orderedRationalRealEmbeddingLevel = standardImported

literalCMP109MixedDerivativeRationalCertificateIdentificationLevel : ProofLevel
literalCMP109MixedDerivativeRationalCertificateIdentificationLevel = conditional
