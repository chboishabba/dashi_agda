module DASHI.Physics.YangMills.BalabanFiniteRGGoodBadResidualEnvelopeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- R. Kotecky and D. Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- P. K. Mitter,
-- "The Exact Renormalization Group", Encyclopedia of Mathematical Physics
-- (Elsevier, 2006), arXiv:math-ph/0505008. No DOI recorded for the cited
-- encyclopedia preprint.
--
-- DASHI CONTRIBUTION
--
-- The exact law of total covariance already gives, at every finite RG step,
--
--   Cov_j = Cov_{j+1} + R_j.
--
-- The physically useful decomposition of the remainder is not "small field"
-- versus "large field" as two unrelated calculations.  It is
--
--   R_j = G_j + E_j,
--
-- where G_j is the controlled-fibre contribution (the region on which the
-- local reopening/cluster machinery contracts), while E_j is the exceptional
-- contribution (the region whose measure must be uniformly suppressed).
--
-- This module proves the exact finite algebra needed by that strategy:
--
--   |Cov_0|
--     <= |Cov_N| + sum_j goodBudget_j + sum_j exceptionalBudget_j.
--
-- It also proves the one-step statement directly for the repository's literal
-- finite reopening kernel, and a final clustering transfer theorem: any
-- summable physical-distance envelope for the terminal term plus the two
-- residual channels is automatically an envelope for the original connected
-- covariance.  Thus the future YM4 producers have only the analytic jobs
--
--   good region: contraction,
--   exceptional region: suppression,
--
-- rather than any further telescoping bookkeeping.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanFiniteRGTotalCovarianceExact as Total
import DASHI.Physics.YangMills.BalabanFiniteRGMultiscaleCovarianceTelescopingExact as Telescope

------------------------------------------------------------------------
-- One literal reopening step with an exact controlled/exceptional split.
------------------------------------------------------------------------

record FibreGoodBadSplit
    {Fine Coarse : Set}
    (step : Reopen.FiniteRGReopeningStep Fine Coarse)
    (left right : Reopen.Observable Fine) : Set where
  field
    goodContribution exceptionalContribution : ℚ

    fibreSplitExact :
      Telescope.fibreCovarianceContribution step left right
      ≡ goodContribution + exceptionalContribution

open FibreGoodBadSplit public

finiteRGOneStepGoodBadCovarianceUpper :
  ∀ {Fine Coarse}
    (step : Reopen.FiniteRGReopeningStep Fine Coarse)
    (left right : Reopen.Observable Fine)
    (split : FibreGoodBadSplit step left right)
    coarseBudget goodBudget exceptionalBudget →
  ∣ Total.coarseCovariance step
      (Reopen.transportObservable step left)
      (Reopen.transportObservable step right) ∣ ≤ coarseBudget →
  ∣ goodContribution split ∣ ≤ goodBudget →
  ∣ exceptionalContribution split ∣ ≤ exceptionalBudget →
  ∣ Total.fineCovariance step left right ∣
    ≤ coarseBudget + goodBudget + exceptionalBudget
finiteRGOneStepGoodBadCovarianceUpper
    step left right split coarseBudget goodBudget exceptionalBudget
    coarseBound goodBound exceptionalBound =
  let
    coarse = Total.coarseCovariance step
      (Reopen.transportObservable step left)
      (Reopen.transportObservable step right)
    good = goodContribution split
    exceptional = exceptionalContribution split
    fibre = Telescope.fibreCovarianceContribution step left right

    fineSplit : Total.fineCovariance step left right ≡ coarse + fibre
    fineSplit = Total.finiteRGTotalCovariance step left right

    fibreAbs : ∣ fibre ∣ ≤ goodBudget + exceptionalBudget
    fibreAbs =
      subst
        (λ selected → ∣ selected ∣ ≤ goodBudget + exceptionalBudget)
        (sym (fibreSplitExact split))
        (ℚP.≤-trans
          (ℚP.∣p+q∣≤∣p∣+∣q∣ good exceptional)
          (ℚP.+-mono-≤ goodBound exceptionalBound))

    first : ∣ Total.fineCovariance step left right ∣
      ≤ ∣ coarse ∣ + ∣ fibre ∣
    first =
      subst
        (λ selected → ∣ selected ∣ ≤ ∣ coarse ∣ + ∣ fibre ∣)
        (sym fineSplit)
        (ℚP.∣p+q∣≤∣p∣+∣q∣ coarse fibre)

    second : ∣ coarse ∣ + ∣ fibre ∣
      ≤ coarseBudget + (goodBudget + exceptionalBudget)
    second = ℚP.+-mono-≤ coarseBound fibreAbs

    associativity∀ :
      ∀ (a b c : ℚ) → a + (b + c) ≡ a + b + c
    associativity∀ = ℚRing.solve-∀

    associativity :
      coarseBudget + (goodBudget + exceptionalBudget)
      ≡ coarseBudget + goodBudget + exceptionalBudget
    associativity =
      associativity∀ coarseBudget goodBudget exceptionalBudget
  in
  ℚP.≤-trans first
    (subst
      (λ upper →
        ∣ coarse ∣ + ∣ fibre ∣ ≤ upper)
      associativity
      second)

------------------------------------------------------------------------
-- A proof-bearing finite multiscale chain with both residual channels.
------------------------------------------------------------------------

data GoodBadCovarianceChain : ℚ → Set where
  terminal : (value : ℚ) → GoodBadCovarianceChain value
  prepend : ∀ {fine coarse : ℚ} →
    (remainder goodContribution exceptionalContribution : ℚ) →
    fine ≡ coarse + remainder →
    remainder ≡ goodContribution + exceptionalContribution →
    GoodBadCovarianceChain coarse →
    GoodBadCovarianceChain fine

terminalCovariance : ∀ {fine} → GoodBadCovarianceChain fine → ℚ
terminalCovariance (terminal value) = value
terminalCovariance (prepend remainder good exceptional fineExact split tail) =
  terminalCovariance tail

goodContributionSum : ∀ {fine} → GoodBadCovarianceChain fine → ℚ
goodContributionSum (terminal value) = 0ℚ
goodContributionSum (prepend remainder good exceptional fineExact split tail) =
  goodContributionSum tail + good

exceptionalContributionSum : ∀ {fine} → GoodBadCovarianceChain fine → ℚ
exceptionalContributionSum (terminal value) = 0ℚ
exceptionalContributionSum
    (prepend remainder good exceptional fineExact split tail) =
  exceptionalContributionSum tail + exceptional

absoluteGoodContributionSum : ∀ {fine} → GoodBadCovarianceChain fine → ℚ
absoluteGoodContributionSum (terminal value) = 0ℚ
absoluteGoodContributionSum
    (prepend remainder good exceptional fineExact split tail) =
  absoluteGoodContributionSum tail + ∣ good ∣

absoluteExceptionalContributionSum : ∀ {fine} → GoodBadCovarianceChain fine → ℚ
absoluteExceptionalContributionSum (terminal value) = 0ℚ
absoluteExceptionalContributionSum
    (prepend remainder good exceptional fineExact split tail) =
  absoluteExceptionalContributionSum tail + ∣ exceptional ∣

goodBadAbsoluteEnvelope : ∀ {fine} → GoodBadCovarianceChain fine → ℚ
goodBadAbsoluteEnvelope chain =
  ∣ terminalCovariance chain ∣
  + absoluteGoodContributionSum chain
  + absoluteExceptionalContributionSum chain

finiteRGGoodBadCovarianceTelescopes :
  ∀ {fine} (chain : GoodBadCovarianceChain fine) →
  fine ≡ terminalCovariance chain
    + goodContributionSum chain
    + exceptionalContributionSum chain
finiteRGGoodBadCovarianceTelescopes (terminal value) =
  trans
    (sym (ℚP.+-identityʳ value))
    (sym (ℚP.+-identityʳ (value + 0ℚ)))
finiteRGGoodBadCovarianceTelescopes
    (prepend {fine} {coarse} remainder good exceptional
      fineExact split tail) =
  let
    regroup∀ :
      ∀ (t g e dg de : ℚ) →
        (t + g + e) + (dg + de) ≡ t + (g + dg) + (e + de)
    regroup∀ = ℚRing.solve-∀

    regroup :
      terminalCovariance tail + goodContributionSum tail
        + exceptionalContributionSum tail + (good + exceptional)
      ≡ terminalCovariance
          (prepend remainder good exceptional fineExact split tail)
        + goodContributionSum
          (prepend remainder good exceptional fineExact split tail)
        + exceptionalContributionSum
          (prepend remainder good exceptional fineExact split tail)
    regroup =
      regroup∀
        (terminalCovariance tail)
        (goodContributionSum tail)
        (exceptionalContributionSum tail)
        good exceptional
  in
  trans fineExact
    (trans
      (cong (coarse +_) split)
      (trans
        (cong
          (λ selected → selected + (good + exceptional))
          (finiteRGGoodBadCovarianceTelescopes tail))
        regroup))

finiteRGGoodBadAbsoluteCovarianceUpper :
  ∀ {fine} (chain : GoodBadCovarianceChain fine) →
  ∣ fine ∣ ≤ goodBadAbsoluteEnvelope chain
finiteRGGoodBadAbsoluteCovarianceUpper (terminal value) =
  let
    terminalId∀ : ∀ (a : ℚ) → a + 0ℚ + 0ℚ ≡ a
    terminalId∀ = ℚRing.solve-∀

    terminalId : ∣ value ∣ + 0ℚ + 0ℚ ≡ ∣ value ∣
    terminalId = terminalId∀ ∣ value ∣
  in
  subst
    (λ upper → ∣ value ∣ ≤ upper)
    (sym terminalId)
    ℚP.≤-refl
finiteRGGoodBadAbsoluteCovarianceUpper
    (prepend {fine} {coarse} remainder good exceptional
      fineExact split tail) =
  let
    remainderBound : ∣ remainder ∣ ≤ ∣ good ∣ + ∣ exceptional ∣
    remainderBound =
      subst
        (λ selected → ∣ selected ∣ ≤ ∣ good ∣ + ∣ exceptional ∣)
        (sym split)
        (ℚP.∣p+q∣≤∣p∣+∣q∣ good exceptional)

    first : ∣ fine ∣ ≤ ∣ coarse ∣ + ∣ remainder ∣
    first =
      subst
        (λ selected → ∣ selected ∣ ≤ ∣ coarse ∣ + ∣ remainder ∣)
        (sym fineExact)
        (ℚP.∣p+q∣≤∣p∣+∣q∣ coarse remainder)

    second : ∣ coarse ∣ + ∣ remainder ∣
      ≤ goodBadAbsoluteEnvelope tail + (∣ good ∣ + ∣ exceptional ∣)
    second = ℚP.+-mono-≤
      (finiteRGGoodBadAbsoluteCovarianceUpper tail)
      remainderBound

    envelopeId∀ :
      ∀ (t g e dg de : ℚ) →
        (t + g + e) + (dg + de) ≡ t + (g + dg) + (e + de)
    envelopeId∀ = ℚRing.solve-∀

    envelopeId :
      goodBadAbsoluteEnvelope tail + (∣ good ∣ + ∣ exceptional ∣)
      ≡ goodBadAbsoluteEnvelope
          (prepend remainder good exceptional fineExact split tail)
    envelopeId =
      envelopeId∀
        (∣ terminalCovariance tail ∣)
        (absoluteGoodContributionSum tail)
        (absoluteExceptionalContributionSum tail)
        ∣ good ∣ ∣ exceptional ∣
  in
  ℚP.≤-trans first
    (subst
      (λ upper →
        ∣ coarse ∣ + ∣ remainder ∣ ≤ upper)
      envelopeId
      second)

------------------------------------------------------------------------
-- Budgeted form: analytic producers may bound the two channels independently.
------------------------------------------------------------------------

record GoodBadBudget
    {fine : ℚ}
    (chain : GoodBadCovarianceChain fine) : Set₁ where
  field
    goodBudget exceptionalBudget : ℚ

    goodSumBound :
      absoluteGoodContributionSum chain ≤ goodBudget

    exceptionalSumBound :
      absoluteExceptionalContributionSum chain ≤ exceptionalBudget

open GoodBadBudget public

finiteRGBudgetedGoodBadAbsoluteUpper :
  ∀ {fine} (chain : GoodBadCovarianceChain fine)
    (budget : GoodBadBudget chain) →
  ∣ fine ∣ ≤
    ∣ terminalCovariance chain ∣
      + goodBudget budget + exceptionalBudget budget
finiteRGBudgetedGoodBadAbsoluteUpper chain budget =
  let
    terminalRefl :
      ∣ terminalCovariance chain ∣ ≤ ∣ terminalCovariance chain ∣
    terminalRefl = ℚP.≤-refl

    goodStep :
      ∣ terminalCovariance chain ∣ + absoluteGoodContributionSum chain
      ≤ ∣ terminalCovariance chain ∣ + goodBudget budget
    goodStep =
      ℚP.+-mono-≤ terminalRefl (goodSumBound budget)

    exceptionalStep :
      (∣ terminalCovariance chain ∣ + absoluteGoodContributionSum chain)
        + absoluteExceptionalContributionSum chain
      ≤ (∣ terminalCovariance chain ∣ + goodBudget budget)
        + exceptionalBudget budget
    exceptionalStep =
      ℚP.+-mono-≤ goodStep (exceptionalSumBound budget)
  in
  ℚP.≤-trans
    (finiteRGGoodBadAbsoluteCovarianceUpper chain)
    exceptionalStep

------------------------------------------------------------------------
-- Physical-distance transfer.  The only remaining input is now a genuinely
-- analytic, summable bound on terminal + controlled + exceptional channels.
------------------------------------------------------------------------

finiteRGClusteringFromGoodBadEnvelope :
  ∀ {Distance : Set} {fine : ℚ}
    (chain : GoodBadCovarianceChain fine)
    (budget : GoodBadBudget chain)
    (distance : Distance)
    (physicalEnvelope : Distance → ℚ) →
  ∣ terminalCovariance chain ∣
      + goodBudget budget + exceptionalBudget budget
    ≤ physicalEnvelope distance →
  ∣ fine ∣ ≤ physicalEnvelope distance
finiteRGClusteringFromGoodBadEnvelope chain budget distance physicalEnvelope
    envelopeBound =
  ℚP.≤-trans
    (finiteRGBudgetedGoodBadAbsoluteUpper chain budget)
    envelopeBound

finiteRGOneStepGoodBadResidualLevel : ProofLevel
finiteRGOneStepGoodBadResidualLevel = machineChecked

finiteRGGoodBadCovarianceTelescopeLevel : ProofLevel
finiteRGGoodBadCovarianceTelescopeLevel = machineChecked

finiteRGGoodBadAbsoluteEnvelopeLevel : ProofLevel
finiteRGGoodBadAbsoluteEnvelopeLevel = machineChecked

goodRegionConditionalFibreContractionLevel : ProofLevel
goodRegionConditionalFibreContractionLevel = conditional

exceptionalLargeFieldSuppressionLevel : ProofLevel
exceptionalLargeFieldSuppressionLevel = conditional
