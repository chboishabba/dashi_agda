module DASHI.Physics.YangMills.BalabanFiniteRGMultiscaleCovarianceTelescopingExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- R. Kotecky and D. Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- P. K. Mitter,
-- "The Exact Renormalization Group", Encyclopedia of Mathematical Physics
-- (Elsevier, 2006), arXiv:math-ph/0505008. No DOI recorded for the cited
-- encyclopedia preprint; persistent identifier arXiv:math-ph/0505008.
--
-- DASHI CONTRIBUTION
--
-- Turn the exact one-step law of total covariance into the algebra needed by
-- a genuine multiscale clustering proof.  First prove the one-step absolute
-- inequality
--
--   |Cov_j| <= |Cov_{j+1}| + |fibreCov_j|.
--
-- Then define a proof-bearing finite covariance chain whose every edge is an
-- exact decomposition `fine = coarse + remainder`.  Structural induction,
-- not an assumed telescoping identity, proves
--
--   Cov_0 = Cov_N + sum_j remainder_j
--
-- and the absolute envelope
--
--   |Cov_0| <= |Cov_N| + sum_j |remainder_j|.
--
-- The future frontier theorem `ym4ConditionalFibreCovarianceContractsOneStep`
-- therefore has one sharply isolated job: bound the actual conditional fibre
-- remainder at each physical RG scale.  Once those bounds are summable, no
-- additional covariance algebra remains.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanFiniteRGTotalCovarianceExact as Total

------------------------------------------------------------------------
-- One actual RG reopening step: exact split and absolute upper bound.
------------------------------------------------------------------------

fibreCovarianceContribution :
  ∀ {Fine Coarse} →
  Reopen.FiniteRGReopeningStep Fine Coarse →
  Reopen.Observable Fine → Reopen.Observable Fine → ℚ
fibreCovarianceContribution step left right =
  Reopen.coarseExpectation step (Total.conditionalCovariance step left right)

finiteRGOneStepAbsoluteCovarianceUpper :
  ∀ {Fine Coarse}
    (step : Reopen.FiniteRGReopeningStep Fine Coarse)
    (left right : Reopen.Observable Fine)
    coarseUpper fibreUpper →
  ∣ Total.coarseCovariance step
      (Reopen.transportObservable step left)
      (Reopen.transportObservable step right) ∣ ≤ coarseUpper →
  ∣ fibreCovarianceContribution step left right ∣ ≤ fibreUpper →
  ∣ Total.fineCovariance step left right ∣ ≤ coarseUpper + fibreUpper
finiteRGOneStepAbsoluteCovarianceUpper
    step left right coarseUpper fibreUpper coarseBound fibreBound =
  let
    coarse = Total.coarseCovariance step
      (Reopen.transportObservable step left)
      (Reopen.transportObservable step right)
    fibre = fibreCovarianceContribution step left right

    splitAbs :
      ∣ Total.fineCovariance step left right ∣ ≡ ∣ coarse + fibre ∣
    splitAbs = cong ∣_∣ (Total.finiteRGTotalCovariance step left right)

    triangle : ∣ coarse + fibre ∣ ≤ ∣ coarse ∣ + ∣ fibre ∣
    triangle = ℚP.∣p+q∣≤∣p∣+∣q∣ coarse fibre

    bounded = ℚP.+-mono-≤ coarseBound fibreBound
  in
  subst
    (λ lower → lower ≤ coarseUpper + fibreUpper)
    (sym splitAbs)
    (ℚP.≤-trans triangle bounded)

------------------------------------------------------------------------
-- Exact finite multiscale chain.
------------------------------------------------------------------------

data ExactCovarianceChain : ℚ → Set where
  terminal : (value : ℚ) → ExactCovarianceChain value
  prepend : ∀ {fine coarse : ℚ} →
    (remainder : ℚ) →
    fine ≡ coarse + remainder →
    ExactCovarianceChain coarse →
    ExactCovarianceChain fine

terminalCovariance : ∀ {fine} → ExactCovarianceChain fine → ℚ
terminalCovariance (terminal value) = value
terminalCovariance (prepend remainder exact tail) = terminalCovariance tail

fibreRemainderSum : ∀ {fine} → ExactCovarianceChain fine → ℚ
fibreRemainderSum (terminal value) = 0ℚ
fibreRemainderSum (prepend remainder exact tail) =
  fibreRemainderSum tail + remainder

absoluteFibreRemainderSum : ∀ {fine} → ExactCovarianceChain fine → ℚ
absoluteFibreRemainderSum (terminal value) = 0ℚ
absoluteFibreRemainderSum (prepend remainder exact tail) =
  absoluteFibreRemainderSum tail + ∣ remainder ∣

absoluteCovarianceEnvelope : ∀ {fine} → ExactCovarianceChain fine → ℚ
absoluteCovarianceEnvelope chain =
  ∣ terminalCovariance chain ∣ + absoluteFibreRemainderSum chain

finiteRGMultiscaleCovarianceTelescopes :
  ∀ {fine} (chain : ExactCovarianceChain fine) →
  fine ≡ terminalCovariance chain + fibreRemainderSum chain
finiteRGMultiscaleCovarianceTelescopes (terminal value) =
  sym (ℚP.+-identityʳ value)
finiteRGMultiscaleCovarianceTelescopes
    (prepend {fine} {coarse} remainder stepExact tail) =
  trans stepExact
    (trans
      (cong (_+ remainder)
        (finiteRGMultiscaleCovarianceTelescopes tail))
      (ℚRing.solve-∀
        (terminalCovariance tail)
        (fibreRemainderSum tail)
        remainder))

finiteRGMultiscaleAbsoluteCovarianceUpper :
  ∀ {fine} (chain : ExactCovarianceChain fine) →
  ∣ fine ∣ ≤ absoluteCovarianceEnvelope chain
finiteRGMultiscaleAbsoluteCovarianceUpper (terminal value) =
  subst
    (λ upper → ∣ value ∣ ≤ upper)
    (sym (ℚP.+-identityʳ ∣ value ∣))
    ℚP.≤-refl
finiteRGMultiscaleAbsoluteCovarianceUpper
    (prepend {fine} {coarse} remainder stepExact tail) =
  let
    oneStep : ∣ fine ∣ ≤ ∣ coarse ∣ + ∣ remainder ∣
    oneStep =
      subst
        (λ lower → lower ≤ ∣ coarse ∣ + ∣ remainder ∣)
        (sym (cong ∣_∣ stepExact))
        (ℚP.∣p+q∣≤∣p∣+∣q∣ coarse remainder)

    tailUpper = finiteRGMultiscaleAbsoluteCovarianceUpper tail
    lifted = ℚP.+-mono-≤ tailUpper ℚP.≤-refl
  in
  ℚP.≤-trans oneStep
    (subst
      (λ upper →
        ∣ coarse ∣ + ∣ remainder ∣ ≤ upper)
      (ℚRing.solve-∀
        ∣ terminalCovariance tail ∣
        (absoluteFibreRemainderSum tail)
        ∣ remainder ∣)
      lifted)

------------------------------------------------------------------------
-- Canonical chain generated by one literal finite reopening step.
------------------------------------------------------------------------

finiteRGOneStepCovarianceChain :
  ∀ {Fine Coarse}
    (step : Reopen.FiniteRGReopeningStep Fine Coarse)
    (left right : Reopen.Observable Fine) →
  ExactCovarianceChain (Total.fineCovariance step left right)
finiteRGOneStepCovarianceChain step left right =
  let
    coarse = Total.coarseCovariance step
      (Reopen.transportObservable step left)
      (Reopen.transportObservable step right)
    fibre = fibreCovarianceContribution step left right
  in
  prepend fibre
    (Total.finiteRGTotalCovariance step left right)
    (terminal coarse)

finiteRGOneStepChainTelescopes :
  ∀ {Fine Coarse}
    (step : Reopen.FiniteRGReopeningStep Fine Coarse)
    (left right : Reopen.Observable Fine) →
  Total.fineCovariance step left right
  ≡ terminalCovariance (finiteRGOneStepCovarianceChain step left right)
    + fibreRemainderSum (finiteRGOneStepCovarianceChain step left right)
finiteRGOneStepChainTelescopes step left right =
  finiteRGMultiscaleCovarianceTelescopes
    (finiteRGOneStepCovarianceChain step left right)

finiteRGOneStepAbsoluteCovarianceLevel : ProofLevel
finiteRGOneStepAbsoluteCovarianceLevel = machineChecked

finiteRGMultiscaleCovarianceTelescopingLevel : ProofLevel
finiteRGMultiscaleCovarianceTelescopingLevel = machineChecked

finiteRGMultiscaleCovarianceAbsoluteEnvelopeLevel : ProofLevel
finiteRGMultiscaleCovarianceAbsoluteEnvelopeLevel = machineChecked

ym4ConditionalFibreCovarianceContractionLevel : ProofLevel
ym4ConditionalFibreCovarianceContractionLevel = conditional
