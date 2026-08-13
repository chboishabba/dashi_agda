module DASHI.Physics.YangMills.BalabanYM4RGCommonBudgetClosureExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions",
-- Communications in Mathematical Physics 116 (1988), 1--22.
-- DOI: 10.1007/BF01239022.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation",
-- Communications in Mathematical Physics 122 (1989), 355--392.
-- DOI: 10.1007/BF01238433.
--
-- Roman Kotecky and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- DASHI CONTRIBUTION
--
-- The first genuinely coupled RG budget should not prove five estimates in
-- isolation and hope their constants reconcile later.  This module proves the
-- central invariant-region arithmetic for the small-field/polymer coordinate:
--
--   K' <= q K + E,       0 <= q <= 1,
--   K  <= Kmax,
--   E  <= (1-q) Kmax
--
-- implies K' <= Kmax.
--
-- It then inserts that derived conclusion together with the large-field,
-- covariance, coupling and decay estimates into the existing YM4 RG region.
-- The analytic estimates themselves remain the research inputs; the shared
-- slack identity cannot drift between independently tuned modules.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanYM4RGInvariantRegionPhysicalGapExact as RG

smallFieldContractionFitsCap :
  ∀ q current next error cap →
  0ℚ ≤ q →
  q ≤ 1ℚ →
  current ≤ cap →
  next ≤ q * current + error →
  error ≤ (1ℚ - q) * cap →
  next ≤ cap
smallFieldContractionFitsCap q current next error cap
    qNonnegative qAtMostOne currentBound nextBound errorFits =
  let
    scaledCurrent : q * current ≤ q * cap
    scaledCurrent = Norm.scaleNonnegative q qNonnegative currentBound

    combined :
      q * current + error
      ≤ q * cap + (1ℚ - q) * cap
    combined = ℚP.+-mono-≤ scaledCurrent errorFits

    closes : q * cap + (1ℚ - q) * cap ≡ cap
    closes = ℚRing.solve-∀ q cap
  in
  ℚP.≤-trans nextBound
    (subst
      (λ upper → q * current + error ≤ upper)
      closes combined)

record CoupledOneStepAnalyticBounds
    (parameters : RG.YM4RGRegionParameters)
    (current next : RG.YM4RGState) : Set where
  field
    contraction error : ℚ
    contractionNonnegative : 0ℚ ≤ contraction
    contractionAtMostOne : contraction ≤ 1ℚ

    smallFieldOneStep :
      RG.smallFieldPolymerNorm next
      ≤ contraction * RG.smallFieldPolymerNorm current + error

    perturbativeErrorFitsSlack :
      error
      ≤ (1ℚ - contraction) * RG.smallFieldCap parameters

    couplingNextControlled :
      RG.runningCoupling next ≤ RG.couplingCap parameters

    largeFieldNextControlled :
      RG.largeFieldActivity next ≤ RG.largeFieldCap parameters

    covarianceNextControlled :
      RG.conditionalCovarianceNorm next ≤ RG.covarianceCap parameters

    decayNextNonnegative : 0ℚ ≤ RG.latticeDecayExponent next
    spacingNextNonnegative : 0ℚ ≤ RG.inversePhysicalSpacing next

open CoupledOneStepAnalyticBounds public

coupledOneStepPreservesAnalyticRegion :
  ∀ {parameters current next} →
  RG.InYM4RGInvariantRegion parameters current →
  CoupledOneStepAnalyticBounds parameters current next →
  RG.InYM4RGInvariantRegion parameters next
coupledOneStepPreservesAnalyticRegion currentRegion estimates = record
  { RG.InYM4RGInvariantRegion.couplingControlled =
      couplingNextControlled estimates
  ; RG.InYM4RGInvariantRegion.smallFieldControlled =
      smallFieldContractionFitsCap
        (contraction estimates)
        (RG.smallFieldPolymerNorm _)
        (RG.smallFieldPolymerNorm _)
        (error estimates)
        (RG.smallFieldCap _)
        (contractionNonnegative estimates)
        (contractionAtMostOne estimates)
        (RG.smallFieldControlled currentRegion)
        (smallFieldOneStep estimates)
        (perturbativeErrorFitsSlack estimates)
  ; RG.InYM4RGInvariantRegion.largeFieldControlled =
      largeFieldNextControlled estimates
  ; RG.InYM4RGInvariantRegion.covarianceControlled =
      covarianceNextControlled estimates
  ; RG.InYM4RGInvariantRegion.latticeDecayNonnegative =
      decayNextNonnegative estimates
  ; RG.InYM4RGInvariantRegion.inverseSpacingNonnegative =
      spacingNextNonnegative estimates
  }

ym4RGSharedSmallFieldBudgetLevel : ProofLevel
ym4RGSharedSmallFieldBudgetLevel = machineChecked

ym4RGCoupledRegionClosureArithmeticLevel : ProofLevel
ym4RGCoupledRegionClosureArithmeticLevel = machineChecked
