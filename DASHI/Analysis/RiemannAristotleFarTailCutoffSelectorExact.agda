module DASHI.Analysis.RiemannAristotleFarTailCutoffSelectorExact where

------------------------------------------------------------------------
-- S2a/S2b JOINT CUTOFF SELECTION
--
-- The far tail decreases as the cutoff moves outward, but the finite signed
-- near core changes at the same time.  Therefore far-tail summability alone
-- must NOT be presented as an automatic selector for the final cutoff.
--
-- Forward capability:
--   a far-tail budget law B_far(J) with eventual smallness.
--
-- Backward requirement:
--   at ONE common J, the near producer leaves a positive allowance epsilon and
--
--       B_near(J) + epsilon < M_cluster,
--       B_far(J) < epsilon.
--
-- The theorem below composes those two inequalities.  A domain producer still
-- has to find the common J; this module does not hide that coupled search.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Product using (Σ; proj₁; proj₂)
open import Data.Rational.Base using (ℚ; _+_; _<_)
import Data.Rational.Properties as ℚP

record FarTailDecayLaw : Set where
  constructor far-tail-decay-law
  field
    farBudgetAt : Nat → ℚ

    -- Eventual smallness supplied by a quantitative shell-tail theorem or a
    -- constructive modulus extracted from the actual summable majorant.
    chooseFarCutoff :
      (allowance : ℚ) →
      (+ 0 / 1) < allowance →
      Σ Nat (λ J → farBudgetAt J < allowance)

open FarTailDecayLaw public

------------------------------------------------------------------------
-- One common cutoff where the growing finite core and shrinking far tail fit
-- simultaneously below the surviving cluster margin.
------------------------------------------------------------------------

record JointNearFarCutoffCertificate (law : FarTailDecayLaw) : Set where
  constructor joint-near-far-cutoff-certificate
  field
    cutoff : Nat
    nearBudget clusterMargin allowance : ℚ

    allowancePositive : (+ 0 / 1) < allowance
    farFitsAllowance : farBudgetAt law cutoff < allowance
    nearPlusAllowanceBelowCluster :
      nearBudget + allowance < clusterMargin

open JointNearFarCutoffCertificate public

jointCombinedBudgetBelowCluster :
  (law : FarTailDecayLaw) →
  (d : JointNearFarCutoffCertificate law) →
  nearBudget d + farBudgetAt law (cutoff d) < clusterMargin d
jointCombinedBudgetBelowCluster law d =
  ℚP.<-trans
    (ℚP.+-monoʳ-< (nearBudget d) (farFitsAllowance d))
    (nearPlusAllowanceBelowCluster d)

------------------------------------------------------------------------
-- Far-only selector remains useful as a producer helper, but it is explicitly
-- not the final coupled cutoff selector.
------------------------------------------------------------------------

farOnlySelectedCutoff :
  (law : FarTailDecayLaw) →
  (allowance : ℚ) →
  (+ 0 / 1) < allowance → Nat
farOnlySelectedCutoff law allowance positive =
  proj₁ (chooseFarCutoff law allowance positive)

farOnlySelectedCutoffFits :
  (law : FarTailDecayLaw) →
  (allowance : ℚ) →
  (positive : (+ 0 / 1) < allowance) →
  farBudgetAt law (farOnlySelectedCutoff law allowance positive) < allowance
farOnlySelectedCutoffFits law allowance positive =
  proj₂ (chooseFarCutoff law allowance positive)

------------------------------------------------------------------------
-- Research boundary.
------------------------------------------------------------------------

record FarTailCutoffSelectorBoundary : Set where
  constructor far-tail-cutoff-selector-boundary
  field
    absoluteSummabilityKnownInLean : Bool
    absoluteSummabilityKnownInLeanIsTrue :
      absoluteSummabilityKnownInLean ≡ true

    farTailEventualSmallnessIsCorrectProducerShape : Bool
    farTailEventualSmallnessIsCorrectProducerShapeIsTrue :
      farTailEventualSmallnessIsCorrectProducerShape ≡ true

    farTailDecayAloneSelectsFinalJointCutoff : Bool
    farTailDecayAloneSelectsFinalJointCutoffIsFalse :
      farTailDecayAloneSelectsFinalJointCutoff ≡ false

    jointNearFarCutoffCompilerClosed : Bool
    jointNearFarCutoffCompilerClosedIsTrue :
      jointNearFarCutoffCompilerClosed ≡ true

    explicitLeanTailModulusTransportedToAgda : Bool
    explicitLeanTailModulusTransportedToAgdaIsFalse :
      explicitLeanTailModulusTransportedToAgda ≡ false

canonicalFarTailCutoffSelectorBoundary : FarTailCutoffSelectorBoundary
canonicalFarTailCutoffSelectorBoundary =
  far-tail-cutoff-selector-boundary
    true refl
    true refl
    false refl
    true refl
    false refl
