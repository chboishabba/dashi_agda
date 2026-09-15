{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCoefficientCollarChargeRound355Exact where

------------------------------------------------------------------------
-- ROUND355 / COEFFICIENT-COLLAR GEOMETRY IS THE LIVE MARKED CHARGE
--
-- R354 isolates the source/application inequality
--
--   rawMarkedMajorant <= chargedMajorant
--
-- from the ordinary CMP116 summation which follows it.  The retained source
-- ledger gives the immediately upstream geometric statement in exponent form:
--
--   delta_mark * markedDistance + kappa * treeLength
--     >= delta_collar * collarRadius + kappa' * treeLength,
--
-- with kappa' > 0, for the near region.
--
-- CMP109 supplies the raw dichotomy behind this inequality.  Relative to a
-- coefficient cube D, a localization X either receives enough marked/domain
-- distance, or it reaches beyond the enlarged collar and connectedness forces
-- enough tree/localization length.  This file proves ONLY the ordered-real
-- assembly of those two alternatives.  It does not manufacture the geometric
-- dichotomy, identify the CMP109/CMP99 coordinates with R354's majorants, or
-- use source citation/status as proof.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; _+ℝ_ ; _*ℝ_ ; _≤ℝ_
  ; ≤ℝ-refl ; ≤ℝ-trans ; +-mono-≤ ; +-identityˡ )
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Source-shaped scalar geometry.
------------------------------------------------------------------------

record CoefficientCollarChargeGeometry : Set₁ where
  field
    deltaMark markedDistance : ℝ
    kappa treeLength : ℝ
    deltaCollar collarRadius : ℝ
    residualKappa : ℝ

    -- The marked exponential factor must be nonnegative as a scalar charge.
    markedChargeNonnegative :
      0ℝ ≤ℝ deltaMark *ℝ markedDistance

    -- Retaining kappa' of the tree exponent leaves no more tree charge than the
    -- original kappa-weighted activity supplied.
    residualTreeBelowOriginalTree :
      residualKappa *ℝ treeLength ≤ℝ kappa *ℝ treeLength

    -- Literal CMP109/CMP99 collar dichotomy, after all distances are expressed
    -- on one block scale.  Branch 1 is the marked-distance payment.  Branch 2
    -- is the large-localization payment and already retains the residual tree
    -- exponent needed by the subsequent CMP116 sum.
    coefficientCollarDichotomy :
      (deltaCollar *ℝ collarRadius
        ≤ℝ deltaMark *ℝ markedDistance)
      ⊎
      ((deltaCollar *ℝ collarRadius)
        +ℝ (residualKappa *ℝ treeLength)
        ≤ℝ kappa *ℝ treeLength)

open CoefficientCollarChargeGeometry public

combinedMarkedTreeCharge : CoefficientCollarChargeGeometry → ℝ
combinedMarkedTreeCharge dataSet =
  deltaMark dataSet *ℝ markedDistance dataSet
  +ℝ kappa dataSet *ℝ treeLength dataSet

requiredCollarResidualCharge : CoefficientCollarChargeGeometry → ℝ
requiredCollarResidualCharge dataSet =
  deltaCollar dataSet *ℝ collarRadius dataSet
  +ℝ residualKappa dataSet *ℝ treeLength dataSet

markedTermPlusTreeDominatesTree :
  (dataSet : CoefficientCollarChargeGeometry) →
  kappa dataSet *ℝ treeLength dataSet
    ≤ℝ combinedMarkedTreeCharge dataSet
markedTermPlusTreeDominatesTree dataSet =
  subst
    (λ lower → lower ≤ℝ combinedMarkedTreeCharge dataSet)
    (+-identityˡ (kappa dataSet *ℝ treeLength dataSet))
    (+-mono-≤
      (markedChargeNonnegative dataSet)
      ≤ℝ-refl)

coefficientCollarDichotomyPaysLinearCharge :
  (dataSet : CoefficientCollarChargeGeometry) →
  requiredCollarResidualCharge dataSet
    ≤ℝ combinedMarkedTreeCharge dataSet
coefficientCollarDichotomyPaysLinearCharge dataSet
  with coefficientCollarDichotomy dataSet
... | inj₁ markedPays =
  +-mono-≤ markedPays (residualTreeBelowOriginalTree dataSet)
... | inj₂ largePays =
  ≤ℝ-trans largePays (markedTermPlusTreeDominatesTree dataSet)

------------------------------------------------------------------------
-- Pareto/source accounting.
------------------------------------------------------------------------

-- CMP109 (3.5) plus the subsequent discussion supplies the source geometry:
-- either the localization pays a propagator/marked-distance factor, or reaching
-- outside the enlarged coefficient collar forces a large connected X whose
-- tree/localization weight pays.  The exact anchor/discrepancy map from that
-- source dichotomy to the CMP99 marked-walk coordinate remains to be inhabited.
coefficientCollarAnchorDiscrepancyGeometryLevel : ProofLevel
coefficientCollarAnchorDiscrepancyGeometryLevel = conditional

-- The ordered-real assembly above is generic and source-independent.
coefficientCollarLinearChargeCompilerLevel : ProofLevel
coefficientCollarLinearChargeCompilerLevel = machineChecked

-- R354 is stated at the majorant level.  Passing from a lower bound on the
-- positive exponent charge to an upper bound on exp(-charge), and identifying
-- those exponentials with R354's raw/charged majorants, is kept separate.
negativeExponentialChargeTransportLevel : ProofLevel
negativeExponentialChargeTransportLevel = standardImported

r355ChargeExponentToR354MajorantAttachmentLevel : ProofLevel
r355ChargeExponentToR354MajorantAttachmentLevel = conditional

cmp116OrdinarySummabilityCreatesCollarGeometry : Bool
cmp116OrdinarySummabilityCreatesCollarGeometry = false

cmp116OrdinarySummabilityCreatesCollarGeometryIsFalse :
  cmp116OrdinarySummabilityCreatesCollarGeometry ≡ false
cmp116OrdinarySummabilityCreatesCollarGeometryIsFalse = refl

sourceCitationCreatesAnchorDiscrepancyMap : Bool
sourceCitationCreatesAnchorDiscrepancyMap = false

sourceCitationCreatesAnchorDiscrepancyMapIsFalse :
  sourceCitationCreatesAnchorDiscrepancyMap ≡ false
sourceCitationCreatesAnchorDiscrepancyMapIsFalse = refl

freshGenericCauchyTheoremRequired : Bool
freshGenericCauchyTheoremRequired = false

freshGenericCauchyTheoremRequiredIsFalse :
  freshGenericCauchyTheoremRequired ≡ false
freshGenericCauchyTheoremRequiredIsFalse = refl

record Round355Boundary : Set where
  constructor round355-boundary
  field
    anchorDiscrepancyGeometryStillOpen : Bool
    anchorDiscrepancyGeometryStillOpenIsTrue :
      anchorDiscrepancyGeometryStillOpen ≡ true

    linearChargeAssemblyOwned : Bool
    linearChargeAssemblyOwnedIsTrue :
      linearChargeAssemblyOwned ≡ true

    exponentToR354MajorantAttachmentStillOpen : Bool
    exponentToR354MajorantAttachmentStillOpenIsTrue :
      exponentToR354MajorantAttachmentStillOpen ≡ true

    ordinaryCMP116SummabilityStillSeparate : Bool
    ordinaryCMP116SummabilityStillSeparateIsTrue :
      ordinaryCMP116SummabilityStillSeparate ≡ true

canonicalRound355Boundary : Round355Boundary
canonicalRound355Boundary =
  round355-boundary
    true refl
    true refl
    true refl
    true refl

round355FrontierRefinementLevel : ProofLevel
round355FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
