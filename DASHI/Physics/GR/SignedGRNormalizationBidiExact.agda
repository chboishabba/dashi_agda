module DASHI.Physics.GR.SignedGRNormalizationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as Signed
import DASHI.Promotion.ClassicalFieldObligations as Promotion

------------------------------------------------------------------------
-- SAME GR CONSTANT SLOT, DIFFERENT SIGN BRANCH
--
-- The existing promotion owner names the gravitational constant slot and keeps
-- the measured value unpromoted.  This module does not overwrite that registry.
-- It adds a counterfactual sign coordinate consumed by theory-comparison work.
------------------------------------------------------------------------

data GNormalizationBranch : Set where
  physicalPositiveGBranch : GNormalizationBranch
  counterfactualNegativeGBranch : GNormalizationBranch

branchSign : GNormalizationBranch → Signed.CouplingSign
branchSign physicalPositiveGBranch = Signed.positiveCoupling
branchSign counterfactualNegativeGBranch = Signed.negativeCoupling

constantSlotName : GNormalizationBranch → String
constantSlotName branch =
  Promotion.gravitationalConstantSlot
    Promotion.canonicalGRNormalizationObligation

constantSlotCollision :
  constantSlotName physicalPositiveGBranch
    ≡ constantSlotName counterfactualNegativeGBranch
constantSlotCollision = refl

branchSignsDistinct :
  branchSign physicalPositiveGBranch
    ≡ branchSign counterfactualNegativeGBranch → ⊥
branchSignsDistinct ()

record SignedGRNormalizationProbe : Set₁ where
  constructor signed-gr-normalization-probe
  field
    baseNormalization : Promotion.GRNormalizationObligation
    signBranch : GNormalizationBranch
    couplingSign : Signed.CouplingSign
    couplingSignMatchesBranch : couplingSign ≡ branchSign signBranch
    measuredRegistryValueOverridden : Bool

open SignedGRNormalizationProbe public

canonicalNegativeGNormalizationProbe : SignedGRNormalizationProbe
canonicalNegativeGNormalizationProbe = signed-gr-normalization-probe
  Promotion.canonicalGRNormalizationObligation
  counterfactualNegativeGBranch
  Signed.negativeCoupling
  refl
  false

canonicalPhysicalGValueStillNotPromotedByNormalizationSurface :
  Promotion.measuredGValuePromoted Promotion.canonicalGRNormalizationObligation
    ≡ false
canonicalPhysicalGValueStillNotPromotedByNormalizationSurface = refl

record SignedGRNormalizationBoundary : Set where
  constructor signed-gr-normalization-boundary
  field
    constantSlotNameDeterminesCouplingSign : Bool
    negativeGCounterfactualMayReuseExistingNormalizationShape : Bool
    negativeGCounterfactualOverwritesMeasuredRegistryValue : Bool
    negativeGCounterfactualEqualsMeasuredNegativeG : Bool
    signBranchMustRemainExplicit : Bool
    counterfactualNormalizationAutomaticallyPromotesGR : Bool

canonicalSignedGRNormalizationBoundary : SignedGRNormalizationBoundary
canonicalSignedGRNormalizationBoundary =
  signed-gr-normalization-boundary false true false false true false
