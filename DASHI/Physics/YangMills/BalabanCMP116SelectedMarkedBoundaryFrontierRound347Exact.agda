{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedBoundaryFrontierRound347Exact where

------------------------------------------------------------------------
-- ROUND347 / PARETO FRONTIER BELOW R346 L_marked
--
-- R346 reduced T78-B to two physical/source fields:
--
--   L_marked : selected literal two-J mixed-log magnitude
--              <= actual shared CMP116 hessian marked analytic shell
--
--   D_time   : selected R318 physical support distance = Euclidean time.
--
-- The source audit below L_marked shows that the generic analytic step is
-- already owned in-repo.  `BalabanDecoupledActivityHessian` proves:
--
--   pointwise marked boundary comparison
--       -> finite-polydisc Cauchy coefficient/Hessian bound,
--
-- and also the shorter substituted-background route:
--
--   substituted-background stability
--       -> marked boundary comparison
--       -> Cauchy coefficient/Hessian bound.
--
-- CMP116 differentiated-localization authority is likewise already recorded.
-- Therefore the surviving YM content is not another Cauchy theorem.  It is the
-- source-specific application on the SAME selected R318 J(F),J(G) carrier:
--
--   (1) selected CMP116 marked boundary/substitution comparison;
--   (2) selected-J physical-coordinate attachment identifying the resulting
--       source coefficient with R318's literal two-J response.
--
-- D_time remains independent and proof-bearing.
--
-- Important Pareto firewalls:
--
-- * do not reintroduce R343 sourceEnvelope -> clusteringEnvelope calibration;
-- * do not require rootedShell <= markedAnalyticShell (wrong direction);
-- * do not require equality with the older hessianInfluenceShell;
-- * do not reintroduce C_H <= 1.
--
-- This module records the dependency frontier only.  It does not manufacture
-- either physical/source payment and it does not claim a Clay mass gap.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source

------------------------------------------------------------------------
-- Already-owned generic/source authority.
------------------------------------------------------------------------

genericBoundaryToCauchyLiftLevel : ProofLevel
genericBoundaryToCauchyLiftLevel = Source.markedBoundaryToHessianCauchyLiftLevel

cmp116DifferentiatedLocalizationAuthorityLevel : ProofLevel
cmp116DifferentiatedLocalizationAuthorityLevel =
  Source.cmp116DifferentiatedLocalizationAuthorityLevel

------------------------------------------------------------------------
-- Surviving physical/source payments.
------------------------------------------------------------------------

-- Literal selected CMP116 boundary/substitution comparison on the shared
-- Hessian-marked analytic shell.  This includes the actual substituted-background
-- comparison and selected source-domain/radius applicability needed by the
-- generic Cauchy lift; bibliographic source authority does not inhabit it.
selectedMarkedBoundarySubstitutionLevel : ProofLevel
selectedMarkedBoundarySubstitutionLevel = conditional

-- Same-object attachment from the source/Cauchy coefficient produced above to
-- R318's literal selected J(F),J(G) mixed-log response.  No equality with an
-- older Pi or hessianInfluenceShell carrier is assumed.
selectedJPhysicalCoordinateAttachmentLevel : ProofLevel
selectedJPhysicalCoordinateAttachmentLevel = conditional

-- R346's second independent leaf: the exact selected support distance used by
-- the R300 decomposition is Euclidean spectral time.
selectedDistanceTimeLevel : ProofLevel
selectedDistanceTimeLevel = conditional

------------------------------------------------------------------------
-- Explicitly pruned stronger routes.
------------------------------------------------------------------------

rootedShellReverseComparisonRequired : Bool
rootedShellReverseComparisonRequired = false

rootedShellReverseComparisonRequiredIsFalse :
  rootedShellReverseComparisonRequired ≡ false
rootedShellReverseComparisonRequiredIsFalse = refl

hessianInfluenceShellEqualityRequired : Bool
hessianInfluenceShellEqualityRequired = false

hessianInfluenceShellEqualityRequiredIsFalse :
  hessianInfluenceShellEqualityRequired ≡ false
hessianInfluenceShellEqualityRequiredIsFalse = refl

r343SourceEnvelopeCalibrationStillPrimitive : Bool
r343SourceEnvelopeCalibrationStillPrimitive = false

r343SourceEnvelopeCalibrationStillPrimitiveIsFalse :
  r343SourceEnvelopeCalibrationStillPrimitive ≡ false
r343SourceEnvelopeCalibrationStillPrimitiveIsFalse = refl

hessianConstantAtMostOneRequired : Bool
hessianConstantAtMostOneRequired = false

hessianConstantAtMostOneRequiredIsFalse :
  hessianConstantAtMostOneRequired ≡ false
hessianConstantAtMostOneRequiredIsFalse = refl

------------------------------------------------------------------------
-- Canonical frontier receipt.
------------------------------------------------------------------------

record Round347Boundary : Set where
  constructor round347-boundary
  field
    genericCauchyExtractionOwned : Bool
    genericCauchyExtractionOwnedIsTrue : genericCauchyExtractionOwned ≡ true

    selectedBoundarySubstitutionStillPhysical : Bool
    selectedBoundarySubstitutionStillPhysicalIsTrue :
      selectedBoundarySubstitutionStillPhysical ≡ true

    selectedJAttachmentStillPhysical : Bool
    selectedJAttachmentStillPhysicalIsTrue :
      selectedJAttachmentStillPhysical ≡ true

    selectedDistanceTimeStillPhysical : Bool
    selectedDistanceTimeStillPhysicalIsTrue :
      selectedDistanceTimeStillPhysical ≡ true

    oldR343CalibrationPruned : Bool
    oldR343CalibrationPrunedIsTrue : oldR343CalibrationPruned ≡ true

canonicalRound347Boundary : Round347Boundary
canonicalRound347Boundary =
  round347-boundary
    true refl
    true refl
    true refl
    true refl
    true refl

round347FrontierCompilerLevel : ProofLevel
round347FrontierCompilerLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
