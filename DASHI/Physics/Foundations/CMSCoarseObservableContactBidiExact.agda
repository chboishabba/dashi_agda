{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMSCoarseObservableContactBidiExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Foundations.CoarseObservableFactorisationBidiExact as Coarse
import DASHI.Physics.Closure.HEPDataW3ComparisonLawReceipt as W3
import DASHI.Physics.Closure.HEPDataCMSBelowZDrellYanClaimExact as CMS
import DASHI.Physics.Closure.NSTriadKNStage3Ternary369Ledger as NS369
import DASHI.Physics.Closure.NSCriticalConeResidualFibre369CrossPollinationExact as NSResidual

------------------------------------------------------------------------
-- The CMS empirical contact and the 369/NS information-loss fixtures are
-- *distinct*, typed evidence owners. No numerical observation is turned
-- into a canonical-spine recovery theorem by importing these modules.
------------------------------------------------------------------------

boundedCMSW3Receipt :
  W3.W3ComparisonLawReceipt.w3Status
    W3.canonicalHEPDataW3ComparisonLawReceipt
  ≡ W3.promotedT43BelowZOnly
boundedCMSW3Receipt =
  W3.canonicalHEPDataW3ComparisonLawReceiptPromotesW3

cmsEarlyFullSpineNotProved :
  CMS.strongEarlyClaimAuthorityConstructed ≡ false
cmsEarlyFullSpineNotProved =
  CMS.strongEarlyClaimAuthorityConstructedIsFalse

cmsZeroFittedParametersNotProved :
  CMS.zeroFittedParametersProved ≡ false
cmsZeroFittedParametersNotProved =
  CMS.zeroFittedParametersProvedIsFalse

cmsFitNotKernelRecomputed :
  CMS.agdaKernelRecomputesFloatingPointCovarianceFit ≡ false
cmsFitNotKernelRecomputed =
  CMS.agdaKernelRecomputesFloatingPointCovarianceFitIsFalse

ns369EncodingRepresented :
  NS369.stage3Ternary369LayerRepresented ≡ true
ns369EncodingRepresented =
  NS369.stage3Ternary369LayerRepresentedIsTrue

nsSignedCovarianceUnpaid :
  NSResidual.NSResidualFibreBoundary.residualFibreAutomaticallyProvesSignedCovariance
    NSResidual.canonicalNSResidualFibreBoundary
  ≡ false
nsSignedCovarianceUnpaid = refl

-- The generic exact obstruction has an actual concrete inhabitant.
-- This refuses any universal consumer-retention claim for a coarse
-- projection that discards a signed fine coordinate.
noUniversalSignedRetention :
  (candidate : Coarse.OneCoarse → Coarse.FineSign) →
  ((x : Coarse.FineSign) →
    Coarse.observeSign x ≡ candidate (Coarse.projectSign x)) →
  ⊥
noUniversalSignedRetention = Coarse.noSignPredictionFromCoarse

-- A different, address-only consumer is exactly retained by that same
-- projection. Thus observational adequacy depends on the consumer.
addressConsumerRetained :
  (x : Coarse.FineSign) →
  Coarse.observeAddress x ≡
    (λ c → c) (Coarse.projectSign x)
addressConsumerRetained = Coarse.addressFactors

------------------------------------------------------------------------
-- Physical frontier, deliberately not inhabited here:
--
-- (1) selected hypervoxel/hyperfabric projection and native transport;
-- (2) selected CMP119 quantum measure -> conserved renormalised stress;
-- (3) same stress as GRQFT selected physical gravitational source;
-- (4) actual continuum metric variation and FLRW backreaction;
-- (5) frozen predictor with stated parameters and fully identified
--     observable/covariance/units/revision;
-- (6) a proof of observable factorisation or a concrete physical collision.
--
-- The CMS record is evidence of a frozen comparison, not proof of (1)-(6).
------------------------------------------------------------------------
