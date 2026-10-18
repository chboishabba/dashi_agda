module DASHI.Analysis.FastCauchyLegacyQuotientBackendWeldExact where

------------------------------------------------------------------------
-- OLD FAST-CAUCHY QUOTIENT REALIZATION -> NEW BACKEND QUOTIENT SEAM
--
-- DASHI CONTRIBUTION
--
-- The repository has two compatible quotient-facing interfaces:
--
--   * FastCauchyReals.FastCauchyQuotientRealization
--   * ConstructedRealBackendSpineExact.PropositionalQuotientRealization
--
-- The former predates the newer setoid-aware backend spine.  This module
-- removes that representation mismatch.  Given any existing Fast-Cauchy
-- quotient realization and the already-defined direct Fast-Cauchy backend
-- packaging, all quotient arithmetic, order and completeness data are reused
-- definition-for-definition.
--
-- This does NOT construct the missing SetQuotientBackend or quotient
-- completeness witness.  It only proves that once the old realization is
-- inhabited, no second quotient theorem is required by the new spine.
------------------------------------------------------------------------

import DASHI.Analysis.FastCauchyReals as Fast
import DASHI.Analysis.FastCauchyConstructedRealBackendExact as Backend
import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine

fastCauchyLegacyQuotientWeld :
  ∀ {A : Fast.RationalMetricAuthority}
    {O : Fast.FastCauchyOperations A} →
  (packaging : Backend.FastCauchyBackendPackaging A O) →
  (Q : Fast.FastCauchyQuotientRealization A O) →
  Spine.PropositionalQuotientRealization
    (Backend.fastCauchySetoidOrderedCompleteReal O packaging)
fastCauchyLegacyQuotientWeld packaging Q = record
  { Spine.Quotient = Fast.Real Q
  ; Spine.quotient = Fast.quotient Q
  ; Spine.quotientSound = Fast.quotientSound Q
  ; Spine.quotientComplete = Fast.quotientComplete Q

  ; Spine.zeroQ = Fast.zero Q
  ; Spine.oneQ = Fast.one Q
  ; Spine.addQ = Fast.add Q
  ; Spine.subQ = Fast.sub Q
  ; Spine.mulQ = Fast.mul Q
  ; Spine.negQ = Fast.neg Q
  ; Spine.absQ = Fast.abs Q
  ; Spine.leQ = Fast.le Q
  ; Spine.ltQ = Fast.lt Q

  ; Spine.operationsAgree = Fast.operationsAgree Q
  ; Spine.orderedFieldLawsQ = Fast.orderedFieldLaws Q

  ; Spine.SequenceQ = Fast.Sequence Q
  ; Spine.sequenceAtQ = Fast.sequenceAt Q
  ; Spine.IsCauchyQ = Fast.IsCauchy Q
  ; Spine.ConvergesToQ = Fast.ConvergesTo Q
  ; Spine.cauchyLimitQ = Fast.cauchyLimit Q

  ; Spine.addAssocQ = Fast.addAssoc Q
  ; Spine.addCommQ = Fast.addComm Q
  ; Spine.addZeroLeftQ = Fast.addZeroLeft Q
  ; Spine.addZeroRightQ = Fast.addZeroRight Q
  ; Spine.mulAssocQ = Fast.mulAssoc Q
  ; Spine.mulCommQ = Fast.mulComm Q
  ; Spine.mulOneLeftQ = Fast.mulOneLeft Q
  ; Spine.mulOneRightQ = Fast.mulOneRight Q
  ; Spine.distribLeftQ = Fast.distribLeft Q
  ; Spine.distribRightQ = Fast.distribRight Q
  ; Spine.subSelfQ = Fast.subSelf Q
  }
