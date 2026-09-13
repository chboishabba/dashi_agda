module DASHI.Physics.ExoticGravity.LiTorr1991CombinedFieldSourceEntitlementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Physics.ExoticGravity.LiTorrCoupledPotentialModelExact as LiTorr

------------------------------------------------------------------------
-- 1991 PRIMARY-ABSTRACT SOURCE ENTITLEMENT
--
-- Canonical APS bibliographic carrier:
--   N. Li; D. G. Torr
--   Effects of a gravitomagnetic field on pure superconductors
--   Phys. Rev. D 43, 457-459 (1991)
--   DOI 10.1103/PhysRevD.43.457
--
-- The publisher abstract source-entitles the bounded historical claim that the
-- combined magnetic/gravitomagnetic coordinate B + (m/q) B_g attenuates
-- exponentially over a characteristic penetration length.  Abstract inspection
-- is not full-paper inspection and does not validate the proposed physics.
------------------------------------------------------------------------

liTorr1991PrimaryAbstractSource : Source.AttributedSource
liTorr1991PrimaryAbstractSource = Source.mkDOISource
  "N. Li; D. G. Torr"
  "Effects of a gravitomagnetic field on pure superconductors"
  "Physical Review D 43, 457-459"
  "1991"
  "10.1103/PhysRevD.43.457"
  "https://journals.aps.org/prd/abstract/10.1103/PhysRevD.43.457"
  Source.academicArticleSource
  "primary APS abstract source-entitled only for the bounded historical combined-field attenuation claim encoded below; not full-text inspection and not physical validation"
  Source.publicAttribution

record PrimaryAbstractInspectionReceipt : Set where
  constructor primary-abstract-inspection-receipt
  field
    attributedSource : Source.AttributedSource
    sourceMatchesCanonical : attributedSource ≡ liTorr1991PrimaryAbstractSource
    carrierKind : String
    inspectedOn : String
    exactLocator : String
    boundedSourceEntitledUse : String

open PrimaryAbstractInspectionReceipt public

liTorr1991PrimaryAbstractInspection : PrimaryAbstractInspectionReceipt
liTorr1991PrimaryAbstractInspection = primary-abstract-inspection-receipt
  liTorr1991PrimaryAbstractSource
  refl
  "APS canonical publisher abstract"
  "2026-09-09"
  "Abstract"
  "historical claim that the combined B + (m/q) B_g field coordinate decays exponentially in the superconductor with a characteristic penetration length"

------------------------------------------------------------------------
-- Exact weld to the existing historical-claim owner.
------------------------------------------------------------------------

record CombinedFieldAttenuationSourceWeld : Set where
  constructor combined-field-attenuation-source-weld
  field
    sourceInspection : PrimaryAbstractInspectionReceipt
    sourceInspectionMatches :
      sourceInspection ≡ liTorr1991PrimaryAbstractInspection
    attenuationConsumer : LiTorr.CombinedFieldAttenuationClaim
    attenuationConsumerMatches :
      attenuationConsumer ≡ LiTorr.canonicalCombinedFieldAttenuationClaim

open CombinedFieldAttenuationSourceWeld public

canonicalCombinedFieldAttenuationSourceWeld : CombinedFieldAttenuationSourceWeld
canonicalCombinedFieldAttenuationSourceWeld =
  combined-field-attenuation-source-weld
    liTorr1991PrimaryAbstractInspection
    refl
    LiTorr.canonicalCombinedFieldAttenuationClaim
    refl

------------------------------------------------------------------------
-- Promotion / custody firewall.
------------------------------------------------------------------------

record LiTorr1991SourceEntitlementBoundary : Set where
  constructor li-torr-1991-source-entitlement-boundary
  field
    primaryPublisherAbstractInspected : Bool
    abstractInspectionEqualsFullArticleInspection : Bool
    historicalClaimShapeIsSourceEntitled : Bool
    sourceEntitlementProvesCombinedFieldLawCorrect : Bool
    sourceEntitlementProvesSuperconductingEnhancement : Bool
    sourceEntitlementProvesMaterialEffectiveNegativeG : Bool
    sourceEntitlementBecomesAmyStatement : Bool

canonicalLiTorr1991SourceEntitlementBoundary : LiTorr1991SourceEntitlementBoundary
canonicalLiTorr1991SourceEntitlementBoundary =
  li-torr-1991-source-entitlement-boundary
    true false true false false false false
