module DASHI.Moonshine.P11Fine5PNFProvenanceQuotientBridgeExact where

------------------------------------------------------------------------
-- The p=11 marked/coarse quotient as a canonical DASHI provenance-bearing
-- quotient.  The coarse j-class alone does not recover the marked point; a
-- three-valued residual sheet coordinate suffices exactly.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.SectionedProjectionProvenanceBridgeExact as Sectioned
import DASHI.Core.ProvenanceBearingQuotient as Quotient

import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo

fine5SectionedProjection :
  Sectioned.SectionedProjection Fine.P11Fine5 Geo.P11SupersingularJ
fine5SectionedProjection =
  Sectioned.sectionedProjection
    Fine.projectFine5
    Fine.representFine5
    Fine.projectRepresentFine5

------------------------------------------------------------------------
-- One residual radix handles both fibres:
--   j=0    uses r0,r1 for a0,a1;
--   j=1728 uses r0,r1,r2 for b0,b1,b2.
-- The (j=0,r2) pair is deliberately unused.
------------------------------------------------------------------------

data Fine5Residual : Set where
  r0 r1 r2 : Fine5Residual

fine5Residual : Fine.P11Fine5 → Fine5Residual
fine5Residual Fine.a0 = r0
fine5Residual Fine.a1 = r1
fine5Residual Fine.b0 = r0
fine5Residual Fine.b1 = r1
fine5Residual Fine.b2 = r2

reopenFine5 : Geo.P11SupersingularJ → Fine5Residual → Fine.P11Fine5
reopenFine5 Geo.jZeroSS r0 = Fine.a0
reopenFine5 Geo.jZeroSS r1 = Fine.a1
reopenFine5 Geo.jZeroSS r2 = Fine.a0
reopenFine5 Geo.j1728SS r0 = Fine.b0
reopenFine5 Geo.j1728SS r1 = Fine.b1
reopenFine5 Geo.j1728SS r2 = Fine.b2

reopenFine5Exact :
  (x : Fine.P11Fine5) →
  reopenFine5 (Fine.projectFine5 x) (fine5Residual x) ≡ x
reopenFine5Exact Fine.a0 = refl
reopenFine5Exact Fine.a1 = refl
reopenFine5Exact Fine.b0 = refl
reopenFine5Exact Fine.b1 = refl
reopenFine5Exact Fine.b2 = refl

fine5ResidualReopening :
  Sectioned.ResidualReopening fine5SectionedProjection
fine5ResidualReopening =
  Sectioned.residualReopening
    Fine5Residual
    fine5Residual
    reopenFine5
    reopenFine5Exact

fine5PNFProvenanceQuotient :
  Quotient.ProvenanceBearingQuotient
    (Sectioned.sectionedProjectionCore fine5SectionedProjection)
fine5PNFProvenanceQuotient =
  Sectioned.residualReopeningGivesProvenanceBearingQuotient
    fine5ResidualReopening

------------------------------------------------------------------------
-- Exact coarse+residual reopening examples.
------------------------------------------------------------------------

a1ReopensFromCoarseAndResidual :
  reopenFine5 Geo.jZeroSS r1 ≡ Fine.a1
a1ReopensFromCoarseAndResidual = refl

b2ReopensFromCoarseAndResidual :
  reopenFine5 Geo.j1728SS r2 ≡ Fine.b2
b2ReopensFromCoarseAndResidual = refl

record P11Fine5PNFQuotientBoundary : Set where
  constructor p11Fine5PNFQuotientBoundary
  field
    coarseJProjectionSectioned : Bool
    coarseJProjectionSectionedIsTrue : coarseJProjectionSectioned ≡ true
    residualSheetCoordinateConstructed : Bool
    residualSheetCoordinateConstructedIsTrue :
      residualSheetCoordinateConstructed ≡ true
    coarsePlusResidualReopensMarkedStateExactly : Bool
    coarsePlusResidualReopensMarkedStateExactlyIsTrue :
      coarsePlusResidualReopensMarkedStateExactly ≡ true
    sectionAlonePromotedToFineStateIdentity : Bool
    sectionAlonePromotedToFineStateIdentityIsFalse :
      sectionAlonePromotedToFineStateIdentity ≡ false

canonicalP11Fine5PNFQuotientBoundary : P11Fine5PNFQuotientBoundary
canonicalP11Fine5PNFQuotientBoundary =
  p11Fine5PNFQuotientBoundary true refl true refl true refl false refl
