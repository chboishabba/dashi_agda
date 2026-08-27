module DASHI.Core.SituatedFormalisationBoundaryExact where

------------------------------------------------------------------------
-- SITUATED FORMALISATION BOUNDARY
--
-- SOURCE CALIBRATION
-- Donna Haraway, "Situated Knowledges: The Science Question in Feminism and
-- the Privilege of Partial Perspective", Feminist Studies 14(3), 575-599
-- (1988). DOI/JSTOR stable 10.2307/3178066.
--
-- Haraway motivates rejection of a disembodied "view from nowhere". DASHI
-- therefore distinguishes domain-uncommitted formal carriers from claims of
-- epistemically positionless representation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record SituatedFormalisationBoundary : Set where
  constructor situated-formalisation-boundary
  field
    formalCarrierIsDomainUncommitted : Bool
    formalCarrierIsDomainUncommittedIsTrue :
      formalCarrierIsDomainUncommitted ≡ true
    formalCarrierIsEpistemicallyPositionless : Bool
    formalCarrierIsEpistemicallyPositionlessIsFalse :
      formalCarrierIsEpistemicallyPositionless ≡ false
    abstractionChoiceHasNoProvenance : Bool
    abstractionChoiceHasNoProvenanceIsFalse : abstractionChoiceHasNoProvenance ≡ false
    domainNeutralityImpliesViewFromNowhere : Bool
    domainNeutralityImpliesViewFromNowhereIsFalse :
      domainNeutralityImpliesViewFromNowhere ≡ false

canonicalSituatedFormalisationBoundary : SituatedFormalisationBoundary
canonicalSituatedFormalisationBoundary =
  situated-formalisation-boundary true refl false refl false refl false refl
