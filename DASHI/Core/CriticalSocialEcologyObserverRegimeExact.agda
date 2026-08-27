module DASHI.Core.CriticalSocialEcologyObserverRegimeExact where

------------------------------------------------------------------------
-- CRITICAL SOCIAL-ECOLOGY OBSERVER REGIMES
--
-- SOURCE CONTEXT / CALIBRATION
--
-- Murray Bookchin, The Ecology of Freedom, original 1982; AK Press 2005,
-- ISBN 9781904859260.
-- Ynestra King, "Healing the Wounds", in Gender/Body/Knowledge, 1989,
-- ISBN 9780813513799.
-- Gloria Anzaldua, Borderlands / La Frontera, 1987,
-- ISBN 9781879960138.
-- Kimberle Crenshaw, "Mapping the Margins", 1991,
-- DOI 10.2307/1229039.
--
-- The finite labels below are synthetic DASHI observer regimes.  No source is
-- asserted to use these exact labels or transition tables.
--
-- CENTRAL DISTINCTIONS
--
--   realized affordance != observer approval
--   liberatory rhetoric  != realized accessibility
--   dominant disapproval != actual dysfunction
--   same nominal space   != same situated option cone
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- Fine ecology state separates material accessibility from social reading.
------------------------------------------------------------------------

data EcologyState : Set where
  dominantClosed
  thirdOpen
  rhetoricallyInclusiveClosed
  : EcologyState

data RealizedRemainAffordance : Set where
  remainClosed remainOpen : RealizedRemainAffordance

data DominantObserverReading : Set where
  orderlyReading ambiguousReading disorderReading : DominantObserverReading

data FeministObserverReading : Set where
  restrictiveReading inclusiveReading : FeministObserverReading

data NominalLiberatoryLabel : Set where
  liberatoryLabel : NominalLiberatoryLabel

realizedRemain : EcologyState → RealizedRemainAffordance
realizedRemain dominantClosed = remainClosed
realizedRemain thirdOpen = remainOpen
realizedRemain rhetoricallyInclusiveClosed = remainClosed

dominantObserver : EcologyState → DominantObserverReading
dominantObserver dominantClosed = orderlyReading
dominantObserver thirdOpen = disorderReading
dominantObserver rhetoricallyInclusiveClosed = ambiguousReading

feministObserver : EcologyState → FeministObserverReading
feministObserver dominantClosed = restrictiveReading
feministObserver thirdOpen = inclusiveReading
feministObserver rhetoricallyInclusiveClosed = inclusiveReading

nominalLiberatoryObserver : EcologyState → NominalLiberatoryLabel
nominalLiberatoryObserver _ = liberatoryLabel

------------------------------------------------------------------------
-- Open affordance can coexist with dominant disapproval.
------------------------------------------------------------------------

thirdSpaceIsOpen : realizedRemain thirdOpen ≡ remainOpen
thirdSpaceIsOpen = refl

thirdSpaceCanBeReadAsDisorder : dominantObserver thirdOpen ≡ disorderReading
thirdSpaceCanBeReadAsDisorder = refl

------------------------------------------------------------------------
-- Positive rhetoric does not determine material accessibility.
------------------------------------------------------------------------

inclusiveReadingsCollide :
  feministObserver thirdOpen ≡ feministObserver rhetoricallyInclusiveClosed
inclusiveReadingsCollide = refl

realizedRemainDiffersUnderSameInclusiveReading :
  realizedRemain thirdOpen ≡ realizedRemain rhetoricallyInclusiveClosed → ⊥
realizedRemainDiffersUnderSameInclusiveReading ()

inclusiveReadingCannotRecoverRealizedAffordance :
  INF.FactorsThrough feministObserver realizedRemain → ⊥
inclusiveReadingCannotRecoverRealizedAffordance =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      thirdOpen
      rhetoricallyInclusiveClosed
      inclusiveReadingsCollide
      realizedRemainDiffersUnderSameInclusiveReading)

nominalLiberatoryLabelCannotRecoverRealizedAffordance :
  INF.FactorsThrough nominalLiberatoryObserver realizedRemain → ⊥
nominalLiberatoryLabelCannotRecoverRealizedAffordance =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      thirdOpen
      rhetoricallyInclusiveClosed
      refl
      realizedRemainDiffersUnderSameInclusiveReading)

------------------------------------------------------------------------
-- Observer disagreement is a property of observer regimes, not proof that one
-- observer is automatically authoritative for all consumers.
------------------------------------------------------------------------

record ObserverRegimeBoundary : Set where
  constructor observer-regime-boundary
  field
    dominantDisapprovalProvesDysfunction : Bool
    dominantDisapprovalProvesDysfunctionIsFalse :
      dominantDisapprovalProvesDysfunction ≡ false
    feministApprovalProvesAccessibility : Bool
    feministApprovalProvesAccessibilityIsFalse :
      feministApprovalProvesAccessibility ≡ false
    thirdSpaceLabelGuaranteesOpenOptionCone : Bool
    thirdSpaceLabelGuaranteesOpenOptionConeIsFalse :
      thirdSpaceLabelGuaranteesOpenOptionCone ≡ false
    observerDisagreementSelectsUniversalAuthority : Bool
    observerDisagreementSelectsUniversalAuthorityIsFalse :
      observerDisagreementSelectsUniversalAuthority ≡ false
    finiteWitnessIsEmpiricalPoliticalClassification : Bool
    finiteWitnessIsEmpiricalPoliticalClassificationIsFalse :
      finiteWitnessIsEmpiricalPoliticalClassification ≡ false

canonicalObserverRegimeBoundary : ObserverRegimeBoundary
canonicalObserverRegimeBoundary =
  observer-regime-boundary false refl false refl false refl false refl false refl
