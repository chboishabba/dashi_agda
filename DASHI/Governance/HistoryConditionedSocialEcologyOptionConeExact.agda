module DASHI.Governance.HistoryConditionedSocialEcologyOptionConeExact where

------------------------------------------------------------------------
-- HISTORY-CONDITIONED SOCIAL-ECOLOGICAL OPTION CONE
--
-- SOURCE / INTERNAL PROVENANCE
--
-- Urie Bronfenbrenner, The Ecology of Human Development, Harvard University
-- Press, 1979. ISBN 9780674224575.  Source context only for nested
-- person-environment ecology; the finite option-cone theorem is DASHI's.
--
-- Internal theorem-pattern provenance:
--   draft PR #606: retained history/body context can change the accessible
--                  subfabric while world structure is held fixed;
--   draft PR #618: the same person can have different realized affordance cones
--                  under different social ecologies;
--   existing OptionConeCoercionExact: proof-bearing option availability and
--                  strict safe-reachability contraction.
--
-- This module does not import #606 or #618 and therefore creates no cyclic
-- draft ancestry.  It extracts only their common finite theorem shape.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Governance.OptionConeCoercionExact as Cone

------------------------------------------------------------------------
-- Two independent conditioning coordinates.
------------------------------------------------------------------------

data HistoryContext : Set where
  regulatedHistory mobilisedHistory : HistoryContext

data EcologyContext : Set where
  supportiveEcology hostileEcology : EcologyContext

record SituatedState : Set where
  constructor situated-state
  field
    history : HistoryContext
    ecology : EcologyContext

open SituatedState public

regulatedSupportive : SituatedState
regulatedSupportive = situated-state regulatedHistory supportiveEcology

mobilisedSupportive : SituatedState
mobilisedSupportive = situated-state mobilisedHistory supportiveEcology

regulatedHostile : SituatedState
regulatedHostile = situated-state regulatedHistory hostileEcology

mobilisedHostile : SituatedState
mobilisedHostile = situated-state mobilisedHistory hostileEcology

sameSupportiveEcology :
  ecology regulatedSupportive ≡ ecology mobilisedSupportive
sameSupportiveEcology = refl

sameRegulatedHistory :
  history regulatedSupportive ≡ history regulatedHostile
sameRegulatedHistory = refl

------------------------------------------------------------------------
-- Realized safe options.
------------------------------------------------------------------------

data SocialOption : Set where
  remain recover optionalInteraction exit returnLater : SocialOption

data Available : SituatedState → SocialOption → Set where
  rsRemain : Available regulatedSupportive remain
  rsRecover : Available regulatedSupportive recover
  rsInteract : Available regulatedSupportive optionalInteraction
  rsExit : Available regulatedSupportive exit
  rsReturn : Available regulatedSupportive returnLater

  msRemain : Available mobilisedSupportive remain
  msExit : Available mobilisedSupportive exit
  msReturn : Available mobilisedSupportive returnLater

  rhRemain : Available regulatedHostile remain
  rhExit : Available regulatedHostile exit

  mhExit : Available mobilisedHostile exit

socialReachability : Cone.SafeReachabilitySystem SituatedState SocialOption
socialReachability = Cone.safeReachabilitySystem Available

------------------------------------------------------------------------
-- History alone can contract accessibility at fixed ecology.
------------------------------------------------------------------------

mobilisedIncludedInRegulatedSupportive :
  (option : SocialOption) →
  Available mobilisedSupportive option →
  Available regulatedSupportive option
mobilisedIncludedInRegulatedSupportive remain msRemain = rsRemain
mobilisedIncludedInRegulatedSupportive exit msExit = rsExit
mobilisedIncludedInRegulatedSupportive returnLater msReturn = rsReturn

historyConditionedContraction :
  Cone.StrictSafeReachabilityContraction
    socialReachability regulatedSupportive mobilisedSupportive
historyConditionedContraction =
  Cone.strictSafeReachabilityContraction
    mobilisedIncludedInRegulatedSupportive
    recover
    rsRecover
    (λ ())

------------------------------------------------------------------------
-- Ecology alone can contract accessibility at fixed retained history.
------------------------------------------------------------------------

hostileIncludedInSupportiveRegulated :
  (option : SocialOption) →
  Available regulatedHostile option →
  Available regulatedSupportive option
hostileIncludedInSupportiveRegulated remain rhRemain = rsRemain
hostileIncludedInSupportiveRegulated exit rhExit = rsExit

ecologyConditionedContraction :
  Cone.StrictSafeReachabilityContraction
    socialReachability regulatedSupportive regulatedHostile
ecologyConditionedContraction =
  Cone.strictSafeReachabilityContraction
    hostileIncludedInSupportiveRegulated
    recover
    rsRecover
    (λ ())

------------------------------------------------------------------------
-- Joint history + ecology is stronger still in the canonical finite specimen.
------------------------------------------------------------------------

mobilisedHostileIncludedInRegulatedSupportive :
  (option : SocialOption) →
  Available mobilisedHostile option →
  Available regulatedSupportive option
mobilisedHostileIncludedInRegulatedSupportive exit mhExit = rsExit

jointHistoryEcologyContraction :
  Cone.StrictSafeReachabilityContraction
    socialReachability regulatedSupportive mobilisedHostile
jointHistoryEcologyContraction =
  Cone.strictSafeReachabilityContraction
    mobilisedHostileIncludedInRegulatedSupportive
    returnLater
    rsReturn
    (λ ())

record HistoryEcologyOptionConeBoundary : Set where
  constructor history-ecology-option-cone-boundary
  field
    sameEcologyImpliesSameAccessibleCone : Bool
    sameEcologyImpliesSameAccessibleConeIsFalse :
      sameEcologyImpliesSameAccessibleCone ≡ false
    sameHistoryImpliesSameAccessibleCone : Bool
    sameHistoryImpliesSameAccessibleConeIsFalse :
      sameHistoryImpliesSameAccessibleCone ≡ false
    contractedAccessibilityDeletesWorldPossibility : Bool
    contractedAccessibilityDeletesWorldPossibilityIsFalse :
      contractedAccessibilityDeletesWorldPossibility ≡ false
    optionConeContractionAloneProvesCoercion : Bool
    optionConeContractionAloneProvesCoercionIsFalse :
      optionConeContractionAloneProvesCoercion ≡ false
    finiteWitnessIsClinicalOrPoliticalPopulationLaw : Bool
    finiteWitnessIsClinicalOrPoliticalPopulationLawIsFalse :
      finiteWitnessIsClinicalOrPoliticalPopulationLaw ≡ false

canonicalHistoryEcologyOptionConeBoundary : HistoryEcologyOptionConeBoundary
canonicalHistoryEcologyOptionConeBoundary =
  history-ecology-option-cone-boundary
    false refl false refl false refl false refl false refl
