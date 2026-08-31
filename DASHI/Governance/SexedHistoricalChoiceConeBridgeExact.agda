module DASHI.Governance.SexedHistoricalChoiceConeBridgeExact where

------------------------------------------------------------------------
-- FORMAL RIGHT / EFFECTIVE CHOICE / SELF-CONCEIVED CHOICE
--
-- Cross-pollinates the transition-bearing sexed historical hyperfabric with
-- proof-bearing option cones, situated effective choice, history-conditioned
-- accessibility, and the existing dependent religious-entrapment candidate.
--
-- The central distinction is three-stage:
--
--   formal right != effectively reachable option != self-conceived option.
--
-- A route may be legally permitted yet materially inaccessible; it may also be
-- materially reachable while remaining absent from the subject's conceived
-- option set under retained history, authority, fear, belonging costs or
-- epistemic closure.  None of these finite witnesses is a population law.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.OptionConeCoercionExact as Cone
import DASHI.Governance.HistoryConditionedSocialEcologyOptionConeExact as HistoryCone
import DASHI.Governance.SituatedEffectiveChoiceExact as Effective
import DASHI.Governance.DependentReligiousEntrapmentCandidateExact as Entrapment
import DASHI.Governance.SexedHistoricalTransitionHyperfabricExact as Transition

------------------------------------------------------------------------
-- Three observers over one fine state.
------------------------------------------------------------------------

data FormalRightSurface : Set where
  formallyPermitted : FormalRightSurface

data EffectiveChoiceSurface : Set where
  effectivelyRestricted effectivelyAvailable : EffectiveChoiceSurface

data ConceivedChoiceSurface : Set where
  notConceived conceivedAsPossible : ConceivedChoiceSurface

data FineChoiceState : Set where
  formalButInaccessible
  formalReachableButUnconceived
  formalReachableAndConceived
  : FineChoiceState

formalRight : FineChoiceState → FormalRightSurface
formalRight _ = formallyPermitted

effectiveChoice : FineChoiceState → EffectiveChoiceSurface
effectiveChoice formalButInaccessible = effectivelyRestricted
effectiveChoice formalReachableButUnconceived = effectivelyAvailable
effectiveChoice formalReachableAndConceived = effectivelyAvailable

conceivedChoice : FineChoiceState → ConceivedChoiceSurface
conceivedChoice formalButInaccessible = notConceived
conceivedChoice formalReachableButUnconceived = notConceived
conceivedChoice formalReachableAndConceived = conceivedAsPossible

formalRightCannotRecoverEffectiveChoice :
  INF.FactorsThrough formalRight effectiveChoice → ⊥
formalRightCannotRecoverEffectiveChoice =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      formalButInaccessible
      formalReachableButUnconceived
      refl
      (λ ()))

effectiveChoiceCannotRecoverConceivedChoice :
  INF.FactorsThrough effectiveChoice conceivedChoice → ⊥
effectiveChoiceCannotRecoverConceivedChoice =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      formalReachableButUnconceived
      formalReachableAndConceived
      refl
      (λ ()))

formalRightCannotRecoverConceivedChoice :
  INF.FactorsThrough formalRight conceivedChoice → ⊥
formalRightCannotRecoverConceivedChoice =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      formalButInaccessible
      formalReachableAndConceived
      refl
      (λ ()))

------------------------------------------------------------------------
-- Proof-bearing effective option cone.
------------------------------------------------------------------------

data ChoiceState : Set where
  formallyFreeLowResources formallyFreeAdequateResources : ChoiceState

data ChoiceOption : Set where
  remainInInstitution exitInstitution independentHousing dissentPublicly : ChoiceOption

data Available : ChoiceState → ChoiceOption → Set where
  lowRemain : Available formallyFreeLowResources remainInInstitution
  lowDissent : Available formallyFreeLowResources dissentPublicly

  adequateRemain : Available formallyFreeAdequateResources remainInInstitution
  adequateExit : Available formallyFreeAdequateResources exitInstitution
  adequateHousing : Available formallyFreeAdequateResources independentHousing
  adequateDissent : Available formallyFreeAdequateResources dissentPublicly

choiceReachability : Cone.SafeReachabilitySystem ChoiceState ChoiceOption
choiceReachability = Cone.safeReachabilitySystem Available

lowIncludedInAdequate :
  (option : ChoiceOption) →
  Available formallyFreeLowResources option →
  Available formallyFreeAdequateResources option
lowIncludedInAdequate remainInInstitution lowRemain = adequateRemain
lowIncludedInAdequate dissentPublicly lowDissent = adequateDissent

formalFreedomCanCoexistWithContractedReachability :
  Cone.StrictSafeReachabilityContraction
    choiceReachability formallyFreeAdequateResources formallyFreeLowResources
formalFreedomCanCoexistWithContractedReachability =
  Cone.strictSafeReachabilityContraction
    lowIncludedInAdequate
    exitInstitution
    adequateExit
    (λ ())

------------------------------------------------------------------------
-- Existing owners remain the canonical provenance for the two conditioning
-- results: resources affect effective reachability, and retained history can
-- affect the option cone even at fixed ecology.
------------------------------------------------------------------------

situatedChoiceAlreadySeparatesFormalFromEffective : Bool
situatedChoiceAlreadySeparatesFormalFromEffective =
  Effective.SituatedEffectiveChoiceBoundary.unequalFeasibleChoiceFieldsCanExist
    Effective.canonicalSituatedEffectiveChoiceBoundary

historyCanContractChoiceAtFixedEcology =
  HistoryCone.historyConditionedContraction

------------------------------------------------------------------------
-- Religious-childhood cross-pollination.  The existing candidate requires
-- explicit low exit capacity, belonging penalty and restricted alternatives;
-- legal adulthood or formal freedom therefore cannot manufacture an exit
-- witness by label alone.
------------------------------------------------------------------------

data LegalAdulthoodImpliesZeroExitCost : Set where

data FormalReligiousFreedomImpliesEffectiveExit : Set where

data MaterialReachabilityImpliesPsychologicalAvailability : Set where

data ConceivedAlternativeImpliesSafePracticalExit : Set where

legalAdulthoodDoesNotImplyZeroExitCost :
  LegalAdulthoodImpliesZeroExitCost → ⊥
legalAdulthoodDoesNotImplyZeroExitCost ()

formalReligiousFreedomDoesNotImplyEffectiveExit :
  FormalReligiousFreedomImpliesEffectiveExit → ⊥
formalReligiousFreedomDoesNotImplyEffectiveExit ()

materialReachabilityDoesNotImplyPsychologicalAvailability :
  MaterialReachabilityImpliesPsychologicalAvailability → ⊥
materialReachabilityDoesNotImplyPsychologicalAvailability ()

conceivedAlternativeDoesNotImplySafePracticalExit :
  ConceivedAlternativeImpliesSafePracticalExit → ⊥
conceivedAlternativeDoesNotImplySafePracticalExit ()

entrapmentCandidateStillRequiresExplicitExitWitnesses : Bool
entrapmentCandidateStillRequiresExplicitExitWitnesses =
  Entrapment.EntrapmentResearchCoordinates.requiresExitRestriction
    Entrapment.canonicalEntrapmentResearchCoordinates

------------------------------------------------------------------------
-- Historical transition cross-pollination.
------------------------------------------------------------------------

suffrageTransitionRetainsMixedMaterialAxis :
  Transition.transitionStatus
    Transition.witchOrderToSuffrage
    Transition.materialIndependence
  ≡ Transition.mixed
suffrageTransitionRetainsMixedMaterialAxis = refl

suffrageTransitionCorrectsFormalRepresentation :
  Transition.transitionStatus
    Transition.witchOrderToSuffrage
    Transition.formalPoliticalRepresentation
  ≡ Transition.corrected
suffrageTransitionCorrectsFormalRepresentation = refl

record SexedHistoricalChoiceConeBoundary : Set where
  constructor sexed-historical-choice-cone-boundary
  field
    formalRightEqualsEffectiveChoice : Bool
    effectiveChoiceEqualsConceivedChoice : Bool
    legalAdulthoodZerosExitCost : Bool
    formalReligiousFreedomGuaranteesEffectiveExit : Bool
    materialReachabilityGuaranteesConceivedAvailability : Bool
    conceivedAvailabilityGuaranteesSafeExit : Bool
    retainedHistoryCanConditionChoice : Bool
    optionConeRequiresExplicitReachabilityWitness : Bool

canonicalSexedHistoricalChoiceConeBoundary : SexedHistoricalChoiceConeBoundary
canonicalSexedHistoricalChoiceConeBoundary =
  sexed-historical-choice-cone-boundary
    false false false false false false true true
