module DASHI.Core.DifferenceWithoutHierarchyExact where

------------------------------------------------------------------------
-- DIFFERENCE WITHOUT HIERARCHY / ESSENCE
--
-- SOURCE / CONCEPTUAL CONTEXT
--
-- Joan W. Scott,
-- "Deconstructing Equality-versus-Difference: Or, the Uses of
-- Poststructuralist Theory for Feminism", Feminist Studies 14(1) (1988),
-- 32--50. DOI: 10.2307/3177997.
--
-- The source motivates separating equality from sameness and refusing the
-- forced equality-versus-difference opposition.  The theorem shapes below are
-- DASHI constructions: observational distinction, normative standing, essence
-- claims, and situated outcome are independently typed coordinates.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- Generic witness: an observer can distinguish two states while a separate
-- standing map assigns equal standing.
------------------------------------------------------------------------

record DifferenceWithEqualStanding
    {Situated Observation Standing : Set}
    (observe : Situated → Observation)
    (standing : Situated → Standing) : Set where
  constructor difference-with-equal-standing
  field
    left right : Situated
    observationDistinct : observe left ≡ observe right → ⊥
    standingEqual : standing left ≡ standing right

open DifferenceWithEqualStanding public

------------------------------------------------------------------------
-- Uniform treatment can still erase a situated outcome.
------------------------------------------------------------------------

record UniformTreatmentOutcomeFailure
    {Situated Treatment Outcome : Set}
    (treatment : Situated → Treatment)
    (outcome : Situated → Outcome) : Set where
  constructor uniform-treatment-outcome-failure
  field
    left right : Situated
    sameTreatment : treatment left ≡ treatment right
    outcomeDistinct : outcome left ≡ outcome right → ⊥

open UniformTreatmentOutcomeFailure public

uniformTreatmentFailureIsNonFactorability :
  ∀ {Situated Treatment Outcome : Set}
    {treatment : Situated → Treatment}
    {outcome : Situated → Outcome} →
  UniformTreatmentOutcomeFailure treatment outcome →
  INF.NonFactorabilityWitness treatment outcome
uniformTreatmentFailureIsNonFactorability failure =
  INF.nonFactorabilityWitness
    (left failure)
    (right failure)
    (sameTreatment failure)
    (outcomeDistinct failure)

uniformTreatmentCannotRecoverSituatedOutcome :
  ∀ {Situated Treatment Outcome : Set}
    {treatment : Situated → Treatment}
    {outcome : Situated → Outcome} →
  UniformTreatmentOutcomeFailure treatment outcome →
  INF.FactorsThrough treatment outcome → ⊥
uniformTreatmentCannotRecoverSituatedOutcome failure =
  INF.witnessRulesOutEveryFlatFactorisation
    (uniformTreatmentFailureIsNonFactorability failure)

------------------------------------------------------------------------
-- Concrete regression: difference + equal standing.
------------------------------------------------------------------------

data SituatedMode : Set where
  modeA modeB : SituatedMode

data ModeObservation : Set where
  observedA observedB : ModeObservation

data EqualStanding : Set where
  sameStanding : EqualStanding

modeObserver : SituatedMode → ModeObservation
modeObserver modeA = observedA
modeObserver modeB = observedB

modeStanding : SituatedMode → EqualStanding
modeStanding modeA = sameStanding
modeStanding modeB = sameStanding

canonicalDifferenceWithEqualStanding :
  DifferenceWithEqualStanding modeObserver modeStanding
canonicalDifferenceWithEqualStanding =
  difference-with-equal-standing modeA modeB (λ ()) refl

------------------------------------------------------------------------
-- Concrete regression: same nominal treatment + different situated outcome.
------------------------------------------------------------------------

data NominalTreatment : Set where
  sameRule : NominalTreatment

data RealizedOutcome : Set where
  realizedA realizedB : RealizedOutcome

nominalTreatment : SituatedMode → NominalTreatment
nominalTreatment modeA = sameRule
nominalTreatment modeB = sameRule

realizedOutcome : SituatedMode → RealizedOutcome
realizedOutcome modeA = realizedA
realizedOutcome modeB = realizedB

canonicalUniformTreatmentFailure :
  UniformTreatmentOutcomeFailure nominalTreatment realizedOutcome
canonicalUniformTreatmentFailure =
  uniform-treatment-outcome-failure modeA modeB refl (λ ())

canonicalUniformRuleCannotRecoverOutcome :
  INF.FactorsThrough nominalTreatment realizedOutcome → ⊥
canonicalUniformRuleCannotRecoverOutcome =
  uniformTreatmentCannotRecoverSituatedOutcome canonicalUniformTreatmentFailure

------------------------------------------------------------------------
-- Boundary: difference, hierarchy, and essence are separate claims.
------------------------------------------------------------------------

record DifferenceWithoutHierarchyBoundary : Set where
  constructor difference-without-hierarchy-boundary
  field
    observedDifferenceImpliesNormativeHierarchy : Bool
    observedDifferenceImpliesNormativeHierarchyIsFalse :
      observedDifferenceImpliesNormativeHierarchy ≡ false
    observedDifferenceImpliesImmutableEssence : Bool
    observedDifferenceImpliesImmutableEssenceIsFalse :
      observedDifferenceImpliesImmutableEssence ≡ false
    equalStandingImpliesObservationalSameness : Bool
    equalStandingImpliesObservationalSamenessIsFalse :
      equalStandingImpliesObservationalSameness ≡ false
    sameNominalTreatmentImpliesSameSituatedOutcome : Bool
    sameNominalTreatmentImpliesSameSituatedOutcomeIsFalse :
      sameNominalTreatmentImpliesSameSituatedOutcome ≡ false
    erasedDifferenceEstablishesJustice : Bool
    erasedDifferenceEstablishesJusticeIsFalse :
      erasedDifferenceEstablishesJustice ≡ false

canonicalDifferenceWithoutHierarchyBoundary :
  DifferenceWithoutHierarchyBoundary
canonicalDifferenceWithoutHierarchyBoundary =
  difference-without-hierarchy-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
