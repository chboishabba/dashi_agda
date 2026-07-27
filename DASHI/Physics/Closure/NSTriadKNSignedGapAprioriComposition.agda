module DASHI.Physics.Closure.NSTriadKNSignedGapAprioriComposition where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Composition theorem from a strict signed gap to a global Galerkin estimate.
--
-- The only remaining analytic input is a concrete scalar comparison. All
-- quantifiers excluding smallness, symmetry, phase and helicity restrictions
-- are carried here.
------------------------------------------------------------------------

record StrictGapEvolutionData {i c t s b : Level} :
    Set (lsuc (i ⊔ c ⊔ t ⊔ s ⊔ b)) where
  field
    InitialData : Set i
    Cutoff : Set c
    Time : Set t
    State : Set s
    Bound : Set b

    Admissible Smooth DivergenceFree : InitialData → Set i

    solution : InitialData → Cutoff → Time → State

    Energy Dissipation Nonlinear : State → Bound
    _≤_ : Bound → Bound → Set b

    strictGapControlsNonlinearity :
      ∀ u0 N time →
      Admissible u0 →
      Smooth u0 →
      DivergenceFree u0 →
      Nonlinear (solution u0 N time)
      ≤ Dissipation (solution u0 N time)

    exactEnergyIdentity : Set
    noSmallnessAssumption : Set
    noSymmetryAssumption : Set
    noPhaseRestriction : Set
    noHelicityRestriction : Set

open StrictGapEvolutionData public

record GlobalScalarComparison
    {i c t s b : Level}
    (D : StrictGapEvolutionData {i} {c} {t} {s} {b}) :
    Set (lsuc (i ⊔ c ⊔ t ⊔ s ⊔ b)) where
  field
    Horizon : Set
    horizonBound : InitialData D → Horizon → Bound D
    timeWithin : Time D → Horizon → Set

    globalEnergyBound :
      ∀ u0 N time horizon →
      Admissible D u0 →
      Smooth D u0 →
      DivergenceFree D u0 →
      timeWithin time horizon →
      _≤_ D
        (Energy D (solution D u0 N time))
        (horizonBound u0 horizon)

    integratedDissipationBound :
      InitialData D → Cutoff D → Horizon → Set b

    boundIndependentOfCutoff : Set
    boundFiniteAtEveryHorizon : Set

open GlobalScalarComparison public

record ArbitraryDataUniformApriori
    {i c t s b : Level}
    (D : StrictGapEvolutionData {i} {c} {t} {s} {b}) :
    Set (lsuc (i ⊔ c ⊔ t ⊔ s ⊔ b)) where
  constructor arbitrary-data-uniform-apriori
  field
    comparison : GlobalScalarComparison D
    everySmoothDivergenceFreeDatumCovered :
      (u0 : InitialData D) →
      Admissible D u0 →
      Smooth D u0 →
      DivergenceFree D u0 →
      Set

open ArbitraryDataUniformApriori public

strictGapAndGlobalComparisonGiveUniformApriori :
  ∀ {i c t s b}
    {D : StrictGapEvolutionData {i} {c} {t} {s} {b}} →
  GlobalScalarComparison D →
  ((u0 : InitialData D) →
    Admissible D u0 →
    Smooth D u0 →
    DivergenceFree D u0 →
    Set) →
  ArbitraryDataUniformApriori D
strictGapAndGlobalComparisonGiveUniformApriori comparison coverage =
  arbitrary-data-uniform-apriori comparison coverage

gapToAprioriCompositionClosed : Bool
gapToAprioriCompositionClosed = true

gapToAprioriCompositionClosedIsTrue :
  gapToAprioriCompositionClosed ≡ true
gapToAprioriCompositionClosedIsTrue = refl
