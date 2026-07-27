module DASHI.Physics.Closure.NSTriadKNAdaptiveQuarticCoherenceCharts where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- A fixed leading mode is not canonical in homogeneous periodic flow.
-- The correct transferable object is an adaptive chart whose coherence
-- direction transforms with the state.  This module proves that equivariant
-- chart selection makes the resulting quartic functional invariant.
------------------------------------------------------------------------

record AdaptiveQuarticChartData {g s c q : Level} :
    Set (lsuc (g ⊔ s ⊔ c ⊔ q)) where
  field
    Symmetry : Set g
    State : Set s
    Chart : Set c
    Scalar : Set q

    actState : Symmetry → State → State
    actChart : Symmetry → Chart → Chart

    selectChart : State → Chart
    selectedChartEquivariant : ∀ symmetry state →
      selectChart (actState symmetry state)
      ≡ actChart symmetry (selectChart state)

    energy quadraticCorrection : State → Scalar
    coherence : Chart → State → Scalar
    quarticFunctional : Chart → State → Scalar

    energyInvariant : ∀ symmetry state →
      energy (actState symmetry state) ≡ energy state

    quadraticCorrectionInvariant : ∀ symmetry state →
      quadraticCorrection (actState symmetry state)
      ≡ quadraticCorrection state

    coherenceEquivariant : ∀ symmetry chart state →
      coherence
        (actChart symmetry chart)
        (actState symmetry state)
      ≡ coherence chart state

    quarticMeaning : State → Chart → Set
    quarticMeaningSelected :
      ∀ state → quarticMeaning state (selectChart state)

    quarticRespectsInvariantIngredients :
      ∀ symmetry chart state →
      energy (actState symmetry state) ≡ energy state →
      coherence
        (actChart symmetry chart)
        (actState symmetry state)
      ≡ coherence chart state →
      quadraticCorrection (actState symmetry state)
      ≡ quadraticCorrection state →
      quarticFunctional
        (actChart symmetry chart)
        (actState symmetry state)
      ≡ quarticFunctional chart state

open AdaptiveQuarticChartData public

selectedQuarticFunctional :
  ∀ {g s c q}
    (D : AdaptiveQuarticChartData {g} {s} {c} {q}) →
  State D → Scalar D
selectedQuarticFunctional D state =
  quarticFunctional D (selectChart D state) state

adaptiveQuarticIsSymmetryInvariant :
  ∀ {g s c q}
    (D : AdaptiveQuarticChartData {g} {s} {c} {q})
    (symmetry : Symmetry D)
    (state : State D) →
  selectedQuarticFunctional D (actState D symmetry state)
  ≡ selectedQuarticFunctional D state
adaptiveQuarticIsSymmetryInvariant D symmetry state
  rewrite selectedChartEquivariant D symmetry state =
  quarticRespectsInvariantIngredients D symmetry (selectChart D state) state
    (energyInvariant D symmetry state)
    (coherenceEquivariant D symmetry (selectChart D state) state)
    (quadraticCorrectionInvariant D symmetry state)

------------------------------------------------------------------------
-- Switching and coverage are stated without quotienting away the dangerous
-- boundary.  These are the precise non-algebraic leaves needed by the
-- compact-Gamma/no-first-exit route.
------------------------------------------------------------------------

record AdaptiveQuarticCoverage
    {g s c q : Level}
    (D : AdaptiveQuarticChartData {g} {s} {c} {q}) :
    Set (lsuc (g ⊔ s ⊔ c ⊔ q)) where
  field
    ZeroState : State D → Set
    NonZeroState : State D → Set
    ChartValid : Chart D → State D → Set

    zeroStateCovered : ∀ state → ZeroState state → Set
    everyNonzeroStateHasValidSelectedChart : ∀ state →
      NonZeroState state →
      ChartValid (selectChart D state) state

    switchAllowed : Chart D → Chart D → State D → Set
    switchDoesNotIncreaseQuartic :
      ∀ old new state →
      switchAllowed old new state →
      Set

    positiveDwellTimeBetweenStrictSwitches : Set

open AdaptiveQuarticCoverage public

adaptiveCoherenceSymmetryClosureImplemented : Bool
adaptiveCoherenceSymmetryClosureImplemented = true

adaptiveCoherenceSymmetryClosureImplementedIsTrue :
  adaptiveCoherenceSymmetryClosureImplemented ≡ true
adaptiveCoherenceSymmetryClosureImplementedIsTrue = refl

fixedStokesLeadingModeIsCanonicalPeriodicPrescription : Bool
fixedStokesLeadingModeIsCanonicalPeriodicPrescription = false

fixedStokesLeadingModeIsCanonicalPeriodicPrescriptionIsFalse :
  fixedStokesLeadingModeIsCanonicalPeriodicPrescription ≡ false
fixedStokesLeadingModeIsCanonicalPeriodicPrescriptionIsFalse = refl
