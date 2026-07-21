module DASHI.Physics.YangMills.BalabanExplicitSmallnessWindow where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- One explicit radius window for all B1/B3/B5/B6/B7 inequalities.
------------------------------------------------------------------------

record ExplicitSmallnessWindow (Bound : Set) : Set₁ where
  field
    zero one : Bound
    add multiply : Bound → Bound → Bound
    LessEqual StrictlyBelow : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotoneRight : ∀ prefix {left right} →
      LessEqual left right → LessEqual (add prefix left) (add prefix right)

    candidate chartThreshold coercivityThreshold neumannThreshold
      nonlinearThreshold : Bound

    candidatePositive : StrictlyBelow zero candidate
    candidateBelowChart : LessEqual candidate chartThreshold
    candidateBelowCoercivity : LessEqual candidate coercivityThreshold
    candidateBelowNeumann : LessEqual candidate neumannThreshold
    candidateBelowNonlinear : LessEqual candidate nonlinearThreshold

    perturbation residual greenUpper nonlinearUpper : Bound → Bound
    c0 cH : Bound

    perturbationMonotone : ∀ {left right} →
      LessEqual left right → LessEqual (perturbation left) (perturbation right)
    residualMonotone : ∀ {left right} →
      LessEqual left right → LessEqual (residual left) (residual right)

    coercivityAtThreshold :
      LessEqual (add cH (perturbation coercivityThreshold)) c0
    residualAtThreshold : StrictlyBelow (residual neumannThreshold) one
    contractionAtThreshold :
      StrictlyBelow
        (multiply (greenUpper nonlinearThreshold)
          (nonlinearUpper nonlinearThreshold)) one

open ExplicitSmallnessWindow public

record StrictTransport {Bound : Set}
    (window : ExplicitSmallnessWindow Bound) : Set₁ where
  field
    strictTransLeft : ∀ {left middle right} →
      LessEqual window left middle →
      StrictlyBelow window middle right →
      StrictlyBelow window left right
    productAtCandidateBelowThreshold :
      LessEqual window
        (multiply window
          (greenUpper window (candidate window))
          (nonlinearUpper window (candidate window)))
        (multiply window
          (greenUpper window (nonlinearThreshold window))
          (nonlinearUpper window (nonlinearThreshold window)))

open StrictTransport public

record SelectedSmallnessWitness {Bound : Set}
    (window : ExplicitSmallnessWindow Bound) : Set₁ where
  field
    positiveRadius : StrictlyBelow window (zero window) (candidate window)
    chartAdmissible : LessEqual window (candidate window) (chartThreshold window)
    coerciveAtCandidate :
      LessEqual window
        (add window (cH window) (perturbation window (candidate window)))
        (c0 window)
    residualStrictAtCandidate :
      StrictlyBelow window (residual window (candidate window)) (one window)
    contractionStrictAtCandidate :
      StrictlyBelow window
        (multiply window
          (greenUpper window (candidate window))
          (nonlinearUpper window (candidate window)))
        (one window)

open SelectedSmallnessWitness public

selectCommonRadius :
  ∀ {Bound : Set} →
  (window : ExplicitSmallnessWindow Bound) →
  StrictTransport window →
  SelectedSmallnessWitness window
selectCommonRadius window transport = record
  { positiveRadius = candidatePositive window
  ; chartAdmissible = candidateBelowChart window
  ; coerciveAtCandidate =
      transitive window
        (addMonotoneRight window (cH window)
          (perturbationMonotone window (candidateBelowCoercivity window)))
        (coercivityAtThreshold window)
  ; residualStrictAtCandidate =
      strictTransLeft transport
        (residualMonotone window (candidateBelowNeumann window))
        (residualAtThreshold window)
  ; contractionStrictAtCandidate =
      strictTransLeft transport
        (productAtCandidateBelowThreshold transport)
        (contractionAtThreshold window)
  }

explicitSmallnessWindowAssemblyLevel : ProofLevel
explicitSmallnessWindowAssemblyLevel = machineChecked

explicitSmallnessThresholdInputsLevel : ProofLevel
explicitSmallnessThresholdInputsLevel = conditional
