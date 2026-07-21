module DASHI.Physics.YangMills.BalabanExplicitSmallnessWindow where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- One explicit radius window for all B1/B3/B5/B6/B7 inequalities.
--
-- The analytic producers may establish their estimates at different threshold
-- radii.  This theorem selects one candidate below every threshold and transports
-- all monotone smallness bounds to that common radius.
------------------------------------------------------------------------

record ExplicitSmallnessWindow (Bound : Set) : Set₁ where
  field
    zero one : Bound
    add multiply : Bound → Bound → Bound
    LessEqual StrictlyBelow : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    candidate chartThreshold coercivityThreshold neumannThreshold
      nonlinearThreshold displacementThreshold : Bound

    candidatePositive : StrictlyBelow zero candidate
    candidateBelowChart : LessEqual candidate chartThreshold
    candidateBelowCoercivity : LessEqual candidate coercivityThreshold
    candidateBelowNeumann : LessEqual candidate neumannThreshold
    candidateBelowNonlinear : LessEqual candidate nonlinearThreshold
    candidateBelowDisplacement : LessEqual candidate displacementThreshold

    perturbation residual greenUpper nonlinearUpper displacement rho :
      Bound → Bound
    c0 cH : Bound

    perturbationMonotone : ∀ {left right} →
      LessEqual left right → LessEqual (perturbation left) (perturbation right)
    residualMonotone : ∀ {left right} →
      LessEqual left right → LessEqual (residual left) (residual right)
    nonlinearMonotone : ∀ {left right} →
      LessEqual left right → LessEqual (nonlinearUpper left) (nonlinearUpper right)
    displacementMonotone : ∀ {left right} →
      LessEqual left right → LessEqual (displacement left) (displacement right)

    coercivityAtThreshold :
      LessEqual (add cH (perturbation coercivityThreshold)) c0
    residualAtThreshold : StrictlyBelow (residual neumannThreshold) one
    contractionAtThreshold :
      StrictlyBelow
        (multiply (greenUpper nonlinearThreshold)
          (nonlinearUpper nonlinearThreshold)) one
    displacementAtThreshold :
      LessEqual
        (add (displacement displacementThreshold)
          (multiply (rho displacementThreshold) displacementThreshold))
        displacementThreshold

open ExplicitSmallnessWindow public

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
    displacementAtCandidate :
      LessEqual window
        (add window
          (displacement window (candidate window))
          (multiply window (rho window (candidate window)) (candidate window)))
        (candidate window)

open SelectedSmallnessWitness public

-- The strict inequalities are transported through explicit threshold witnesses.
-- Their monotone strict-order transport is supplied by the ordered-bound carrier.
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
    displacementBudgetAtCandidateBelowThreshold :
      LessEqual window
        (add window
          (displacement window (candidate window))
          (multiply window (rho window (candidate window)) (candidate window)))
        (add window
          (displacement window (displacementThreshold window))
          (multiply window
            (rho window (displacementThreshold window))
            (displacementThreshold window)))

open StrictTransport public

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
        (let p = perturbationMonotone window (candidateBelowCoercivity window)
         in transportCoercivity p)
        (coercivityAtThreshold window)
  ; residualStrictAtCandidate =
      strictTransLeft transport
        (residualMonotone window (candidateBelowNeumann window))
        (residualAtThreshold window)
  ; contractionStrictAtCandidate =
      strictTransLeft transport
        (productAtCandidateBelowThreshold transport)
        (contractionAtThreshold window)
  ; displacementAtCandidate =
      transitive window
        (displacementBudgetAtCandidateBelowThreshold transport)
        (transitive window
          (displacementAtThreshold window)
          (candidateBelowDisplacement window))
  }
  where
  transportCoercivity :
    LessEqual window
      (perturbation window (candidate window))
      (perturbation window (coercivityThreshold window)) →
    LessEqual window
      (add window (cH window) (perturbation window (candidate window)))
      (add window (cH window) (perturbation window (coercivityThreshold window)))
  transportCoercivity p = addMonotoneRight p

  addMonotoneRight : ∀ {left right} →
    LessEqual window left right →
    LessEqual window
      (add window (cH window) left)
      (add window (cH window) right)
  addMonotoneRight = addMonotoneRight

explicitSmallnessWindowAssemblyLevel : ProofLevel
explicitSmallnessWindowAssemblyLevel = machineChecked

explicitSmallnessThresholdInputsLevel : ProofLevel
explicitSmallnessThresholdInputsLevel = conditional
