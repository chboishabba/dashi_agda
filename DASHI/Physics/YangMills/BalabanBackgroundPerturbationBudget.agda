module DASHI.Physics.YangMills.BalabanBackgroundPerturbationBudget where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Producer for the relative Hessian perturbation constant delta.
--
-- Each geometric source of the background perturbation is bounded separately
-- on one common admissible small-field domain.  Their ordered sum is the delta
-- consumed by BalabanRelativeHessianCoercivity.
------------------------------------------------------------------------

record BackgroundPerturbationComponents
    (Index State Bound : Set) : Set₁ where
  field
    perturbationEnergy normSq : Index → State → Bound
    curvaturePart transportPart chartPart gaugePart constraintPart :
      Index → State → Bound
    add scale : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left left′ right right′} →
      LessEqual left left′ → LessEqual right right′ →
      LessEqual (add left right) (add left′ right′)

    curvatureUpper transportUpper chartUpper gaugeUpper constraintUpper : Bound

    perturbationBelowComponents : ∀ index state →
      LessEqual (perturbationEnergy index state)
        (add (curvaturePart index state)
          (add (transportPart index state)
            (add (chartPart index state)
              (add (gaugePart index state) (constraintPart index state)))))

    curvatureBound : ∀ index state →
      LessEqual (curvaturePart index state)
        (scale curvatureUpper (normSq index state))
    transportBound : ∀ index state →
      LessEqual (transportPart index state)
        (scale transportUpper (normSq index state))
    chartBound : ∀ index state →
      LessEqual (chartPart index state)
        (scale chartUpper (normSq index state))
    gaugeBound : ∀ index state →
      LessEqual (gaugePart index state)
        (scale gaugeUpper (normSq index state))
    constraintBound : ∀ index state →
      LessEqual (constraintPart index state)
        (scale constraintUpper (normSq index state))

    combineScaled : ∀ radius →
      add (scale curvatureUpper radius)
        (add (scale transportUpper radius)
          (add (scale chartUpper radius)
            (add (scale gaugeUpper radius) (scale constraintUpper radius))))
      ≡
      scale
        (add curvatureUpper
          (add transportUpper
            (add chartUpper (add gaugeUpper constraintUpper))))
        radius

open BackgroundPerturbationComponents public

perturbationUpper :
  ∀ {Index State Bound : Set} →
  BackgroundPerturbationComponents Index State Bound → Bound
perturbationUpper dataSet =
  add dataSet (curvatureUpper dataSet)
    (add dataSet (transportUpper dataSet)
      (add dataSet (chartUpper dataSet)
        (add dataSet (gaugeUpper dataSet) (constraintUpper dataSet))))

backgroundPerturbationBound :
  ∀ {Index State Bound : Set} →
  (dataSet : BackgroundPerturbationComponents Index State Bound) →
  ∀ index state →
  LessEqual dataSet
    (perturbationEnergy dataSet index state)
    (scale dataSet (perturbationUpper dataSet) (normSq dataSet index state))
backgroundPerturbationBound dataSet index state
  rewrite combineScaled dataSet (normSq dataSet index state) =
  transitive dataSet
    (perturbationBelowComponents dataSet index state)
    (addMonotone dataSet
      (curvatureBound dataSet index state)
      (addMonotone dataSet
        (transportBound dataSet index state)
        (addMonotone dataSet
          (chartBound dataSet index state)
          (addMonotone dataSet
            (gaugeBound dataSet index state)
            (constraintBound dataSet index state)))))

backgroundPerturbationAssemblyLevel : ProofLevel
backgroundPerturbationAssemblyLevel = machineChecked

backgroundPerturbationComponentInputsLevel : ProofLevel
backgroundPerturbationComponentInputsLevel = conditional
