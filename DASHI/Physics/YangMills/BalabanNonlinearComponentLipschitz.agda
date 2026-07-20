module DASHI.Physics.YangMills.BalabanNonlinearComponentLipschitz where

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanBackgroundFieldClosure as Background

record SevenComponentNonlinearData
    (Index State Bound : Set) : Set₁ where
  field
    nonlinear : Index → State → State
    bchPart commutatorPart transportPart backgroundDerivativePart
      gaugeFixingPart blockConstraintPart chartChangePart :
      Index → State → State
    subtract : State → State → State
    norm : State → Bound
    add multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    InCriticalBall : Index → State → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left left′ right right′} →
      LessEqual left left′ → LessEqual right right′ →
      LessEqual (add left right) (add left′ right′)
    bchUpper commutatorUpper transportUpper backgroundDerivativeUpper
      gaugeFixingUpper blockConstraintUpper chartChangeUpper : Bound
    nonlinearDifferenceBelowParts : ∀ index left right →
      InCriticalBall index left → InCriticalBall index right →
      LessEqual
        (norm (subtract (nonlinear index left) (nonlinear index right)))
        (add
          (norm (subtract (bchPart index left) (bchPart index right)))
          (add
            (norm (subtract (commutatorPart index left)
              (commutatorPart index right)))
            (add
              (norm (subtract (transportPart index left)
                (transportPart index right)))
              (add
                (norm (subtract (backgroundDerivativePart index left)
                  (backgroundDerivativePart index right)))
                (add
                  (norm (subtract (gaugeFixingPart index left)
                    (gaugeFixingPart index right)))
                  (add
                    (norm (subtract (blockConstraintPart index left)
                      (blockConstraintPart index right)))
                    (norm (subtract (chartChangePart index left)
                      (chartChangePart index right)))))))))
    bchLipschitz : ∀ index left right →
      InCriticalBall index left → InCriticalBall index right →
      LessEqual
        (norm (subtract (bchPart index left) (bchPart index right)))
        (multiply bchUpper (norm (subtract left right)))
    commutatorLipschitz : ∀ index left right →
      InCriticalBall index left → InCriticalBall index right →
      LessEqual
        (norm (subtract (commutatorPart index left)
          (commutatorPart index right)))
        (multiply commutatorUpper (norm (subtract left right)))
    transportLipschitz : ∀ index left right →
      InCriticalBall index left → InCriticalBall index right →
      LessEqual
        (norm (subtract (transportPart index left) (transportPart index right)))
        (multiply transportUpper (norm (subtract left right)))
    backgroundDerivativeLipschitz : ∀ index left right →
      InCriticalBall index left → InCriticalBall index right →
      LessEqual
        (norm (subtract (backgroundDerivativePart index left)
          (backgroundDerivativePart index right)))
        (multiply backgroundDerivativeUpper (norm (subtract left right)))
    gaugeFixingLipschitz : ∀ index left right →
      InCriticalBall index left → InCriticalBall index right →
      LessEqual
        (norm (subtract (gaugeFixingPart index left)
          (gaugeFixingPart index right)))
        (multiply gaugeFixingUpper (norm (subtract left right)))
    blockConstraintLipschitz : ∀ index left right →
      InCriticalBall index left → InCriticalBall index right →
      LessEqual
        (norm (subtract (blockConstraintPart index left)
          (blockConstraintPart index right)))
        (multiply blockConstraintUpper (norm (subtract left right)))
    chartChangeLipschitz : ∀ index left right →
      InCriticalBall index left → InCriticalBall index right →
      LessEqual
        (norm (subtract (chartChangePart index left)
          (chartChangePart index right)))
        (multiply chartChangeUpper (norm (subtract left right)))
    addScaledConstants : ∀ radius →
      add
        (multiply bchUpper radius)
        (add
          (multiply commutatorUpper radius)
          (add
            (multiply transportUpper radius)
            (add
              (multiply backgroundDerivativeUpper radius)
              (add
                (multiply gaugeFixingUpper radius)
                (add
                  (multiply blockConstraintUpper radius)
                  (multiply chartChangeUpper radius))))))
      ≡
      multiply
        (add bchUpper
          (add commutatorUpper
            (add transportUpper
              (add backgroundDerivativeUpper
                (add gaugeFixingUpper
                  (add blockConstraintUpper chartChangeUpper))))))
        radius
    BCHHigherControl CommutatorControl ParallelTransportControl
      BackgroundDerivativeControl GaugeFixingControl BlockConstraintControl
      ChartChangeControl : Index → Set
    bchHigherControl : ∀ index → BCHHigherControl index
    commutatorControl : ∀ index → CommutatorControl index
    parallelTransportControl : ∀ index → ParallelTransportControl index
    backgroundDerivativeControl : ∀ index → BackgroundDerivativeControl index
    gaugeFixingControl : ∀ index → GaugeFixingControl index
    blockConstraintControl : ∀ index → BlockConstraintControl index
    chartChangeControl : ∀ index → ChartChangeControl index

open SevenComponentNonlinearData public

nonlinearUpper :
  ∀ {Index State Bound : Set} →
  SevenComponentNonlinearData Index State Bound → Bound
nonlinearUpper dataSet =
  add dataSet (bchUpper dataSet)
    (add dataSet (commutatorUpper dataSet)
      (add dataSet (transportUpper dataSet)
        (add dataSet (backgroundDerivativeUpper dataSet)
          (add dataSet (gaugeFixingUpper dataSet)
            (add dataSet (blockConstraintUpper dataSet)
              (chartChangeUpper dataSet))))))

componentSumBound :
  ∀ {Index State Bound : Set} →
  (dataSet : SevenComponentNonlinearData Index State Bound) →
  ∀ index left right →
  InCriticalBall dataSet index left → InCriticalBall dataSet index right →
  LessEqual dataSet
    (add dataSet
      (norm dataSet (subtract dataSet
        (bchPart dataSet index left) (bchPart dataSet index right)))
      (add dataSet
        (norm dataSet (subtract dataSet
          (commutatorPart dataSet index left)
          (commutatorPart dataSet index right)))
        (add dataSet
          (norm dataSet (subtract dataSet
            (transportPart dataSet index left)
            (transportPart dataSet index right)))
          (add dataSet
            (norm dataSet (subtract dataSet
              (backgroundDerivativePart dataSet index left)
              (backgroundDerivativePart dataSet index right)))
            (add dataSet
              (norm dataSet (subtract dataSet
                (gaugeFixingPart dataSet index left)
                (gaugeFixingPart dataSet index right)))
              (add dataSet
                (norm dataSet (subtract dataSet
                  (blockConstraintPart dataSet index left)
                  (blockConstraintPart dataSet index right)))
                (norm dataSet (subtract dataSet
                  (chartChangePart dataSet index left)
                  (chartChangePart dataSet index right)))))))))
    (multiply dataSet (nonlinearUpper dataSet)
      (norm dataSet (subtract dataSet left right)))
componentSumBound dataSet index left right leftBall rightBall
  rewrite addScaledConstants dataSet (norm dataSet (subtract dataSet left right)) =
  addMonotone dataSet
    (bchLipschitz dataSet index left right leftBall rightBall)
    (addMonotone dataSet
      (commutatorLipschitz dataSet index left right leftBall rightBall)
      (addMonotone dataSet
        (transportLipschitz dataSet index left right leftBall rightBall)
        (addMonotone dataSet
          (backgroundDerivativeLipschitz dataSet index left right leftBall rightBall)
          (addMonotone dataSet
            (gaugeFixingLipschitz dataSet index left right leftBall rightBall)
            (addMonotone dataSet
              (blockConstraintLipschitz dataSet index left right leftBall rightBall)
              (chartChangeLipschitz dataSet index left right leftBall rightBall))))))

uniformNonlinearLipschitz :
  ∀ {Index State Bound : Set} →
  (dataSet : SevenComponentNonlinearData Index State Bound) →
  ∀ index left right →
  InCriticalBall dataSet index left → InCriticalBall dataSet index right →
  LessEqual dataSet
    (norm dataSet (subtract dataSet
      (nonlinear dataSet index left) (nonlinear dataSet index right)))
    (multiply dataSet (nonlinearUpper dataSet)
      (norm dataSet (subtract dataSet left right)))
uniformNonlinearLipschitz dataSet index left right leftBall rightBall =
  transitive dataSet
    (nonlinearDifferenceBelowParts dataSet index left right leftBall rightBall)
    (componentSumBound dataSet index left right leftBall rightBall)

toUniformNonlinearRemainderEstimate :
  ∀ {Index State Bound : Set} →
  (dataSet : SevenComponentNonlinearData Index State Bound) →
  Background.UniformNonlinearRemainderEstimate Index State Bound
toUniformNonlinearRemainderEstimate dataSet = record
  { nonlinear = nonlinear dataSet
  ; subtract = subtract dataSet
  ; norm = norm dataSet
  ; multiply = multiply dataSet
  ; LessEqual = LessEqual dataSet
  ; InCriticalBall = InCriticalBall dataSet
  ; nonlinearUpper = nonlinearUpper dataSet
  ; uniformNonlinearRemainderLipschitz = uniformNonlinearLipschitz dataSet
  ; BCHHigherControl = BCHHigherControl dataSet
  ; CommutatorControl = CommutatorControl dataSet
  ; ParallelTransportControl = ParallelTransportControl dataSet
  ; BackgroundDerivativeControl = BackgroundDerivativeControl dataSet
  ; GaugeFixingControl = GaugeFixingControl dataSet
  ; BlockConstraintControl = BlockConstraintControl dataSet
  ; ChartChangeControl = ChartChangeControl dataSet
  ; bchHigherControl = bchHigherControl dataSet
  ; commutatorControl = commutatorControl dataSet
  ; parallelTransportControl = parallelTransportControl dataSet
  ; backgroundDerivativeControl = backgroundDerivativeControl dataSet
  ; gaugeFixingControl = gaugeFixingControl dataSet
  ; blockConstraintControl = blockConstraintControl dataSet
  ; chartChangeControl = chartChangeControl dataSet
  }

nonlinearComponentAssemblyLevel : ProofLevel
nonlinearComponentAssemblyLevel = machineChecked

nonlinearComponentEstimateInputsLevel : ProofLevel
nonlinearComponentEstimateInputsLevel = conditional
