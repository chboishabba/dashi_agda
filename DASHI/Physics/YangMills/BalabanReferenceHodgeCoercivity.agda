module DASHI.Physics.YangMills.BalabanReferenceHodgeCoercivity where

open import DASHI.Physics.YangMills.CompactLieProofLevel

record ReferenceHodgeCoercivityData
    (Index State Bound : Set) : Set₁ where
  field
    derivativeEnergy gaugeEnergy blockEnergy referenceEnergy normSq : Index → State → Bound
    add scale : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    hodgeConstant c0 : Bound
    referenceEnergyDefinition : ∀ index state →
      referenceEnergy index state ≡
      add (derivativeEnergy index state)
        (add (gaugeEnergy index state) (blockEnergy index state))

    uniformHodgePoincare : ∀ index state →
      LessEqual (scale hodgeConstant (normSq index state))
        (add (derivativeEnergy index state)
          (add (gaugeEnergy index state) (blockEnergy index state)))

    c0BelowHodge : ∀ index state →
      LessEqual (scale c0 (normSq index state))
        (scale hodgeConstant (normSq index state))

    Positive : Bound → Set
    c0Positive : Positive c0

open ReferenceHodgeCoercivityData public

referenceHessianCoercive :
  ∀ {Index State Bound : Set} →
  (dataSet : ReferenceHodgeCoercivityData Index State Bound) →
  ∀ index state →
  LessEqual dataSet
    (scale dataSet (c0 dataSet) (normSq dataSet index state))
    (referenceEnergy dataSet index state)
referenceHessianCoercive dataSet index state =
  transitive dataSet
    (c0BelowHodge dataSet index state)
    (transitive dataSet
      (uniformHodgePoincare dataSet index state)
      (rewrite referenceEnergyDefinition dataSet index state in
       let open ReferenceHodgeCoercivityData dataSet in
       uniformHodgePoincare dataSet index state))

referenceHodgeCoercivityAssemblyLevel : ProofLevel
referenceHodgeCoercivityAssemblyLevel = machineChecked

referenceHodgePoincareInputsLevel : ProofLevel
referenceHodgePoincareInputsLevel = conditional
