module DASHI.Physics.YangMills.BalabanMultilinearLipschitzCalculus where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Reusable analytic reduction for the seven nonlinear components.
--
-- The exact algebraic difference identities are supplied by a concrete map
-- (BCH commutator, transport product, chart term, ...).  Triangle inequality
-- and the map's multilinear norm bound then produce the complete Lipschitz
-- estimate.  This prevents the seven producers from each re-assuming the final
-- difference inequality as a primitive fact.
------------------------------------------------------------------------

record BilinearLipschitzData (State Bound : Set) : Set₁ where
  field
    bilinear : State → State → State
    addState subtractState : State → State → State
    norm : State → Bound

    addBound multiplyBound : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left left′ right right′} →
      LessEqual left left′ → LessEqual right right′ →
      LessEqual (addBound left right) (addBound left′ right′)
    multiplyMonotone : ∀ {left left′ right right′} →
      LessEqual left left′ → LessEqual right right′ →
      LessEqual (multiplyBound left right) (multiplyBound left′ right′)

    differenceIdentity : ∀ left right left′ right′ →
      subtractState
        (bilinear left right)
        (bilinear left′ right′)
      ≡ addState
          (bilinear left (subtractState right right′))
          (bilinear (subtractState left left′) right′)

    triangle : ∀ left right →
      LessEqual
        (norm (addState left right))
        (addBound (norm left) (norm right))

    bilinearConstant : Bound
    bilinearNormBound : ∀ left right →
      LessEqual
        (norm (bilinear left right))
        (multiplyBound bilinearConstant
          (multiplyBound (norm left) (norm right)))

open BilinearLipschitzData public

bilinearDifferenceBound :
  ∀ {State Bound}
    (dataSet : BilinearLipschitzData State Bound)
    left right left′ right′ →
  LessEqual dataSet
    (norm dataSet
      (subtractState dataSet
        (bilinear dataSet left right)
        (bilinear dataSet left′ right′)))
    (addBound dataSet
      (multiplyBound dataSet (bilinearConstant dataSet)
        (multiplyBound dataSet
          (norm dataSet left)
          (norm dataSet (subtractState dataSet right right′))))
      (multiplyBound dataSet (bilinearConstant dataSet)
        (multiplyBound dataSet
          (norm dataSet (subtractState dataSet left left′))
          (norm dataSet right′))))
bilinearDifferenceBound dataSet left right left′ right′
  rewrite differenceIdentity dataSet left right left′ right′ =
  transitive dataSet
    (triangle dataSet
      (bilinear dataSet left (subtractState dataSet right right′))
      (bilinear dataSet (subtractState dataSet left left′) right′))
    (addMonotone dataSet
      (bilinearNormBound dataSet left
        (subtractState dataSet right right′))
      (bilinearNormBound dataSet
        (subtractState dataSet left left′) right′))

record TrilinearLipschitzData (State Bound : Set) : Set₁ where
  field
    trilinear : State → State → State → State
    addState subtractState : State → State → State
    norm : State → Bound

    addBound multiplyBound : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left left′ right right′} →
      LessEqual left left′ → LessEqual right right′ →
      LessEqual (addBound left right) (addBound left′ right′)

    differenceIdentity : ∀ x y z x′ y′ z′ →
      subtractState
        (trilinear x y z)
        (trilinear x′ y′ z′)
      ≡ addState
          (trilinear x y (subtractState z z′))
          (addState
            (trilinear x (subtractState y y′) z′)
            (trilinear (subtractState x x′) y′ z′))

    triangle : ∀ left right →
      LessEqual
        (norm (addState left right))
        (addBound (norm left) (norm right))

    trilinearConstant : Bound
    trilinearNormBound : ∀ x y z →
      LessEqual
        (norm (trilinear x y z))
        (multiplyBound trilinearConstant
          (multiplyBound (norm x)
            (multiplyBound (norm y) (norm z))))

open TrilinearLipschitzData public

trilinearDifferenceBound :
  ∀ {State Bound}
    (dataSet : TrilinearLipschitzData State Bound)
    x y z x′ y′ z′ →
  LessEqual dataSet
    (norm dataSet
      (subtractState dataSet
        (trilinear dataSet x y z)
        (trilinear dataSet x′ y′ z′)))
    (addBound dataSet
      (multiplyBound dataSet (trilinearConstant dataSet)
        (multiplyBound dataSet (norm dataSet x)
          (multiplyBound dataSet (norm dataSet y)
            (norm dataSet (subtractState dataSet z z′)))))
      (addBound dataSet
        (multiplyBound dataSet (trilinearConstant dataSet)
          (multiplyBound dataSet (norm dataSet x)
            (multiplyBound dataSet
              (norm dataSet (subtractState dataSet y y′))
              (norm dataSet z′))))
        (multiplyBound dataSet (trilinearConstant dataSet)
          (multiplyBound dataSet
            (norm dataSet (subtractState dataSet x x′))
            (multiplyBound dataSet (norm dataSet y′) (norm dataSet z′))))))
trilinearDifferenceBound dataSet x y z x′ y′ z′
  rewrite differenceIdentity dataSet x y z x′ y′ z′ =
  transitive dataSet
    (triangle dataSet
      (trilinear dataSet x y (subtractState dataSet z z′))
      (addState dataSet
        (trilinear dataSet x (subtractState dataSet y y′) z′)
        (trilinear dataSet (subtractState dataSet x x′) y′ z′)))
    (addMonotone dataSet
      (trilinearNormBound dataSet x y (subtractState dataSet z z′))
      (transitive dataSet
        (triangle dataSet
          (trilinear dataSet x (subtractState dataSet y y′) z′)
          (trilinear dataSet (subtractState dataSet x x′) y′ z′))
        (addMonotone dataSet
          (trilinearNormBound dataSet x
            (subtractState dataSet y y′) z′)
          (trilinearNormBound dataSet
            (subtractState dataSet x x′) y′ z′))))

bilinearLipschitzReductionLevel : ProofLevel
bilinearLipschitzReductionLevel = machineChecked

trilinearLipschitzReductionLevel : ProofLevel
trilinearLipschitzReductionLevel = machineChecked

literalSevenComponentMapInstantiationsLevel : ProofLevel
literalSevenComponentMapInstantiationsLevel = conditional
