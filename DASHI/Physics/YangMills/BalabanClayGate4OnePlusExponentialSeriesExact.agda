module DASHI.Physics.YangMills.BalabanClayGate4OnePlusExponentialSeriesExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary provenance.
--
-- Errett Bishop and Douglas Bridges,
-- "Constructive Analysis", Springer (1985).
-- DOI: 10.1007/978-3-642-61667-9.
--
-- The proof is the ordered power-series fact
--   exp(x) = 1 + x + sum_{n>=2} x^n/n!,
-- with a nonnegative tail on the selected nonnegative domain. The tail
-- positivity and series identity remain explicit constructive-analysis inputs.
------------------------------------------------------------------------

record ExponentialNonnegativeTail (Scalar : Set) : Set₁ where
  field
    zero one : Scalar
    add : Scalar → Scalar → Scalar
    exponential tail : Scalar → Scalar
    Nonnegative : Scalar → Set
    LessEqual : Scalar → Scalar → Set

    addZeroRight : ∀ value → add value zero ≡ value
    addMonotoneRight : ∀ {left right} common →
      LessEqual left right → LessEqual (add common left) (add common right)

    tailNonnegative : ∀ value → Nonnegative value → Nonnegative (tail value)
    nonnegativeMeansZeroBelow : ∀ {value} →
      Nonnegative value → LessEqual zero value

    exponentialSeriesSplit : ∀ value →
      exponential value ≡ add (add one value) (tail value)

open ExponentialNonnegativeTail public

onePlusBelowExponential :
  ∀ {Scalar} (dataSet : ExponentialNonnegativeTail Scalar) value →
  Nonnegative dataSet value →
  LessEqual dataSet
    (add dataSet (one dataSet) value)
    (exponential dataSet value)
onePlusBelowExponential dataSet value nonnegative =
  subst
    (λ upper → LessEqual dataSet
      (add dataSet (one dataSet) value) upper)
    (sym (exponentialSeriesSplit dataSet value))
    (subst
      (λ lower → LessEqual dataSet lower
        (add dataSet (add dataSet (one dataSet) value)
          (tail dataSet value)))
      (addZeroRight dataSet (add dataSet (one dataSet) value))
      (addMonotoneRight dataSet
        (add dataSet (one dataSet) value)
        (nonnegativeMeansZeroBelow dataSet
          (tailNonnegative dataSet value nonnegative))))

exponentialTailOrderAssemblyLevel : ProofLevel
exponentialTailOrderAssemblyLevel = machineChecked

onePlusExponentialSeriesAssemblyLevel : ProofLevel
onePlusExponentialSeriesAssemblyLevel = machineChecked

constructiveExponentialSeriesSplitInputsLevel : ProofLevel
constructiveExponentialSeriesSplitInputsLevel = conditional

constructiveExponentialTailNonnegativeInputsLevel : ProofLevel
constructiveExponentialTailNonnegativeInputsLevel = conditional
