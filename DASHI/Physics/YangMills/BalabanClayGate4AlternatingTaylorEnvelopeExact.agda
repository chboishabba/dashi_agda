module DASHI.Physics.YangMills.BalabanClayGate4AlternatingTaylorEnvelopeExact where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Constructive Taylor-envelope algebra.
--
-- The usual first-omitted-term estimates are often imported as complete
-- inequalities.  Here the analytic proof boundary is lower: a caller supplies
-- the signed series decomposition and the sign/order of the remainder, while
-- this module derives the absolute-value bound.  The equality is setoid-valued
-- so the result applies directly to Bishop regular-sequence reals.
------------------------------------------------------------------------

record OrderedAbsoluteAlgebra (Scalar : Set) : Set₁ where
  field
    zero : Scalar
    add subtract : Scalar → Scalar → Scalar
    negate absolute : Scalar → Scalar

    Equivalent LessEqual : Scalar → Scalar → Set

    equivalentRefl : ∀ value → Equivalent value value
    equivalentSym : ∀ {left right} →
      Equivalent left right → Equivalent right left
    equivalentTrans : ∀ {left middle right} →
      Equivalent left middle → Equivalent middle right →
      Equivalent left right

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    lessEqualResp : ∀ {left left′ right right′} →
      Equivalent left left′ → Equivalent right right′ →
      LessEqual left right → LessEqual left′ right′

    absoluteCong : ∀ {left right} →
      Equivalent left right →
      Equivalent (absolute left) (absolute right)

    absoluteNegate : ∀ value →
      Equivalent (absolute (negate value)) (absolute value)

    absoluteOfNonnegative : ∀ {value} →
      LessEqual zero value →
      Equivalent (absolute value) value

    subtractNonnegative : ∀ {small large} →
      LessEqual small large →
      LessEqual zero (subtract large small)

    subtractBelowLeft : ∀ {small large} →
      LessEqual zero small →
      LessEqual small large →
      LessEqual (subtract large small) large

    addNonnegative : ∀ {left right} →
      LessEqual zero left → LessEqual zero right →
      LessEqual zero (add left right)

    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (add left right) (add leftUpper rightUpper)

open OrderedAbsoluteAlgebra public

record AlternatingFirstOmittedCertificate
    {Scalar : Set} (algebra : OrderedAbsoluteAlgebra Scalar) : Set₁ where
  field
    value centre leading remainder : Scalar

    remainderNonnegative : LessEqual algebra (zero algebra) remainder
    remainderBelowLeading : LessEqual algebra remainder leading

    -- value - centre = -(leading - remainder)
    signedDifferenceMeaning :
      Equivalent algebra
        (subtract algebra value centre)
        (negate algebra (subtract algebra leading remainder))

open AlternatingFirstOmittedCertificate public

alternatingDifferenceAbsoluteMeaning :
  ∀ {Scalar}
    {algebra : OrderedAbsoluteAlgebra Scalar}
    (certificate : AlternatingFirstOmittedCertificate algebra) →
  Equivalent algebra
    (absolute algebra
      (subtract algebra (value certificate) (centre certificate)))
    (subtract algebra (leading certificate) (remainder certificate))
alternatingDifferenceAbsoluteMeaning {algebra = algebra} certificate =
  equivalentTrans algebra
    (absoluteCong algebra (signedDifferenceMeaning certificate))
    (equivalentTrans algebra
      (absoluteNegate algebra
        (subtract algebra
          (leading certificate) (remainder certificate)))
      (absoluteOfNonnegative algebra
        (subtractNonnegative algebra
          (remainderBelowLeading certificate))))

alternatingFirstOmittedAbsoluteBound :
  ∀ {Scalar}
    {algebra : OrderedAbsoluteAlgebra Scalar}
    (certificate : AlternatingFirstOmittedCertificate algebra) →
  LessEqual algebra
    (absolute algebra
      (subtract algebra (value certificate) (centre certificate)))
    (leading certificate)
alternatingFirstOmittedAbsoluteBound {algebra = algebra} certificate =
  lessEqualResp algebra
    (equivalentSym algebra
      (alternatingDifferenceAbsoluteMeaning certificate))
    (equivalentRefl algebra (leading certificate))
    (subtractBelowLeft algebra
      (remainderNonnegative certificate)
      (remainderBelowLeading certificate))

record PositiveTaylorTailCertificate
    {Scalar : Set} (algebra : OrderedAbsoluteAlgebra Scalar) : Set₁ where
  field
    value centre leading remainder tailBudget : Scalar

    leadingNonnegative : LessEqual algebra (zero algebra) leading
    remainderNonnegative : LessEqual algebra (zero algebra) remainder
    remainderBelowTailBudget : LessEqual algebra remainder tailBudget

    -- value - centre = leading + remainder
    positiveDifferenceMeaning :
      Equivalent algebra
        (subtract algebra value centre)
        (add algebra leading remainder)

open PositiveTaylorTailCertificate public

positiveTailAbsoluteBound :
  ∀ {Scalar}
    {algebra : OrderedAbsoluteAlgebra Scalar}
    (certificate : PositiveTaylorTailCertificate algebra) →
  LessEqual algebra
    (absolute algebra
      (subtract algebra (value certificate) (centre certificate)))
    (add algebra (leading certificate) (tailBudget certificate))
positiveTailAbsoluteBound {algebra = algebra} certificate =
  lessEqualResp algebra
    (equivalentSym algebra
      (equivalentTrans algebra
        (absoluteCong algebra
          (positiveDifferenceMeaning certificate))
        (absoluteOfNonnegative algebra
          (addNonnegative algebra
            (leadingNonnegative certificate)
            (remainderNonnegative certificate)))))
    (equivalentRefl algebra
      (add algebra (leading certificate) (tailBudget certificate)))
    (addMonotone algebra
      (reflexive algebra (leading certificate))
      (remainderBelowTailBudget certificate))

alternatingTaylorEnvelopeLevel : ProofLevel
alternatingTaylorEnvelopeLevel = machineChecked

positiveTaylorTailEnvelopeLevel : ProofLevel
positiveTaylorTailEnvelopeLevel = machineChecked
