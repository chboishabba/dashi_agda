module DASHI.Physics.Closure.NSTriadKNCauchyResolvedPhysicalSnapshotRound480Exact where

------------------------------------------------------------------------
-- ROUND480 / ACTUAL PHYSICAL SNAPSHOT IS WEAKER THAN A UNIFORM OPERATOR BOUND
--
-- R471/R478 expose a useful uniform producer:
--
--   forall c, Q_resolved(c) <= A * M(c).
--
-- But R472's literal downstream payment does not consume every coefficient
-- vector.  A PhysicalFixedOutputGramSnapshot carries one ACTUAL coefficient
-- vector together with exact same-object equalities to the R432 signed cross and
-- fibre budget.  Therefore the least-privilege physical payment is only
--
--   Q_resolved(c_physical) <= A * M(c_physical).
--
-- A uniform R478 bound certainly produces this payment, but it is not mandatory.
-- This owner prevents proof search from quantifying over unused coefficient
-- vectors unless that stronger theorem is genuinely the cheapest producer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNFixedOutputSignedCrossAggregationRound432Exact as R432
import DASHI.Physics.Closure.NSTriadKNPhysicalGramOperatorPaymentRound472Exact as R472
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedGramOperatorRound477Exact as R477
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedDirectConsumerRound478Exact as R478

record PhysicalResolvedSnapshotPayment
    {Index : Set}
    (family : R477.CauchyResolvedCellFamily Index)
    (A : ℚ) : Set where
  constructor physical-resolved-snapshot-payment
  field
    snapshot :
      R472.PhysicalFixedOutputGramSnapshot
        (Index → ℚ)
        (R477.resolvedQuadratic family)
        (R477.coefficientMass family)
        A

    selectedResolvedBound :
      R477.resolvedQuadratic family (R472.coeff snapshot)
      ≤ A * R477.coefficientMass family (R472.coeff snapshot)

open PhysicalResolvedSnapshotPayment public

physicalResolvedSnapshotPaysR432 :
  ∀ {Index}
    {family : R477.CauchyResolvedCellFamily Index}
    {A : ℚ} →
  PhysicalResolvedSnapshotPayment family A →
  R432.FixedOutputSignedCrossPayment
physicalResolvedSnapshotPaysR432 payment =
  let
    S = snapshot payment
    selected = selectedResolvedBound payment
  in
  record
    { R432.signedCross = R472.signedCross S
    ; R432.fibreBudget = R472.fibreBudget S
    ; R432.signedCrossBound =
        subst
          (λ lower → lower ≤ R472.fibreBudget S)
          (sym (R472.signedCrossMeaning S))
          (subst
            ((R477.resolvedQuadratic _ (R472.coeff S)) ≤_)
            (sym (R472.fibreBudgetMeaning S))
            selected)
    }

uniformDirectBoundPaysPhysicalSnapshot :
  ∀ {Index}
    {family : R477.CauchyResolvedCellFamily Index}
    {A : ℚ} →
  R478.DirectResolvedPhysicalGramBound family A →
  (S : R472.PhysicalFixedOutputGramSnapshot
    (Index → ℚ)
    (R477.resolvedQuadratic family)
    (R477.coefficientMass family)
    A) →
  PhysicalResolvedSnapshotPayment family A
uniformDirectBoundPaysPhysicalSnapshot bound S =
  physical-resolved-snapshot-payment
    S
    (R478.R477.R471.quadraticBound bound (R472.coeff S))

------------------------------------------------------------------------
-- Trust / search boundary.
------------------------------------------------------------------------

round480ActualPhysicalSnapshotIsPreferredConsumer : Bool
round480ActualPhysicalSnapshotIsPreferredConsumer = true

round480UniformAllCoefficientBoundIsSufficient : Bool
round480UniformAllCoefficientBoundIsSufficient = true

round480UniformAllCoefficientBoundIsMandatory : Bool
round480UniformAllCoefficientBoundIsMandatory = false

round480SelectedSnapshotCompilesDirectlyToR432 : Bool
round480SelectedSnapshotCompilesDirectlyToR432 = true

round480PhysicalSnapshotSameObjectWeldClosed : Bool
round480PhysicalSnapshotSameObjectWeldClosed = false

round480PhysicalSelectedResolvedBoundClosed : Bool
round480PhysicalSelectedResolvedBoundClosed = false

round480PackageAClosed : Bool
round480PackageAClosed = false

round480ClayPromotion : Bool
round480ClayPromotion = false

round480UniformAllCoefficientBoundIsMandatoryIsFalse :
  round480UniformAllCoefficientBoundIsMandatory ≡ false
round480UniformAllCoefficientBoundIsMandatoryIsFalse = refl

round480PhysicalSnapshotSameObjectWeldClosedIsFalse :
  round480PhysicalSnapshotSameObjectWeldClosed ≡ false
round480PhysicalSnapshotSameObjectWeldClosedIsFalse = refl

round480PhysicalSelectedResolvedBoundClosedIsFalse :
  round480PhysicalSelectedResolvedBoundClosed ≡ false
round480PhysicalSelectedResolvedBoundClosedIsFalse = refl
