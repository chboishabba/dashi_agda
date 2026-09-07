module DASHI.Physics.Closure.NSTriadKNCauchyResolvedSignedResidualRound479Exact where

------------------------------------------------------------------------
-- ROUND479 / DIRECT CAUCHY-RESOLVED BOUND FROM BASELINE + SIGNED RESIDUAL
--
-- R478 exposes the least-privilege terminal consumer directly:
--
--   Q_resolved(c) <= A * M(c).
--
-- The existing physical Cauchy tranche separately shows that the literal
-- completion splits into a diagonal part plus a signed off-diagonal part, and
-- that the diagonal part admits a cutoff-independent resolvent ceiling once a
-- physical rate floor is available.  R448 identifies the physical off-diagonal
-- scalar with the already-existing signed weighted flux.
--
-- This owner captures the exact algebraic producer shape needed to exploit that
-- fact without strengthening the consumer back to two helicity blocks.  A
-- producer may write
--
--   Q(c) = baseline * M(c) + residual(c)
--
-- and pay only
--
--   residual(c) <= slack * M(c),
--   baseline + slack = A.
--
-- The residual remains SIGNED.  No modulus, absolute Schur row sum, or
-- cardinality factor is introduced.  In the physical Cauchy realization the
-- intended residual is the off-diagonal weighted flux after the paid diagonal
-- contribution has been removed.
--
-- This file does not manufacture the physical residual estimate or the final
-- R447/R448/R451/R456 -> R478 same-object weld.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNCauchyResolvedGramOperatorRound477Exact as R477
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedDirectConsumerRound478Exact as R478

record SignedResidualAllowanceProducer
    {Index : Set}
    (family : R477.CauchyResolvedCellFamily Index)
    (A : ℚ) : Set where
  constructor signed-residual-allowance-producer
  field
    baseline slack : ℚ
    residual : (Index → ℚ) → ℚ

    resolvedDecomposition :
      (coefficient : Index → ℚ) →
      R477.resolvedQuadratic family coefficient
      ≡ baseline * R477.coefficientMass family coefficient
        + residual coefficient

    residualAllowance :
      (coefficient : Index → ℚ) →
      residual coefficient
      ≤ slack * R477.coefficientMass family coefficient

    allowanceFit : baseline + slack ≡ A

open SignedResidualAllowanceProducer public

signedResidualProducerToDirectResolvedBound :
  ∀ {Index}
    {family : R477.CauchyResolvedCellFamily Index}
    {A : ℚ} →
  SignedResidualAllowanceProducer family A →
  R478.DirectResolvedPhysicalGramBound family A
signedResidualProducerToDirectResolvedBound {family = family} {A = A} producer =
  record
    { quadraticBound = bound
    }
  where
  bound :
    (coefficient : _ → ℚ) →
    R477.resolvedQuadratic family coefficient
    ≤ A * R477.coefficientMass family coefficient
  bound coefficient =
    let
      mass = R477.coefficientMass family coefficient
      base = baseline producer
      room = slack producer
      rem = residual producer coefficient

      residualPaid : rem ≤ room * mass
      residualPaid = residualAllowance producer coefficient

      shifted : base * mass + rem ≤ base * mass + room * mass
      shifted = ℚP.+-monoˡ-≤ (base * mass) residualPaid

      regroup : base * mass + room * mass ≡ (base + room) * mass
      regroup = solve (base ∷ room ∷ mass ∷ [])

      endpoint : (base + room) * mass ≡ A * mass
      endpoint = subst (λ selected → selected * mass ≡ A * mass)
        (allowanceFit producer) refl

      paid : base * mass + rem ≤ A * mass
      paid = subst
        (λ upper → base * mass + rem ≤ upper)
        endpoint
        (subst
          (λ upper → base * mass + rem ≤ upper)
          regroup
          shifted)
    in
    subst
      (λ lower → lower ≤ A * mass)
      (sym (resolvedDecomposition producer coefficient))
      paid

------------------------------------------------------------------------
-- Trust / search boundary.
------------------------------------------------------------------------

round479SignedResidualProducerCompilesToDirectConsumer : Bool
round479SignedResidualProducerCompilesToDirectConsumer = true

round479ResidualRemainsSigned : Bool
round479ResidualRemainsSigned = true

round479AbsoluteSchurRequired : Bool
round479AbsoluteSchurRequired = false

round479TwoHelicityBoundsRequired : Bool
round479TwoHelicityBoundsRequired = false

round479PhysicalCauchyDiagonalInfrastructureExists : Bool
round479PhysicalCauchyDiagonalInfrastructureExists = true

round479PhysicalOffDiagonalAlreadyIdentifiedWithSignedFlux : Bool
round479PhysicalOffDiagonalAlreadyIdentifiedWithSignedFlux = true

round479PhysicalSameObjectWeldToR478Closed : Bool
round479PhysicalSameObjectWeldToR478Closed = false

round479PhysicalSignedResidualAllowanceClosed : Bool
round479PhysicalSignedResidualAllowanceClosed = false

round479PackageAClosed : Bool
round479PackageAClosed = false

round479ClayPromotion : Bool
round479ClayPromotion = false

round479AbsoluteSchurRequiredIsFalse : round479AbsoluteSchurRequired ≡ false
round479AbsoluteSchurRequiredIsFalse = refl

round479TwoHelicityBoundsRequiredIsFalse : round479TwoHelicityBoundsRequired ≡ false
round479TwoHelicityBoundsRequiredIsFalse = refl

round479PhysicalSameObjectWeldToR478ClosedIsFalse :
  round479PhysicalSameObjectWeldToR478Closed ≡ false
round479PhysicalSameObjectWeldToR478ClosedIsFalse = refl

round479PhysicalSignedResidualAllowanceClosedIsFalse :
  round479PhysicalSignedResidualAllowanceClosed ≡ false
round479PhysicalSignedResidualAllowanceClosedIsFalse = refl
