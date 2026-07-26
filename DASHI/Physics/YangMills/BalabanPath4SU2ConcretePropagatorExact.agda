module DASHI.Physics.YangMills.BalabanPath4SU2ConcretePropagatorExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanConfiguredRGSide4Certificate
  using
    ( configuredPathCoercivityConstant
    ; configuredPathCoercivityConstantPositive
    )
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
  using (PhysicalSU2Tangent4; physicalUnweightedNormSq)
open import DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact
  using (physicalTangentInner)
open import DASHI.Physics.YangMills.BalabanSU2GaugeFixedHessian
  using (gaugeFixedHessian)
open import DASHI.Physics.YangMills.BalabanSU2GaugeFixedHessianQuadraticExact
  using
    ( hessianData
    ; gaugeFixedHessianQuadraticForm
    )
open import DASHI.Physics.YangMills.BalabanPath4SU2ConcreteCoarseBlockExact
  using
    ( concreteGaugeFixedHessianData
    ; CoarseAverageZero
    ; fineFluctuationCoercivity
    )
import DASHI.Physics.YangMills.BalabanFiniteCoerciveGreen as Green

------------------------------------------------------------------------
-- Concrete finite operator and quadratic form.
------------------------------------------------------------------------

configuredGaugeFixedMatrix : PhysicalSU2Tangent4 → PhysicalSU2Tangent4
configuredGaugeFixedMatrix =
  gaugeFixedHessian (hessianData concreteGaugeFixedHessianData)

configuredGaugeFixedEnergy : PhysicalSU2Tangent4 → ℚ
configuredGaugeFixedEnergy tangent =
  physicalTangentInner tangent (configuredGaugeFixedMatrix tangent)

configuredGaugeFixedEnergyMatchesQuadratic : ∀ tangent →
  configuredGaugeFixedEnergy tangent
  ≡ gaugeFixedHessianQuadraticForm concreteGaugeFixedHessianData tangent
configuredGaugeFixedEnergyMatchesQuadratic tangent = refl

ConfiguredGaugeFixedCoercive : Set
ConfiguredGaugeFixedCoercive =
  ∀ tangent → CoarseAverageZero tangent →
  configuredPathCoercivityConstant * physicalUnweightedNormSq tangent
  ≤ configuredGaugeFixedEnergy tangent

configuredGaugeFixedMatrixPositive : ConfiguredGaugeFixedCoercive
configuredGaugeFixedMatrixPositive tangent averageZero =
  fineFluctuationCoercivity tangent averageZero

configuredGaugeFixedOperatorData :
  Green.CoerciveFiniteOperator PhysicalSU2Tangent4 ℚ ℚ
configuredGaugeFixedOperatorData = record
  { Green.operator = configuredGaugeFixedMatrix
  ; Green.inner = physicalTangentInner
  ; Green.vectorNorm = physicalUnweightedNormSq
  ; Green.energy = configuredGaugeFixedEnergy
  ; Green.coercivityConstant = configuredPathCoercivityConstant
  ; Green.LessEqual = _≤_
  ; Green.Positive = λ value → 0ℚ < value
  ; Green.positiveCoercivity = configuredPathCoercivityConstantPositive
  ; Green.energyDefinition = λ tangent → refl
  ; Green.Coercive = ConfiguredGaugeFixedCoercive
  ; Green.coercive = configuredGaugeFixedMatrixPositive
  }

------------------------------------------------------------------------
-- Finite-dimensional inversion authority.
--
-- The carrier and coercive operator are now concrete.  The only imported theorem
-- is the standard finite-dimensional result converting positive coercivity into
-- a two-sided inverse with reciprocal norm bound; no Yang--Mills estimate is
-- hidden in this authority.
------------------------------------------------------------------------

sixteenℚ : ℚ
sixteenℚ =
  1ℚ + (1ℚ + (1ℚ + (1ℚ + (1ℚ + (1ℚ + (1ℚ + (1ℚ +
  (1ℚ + (1ℚ + (1ℚ + (1ℚ + (1ℚ + (1ℚ + (1ℚ + 1ℚ))))))))))))))

record ConfiguredPropagatorAuthority : Set₁ where
  field
    finiteAuthority :
      Green.FiniteCoerciveInverseAuthority configuredGaugeFixedOperatorData
    reciprocalIsSixteen :
      Green.reciprocalCoercivity finiteAuthority ≡ sixteenℚ
    multiplyBoundExact : ∀ left right →
      Green.multiplyBound finiteAuthority left right ≡ left * right

open ConfiguredPropagatorAuthority public

configuredPropagator :
  ConfiguredPropagatorAuthority →
  PhysicalSU2Tangent4 → PhysicalSU2Tangent4
configuredPropagator authority = Green.inverse (finiteAuthority authority)

record ConfiguredGaugeFixedMatrixInvertible
    (authority : ConfiguredPropagatorAuthority) : Set where
  field
    inverseLeftExact : ∀ tangent →
      configuredPropagator authority (configuredGaugeFixedMatrix tangent) ≡ tangent
    inverseRightExact : ∀ tangent →
      configuredGaugeFixedMatrix (configuredPropagator authority tangent) ≡ tangent

open ConfiguredGaugeFixedMatrixInvertible public

configuredPropagatorLeftInverse :
  (authority : ConfiguredPropagatorAuthority) → ∀ tangent →
  configuredPropagator authority (configuredGaugeFixedMatrix tangent) ≡ tangent
configuredPropagatorLeftInverse authority =
  Green.inverseLeft (finiteAuthority authority)

configuredPropagatorRightInverse :
  (authority : ConfiguredPropagatorAuthority) → ∀ tangent →
  configuredGaugeFixedMatrix (configuredPropagator authority tangent) ≡ tangent
configuredPropagatorRightInverse authority =
  Green.inverseRight (finiteAuthority authority)

configuredGaugeFixedMatrixInvertible :
  (authority : ConfiguredPropagatorAuthority) →
  ConfiguredGaugeFixedMatrixInvertible authority
configuredGaugeFixedMatrixInvertible authority = record
  { inverseLeftExact = configuredPropagatorLeftInverse authority
  ; inverseRightExact = configuredPropagatorRightInverse authority
  }

configuredPropagatorNormBound :
  (authority : ConfiguredPropagatorAuthority) → ∀ source →
  physicalUnweightedNormSq (configuredPropagator authority source)
  ≤ sixteenℚ * physicalUnweightedNormSq source
configuredPropagatorNormBound authority source =
  subst
    (λ coefficient →
      physicalUnweightedNormSq (configuredPropagator authority source)
      ≤ coefficient * physicalUnweightedNormSq source)
    (reciprocalIsSixteen authority)
    (subst
      (λ right →
        physicalUnweightedNormSq (configuredPropagator authority source) ≤ right)
      (multiplyBoundExact authority
        (Green.reciprocalCoercivity (finiteAuthority authority))
        (physicalUnweightedNormSq source))
      (Green.inverseNormBound (finiteAuthority authority) source))

configuredGaugeFixedMatrixLevel : ProofLevel
configuredGaugeFixedMatrixLevel = machineChecked

configuredGaugeFixedMatrixPositiveLevel : ProofLevel
configuredGaugeFixedMatrixPositiveLevel = machineChecked

configuredPropagatorInverseAssemblyLevel : ProofLevel
configuredPropagatorInverseAssemblyLevel = machineChecked

configuredPropagatorNormAssemblyLevel : ProofLevel
configuredPropagatorNormAssemblyLevel = machineChecked

configuredFiniteCoerciveInverseAuthorityLevel : ProofLevel
configuredFiniteCoerciveInverseAuthorityLevel = standardImported
