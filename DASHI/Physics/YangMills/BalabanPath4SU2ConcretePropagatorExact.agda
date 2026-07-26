module DASHI.Physics.YangMills.BalabanPath4SU2ConcretePropagatorExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 1ℚ; _+_; _*_; _≤_; _<_)
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
  ; Green.Positive = λ value → 1ℚ * 0ℚ < value
  ; Green.positiveCoercivity = configuredPathCoercivityConstantPositive
  ; Green.energyDefinition = λ tangent → refl
  ; Green.Coercive = ConfiguredGaugeFixedCoercive
  ; Green.coercive = configuredGaugeFixedMatrixPositive
  }
  where
  open import Data.Rational using (0ℚ)

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

open ConfiguredPropagatorAuthority public

configuredPropagator :
  ConfiguredPropagatorAuthority →
  PhysicalSU2Tangent4 → PhysicalSU2Tangent4
configuredPropagator authority = Green.inverse (finiteAuthority authority)

configuredGaugeFixedMatrixInvertible :
  ConfiguredPropagatorAuthority → Set
configuredGaugeFixedMatrixInvertible authority =
  (∀ tangent →
    configuredPropagator authority (configuredGaugeFixedMatrix tangent) ≡ tangent)
  ×
  (∀ tangent →
    configuredGaugeFixedMatrix (configuredPropagator authority tangent) ≡ tangent)
  where
  infixr 4 _×_
  record _×_ (A B : Set) : Set where
    constructor _,_
    field first : A
          second : B

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

configuredGaugeFixedMatrixInvertibleWitness :
  (authority : ConfiguredPropagatorAuthority) →
  configuredGaugeFixedMatrixInvertible authority
configuredGaugeFixedMatrixInvertibleWitness authority =
  configuredPropagatorLeftInverse authority ,
  configuredPropagatorRightInverse authority
  where
  infixr 4 _×_
  record _×_ (A B : Set) : Set where
    constructor _,_
    field first : A
          second : B

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
    (Green.inverseNormBound (finiteAuthority authority) source)

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
