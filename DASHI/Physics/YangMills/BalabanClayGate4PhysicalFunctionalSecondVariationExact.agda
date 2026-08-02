module DASHI.Physics.YangMills.BalabanClayGate4PhysicalFunctionalSecondVariationExact where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literal second variation of the selected physical functional.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- The selected action is represented as a sum of six owned atoms: the
-- reference quadratic action and the five audited perturbation channels.
-- Hessian additivity then derives the operator split; it is not accepted as an
-- unrelated equality at the final coercivity boundary.
------------------------------------------------------------------------

record AdditiveSecondVariationCalculus
    (Functional Operator : Set) : Set₁ where
  field
    addFunctional : Functional → Functional → Functional
    addOperator : Operator → Operator → Operator
    hessian : Functional → Operator

    hessianAdd : ∀ left right →
      hessian (addFunctional left right)
      ≡ addOperator (hessian left) (hessian right)

open AdditiveSecondVariationCalculus public

record PhysicalFunctionalAtoms
    (Functional Operator : Set)
    (calculus : AdditiveSecondVariationCalculus Functional Operator) : Set₁ where
  field
    referenceFunctional curvatureFunctional transportFunctional
      chartFunctional gaugeFunctional constraintFunctional : Functional

    referenceHessian curvatureHessian transportHessian
      chartHessian gaugeHessian constraintHessian : Operator

    referenceHessianMeaning :
      hessian calculus referenceFunctional ≡ referenceHessian
    curvatureHessianMeaning :
      hessian calculus curvatureFunctional ≡ curvatureHessian
    transportHessianMeaning :
      hessian calculus transportFunctional ≡ transportHessian
    chartHessianMeaning :
      hessian calculus chartFunctional ≡ chartHessian
    gaugeHessianMeaning :
      hessian calculus gaugeFunctional ≡ gaugeHessian
    constraintHessianMeaning :
      hessian calculus constraintFunctional ≡ constraintHessian

open PhysicalFunctionalAtoms public

selectedPhysicalFunctional :
  ∀ {Functional Operator calculus} →
  PhysicalFunctionalAtoms Functional Operator calculus → Functional
selectedPhysicalFunctional {calculus = calculus} atoms =
  addFunctional calculus (referenceFunctional atoms)
    (addFunctional calculus (curvatureFunctional atoms)
      (addFunctional calculus (transportFunctional atoms)
        (addFunctional calculus (chartFunctional atoms)
          (addFunctional calculus
            (gaugeFunctional atoms) (constraintFunctional atoms)))))

selectedPhysicalHessian :
  ∀ {Functional Operator calculus} →
  PhysicalFunctionalAtoms Functional Operator calculus → Operator
selectedPhysicalHessian {calculus = calculus} atoms =
  addOperator calculus (referenceHessian atoms)
    (addOperator calculus (curvatureHessian atoms)
      (addOperator calculus (transportHessian atoms)
        (addOperator calculus (chartHessian atoms)
          (addOperator calculus
            (gaugeHessian atoms) (constraintHessian atoms)))))

selectedFunctionalSecondVariationExact :
  ∀ {Functional Operator}
    {calculus : AdditiveSecondVariationCalculus Functional Operator}
    (atoms : PhysicalFunctionalAtoms Functional Operator calculus) →
  hessian calculus (selectedPhysicalFunctional atoms)
  ≡ selectedPhysicalHessian atoms
selectedFunctionalSecondVariationExact {calculus = calculus} atoms
  rewrite hessianAdd calculus
      (referenceFunctional atoms)
      (addFunctional calculus (curvatureFunctional atoms)
        (addFunctional calculus (transportFunctional atoms)
          (addFunctional calculus (chartFunctional atoms)
            (addFunctional calculus
              (gaugeFunctional atoms) (constraintFunctional atoms)))))
        | hessianAdd calculus
            (curvatureFunctional atoms)
            (addFunctional calculus (transportFunctional atoms)
              (addFunctional calculus (chartFunctional atoms)
                (addFunctional calculus
                  (gaugeFunctional atoms) (constraintFunctional atoms))))
        | hessianAdd calculus
            (transportFunctional atoms)
            (addFunctional calculus (chartFunctional atoms)
              (addFunctional calculus
                (gaugeFunctional atoms) (constraintFunctional atoms)))
        | hessianAdd calculus
            (chartFunctional atoms)
            (addFunctional calculus
              (gaugeFunctional atoms) (constraintFunctional atoms))
        | hessianAdd calculus
            (gaugeFunctional atoms) (constraintFunctional atoms)
        | referenceHessianMeaning atoms
        | curvatureHessianMeaning atoms
        | transportHessianMeaning atoms
        | chartHessianMeaning atoms
        | gaugeHessianMeaning atoms
        | constraintHessianMeaning atoms = refl

record PhysicalFunctionalFactorizationMeaning
    (Functional Operator : Set)
    (calculus : AdditiveSecondVariationCalculus Functional Operator)
    (atoms : PhysicalFunctionalAtoms Functional Operator calculus) : Set₁ where
  field
    CurvatureFactorization TransportFactorization ChartFactorization
      GaugeFactorization ConstraintFactorization : Set

    curvatureFactorization : CurvatureFactorization
    transportFactorization : TransportFactorization
    chartFactorization : ChartFactorization
    gaugeFactorization : GaugeFactorization
    constraintFactorization : ConstraintFactorization

open PhysicalFunctionalFactorizationMeaning public

physicalFunctionalSecondVariationLevel : ProofLevel
physicalFunctionalSecondVariationLevel = machineChecked

physicalFunctionalFiveChannelOwnershipLevel : ProofLevel
physicalFunctionalFiveChannelOwnershipLevel = machineChecked

physicalWilsonTransportChartDerivativeInputsLevel : ProofLevel
physicalWilsonTransportChartDerivativeInputsLevel = conditional

physicalGaugeConstraintDerivativeInputsLevel : ProofLevel
physicalGaugeConstraintDerivativeInputsLevel = conditional
