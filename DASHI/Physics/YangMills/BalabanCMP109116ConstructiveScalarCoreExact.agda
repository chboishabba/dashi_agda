{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109116ConstructiveScalarCoreExact where

------------------------------------------------------------------------
-- CONSTRUCTIVE SOURCE-FIRST CORE FOR CMP109 / CMP116.
--
-- Unlike RealAnalysisAxioms, this module contains NO postulates and uses
-- NO abstract postulated real carrier. It is polymorphic in Scalar and can
-- be instantiated on the already constructed Bishop setoid reals.
--
-- SAME potential and SAME second derivative are identified by construction.
-- The physical proof that Bałaban's Wilson/FP/Haar effective potential
-- inhabits this source, the analytic derivative, and Bishop equivalence
-- are not manufactured here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

record OnePhysicalDifferentiatedAction
    (Scalar Background Tangent : Set) : Set₁ where
  field
    effectivePotential : Background → Scalar
    secondVariation :
      (Background → Scalar) →
      Background → Tangent → Tangent → Scalar

  cmp109Polarization :
    Background → Tangent → Tangent → Scalar
  cmp109Polarization = secondVariation effectivePotential

  cmp116PhysicalMarkedHessian :
    Background → Tangent → Tangent → Scalar
  cmp116PhysicalMarkedHessian = secondVariation effectivePotential

  cmp109EqualsCMP116OnSameSource :
    ∀ background u v →
    cmp109Polarization background u v
      ≡ cmp116PhysicalMarkedHessian background u v
  cmp109EqualsCMP116OnSameSource background u v = refl

open OnePhysicalDifferentiatedAction public

record SameSourceHeatDoobAlgebra
    {Scalar Background Tangent : Set}
    (action : OnePhysicalDifferentiatedAction Scalar Background Tangent)
    (Time : Set) : Set₁ where
  field
    subtract multiply : Scalar → Scalar → Scalar
    firstVariation :
      (Background → Scalar) →
      Background → Tangent → Scalar
    expectation :
      Time → Background → (Background → Scalar) → Scalar

  covariance :
    Time → Background →
    (Background → Scalar) → (Background → Scalar) → Scalar
  covariance t x f g =
    subtract
      (expectation t x (λ y → multiply (f y) (g y)))
      (multiply (expectation t x f) (expectation t x g))

  staticMinusCovariance :
    Time → Background → Tangent → Tangent → Scalar
  staticMinusCovariance t x u v =
    subtract
      (expectation t x
        (λ y → cmp116PhysicalMarkedHessian action y u v))
      (covariance t x
        (λ y → firstVariation (effectivePotential action) y u)
        (λ y → firstVariation (effectivePotential action) y v))

  covarianceIsDefinition :
    ∀ t x f g →
    covariance t x f g
      ≡
      subtract
        (expectation t x (λ y → multiply (f y) (g y)))
        (multiply (expectation t x f) (expectation t x g))
  covarianceIsDefinition t x f g = refl

  heatHessianIsSamePotentialExpression :
    ∀ t x u v →
    staticMinusCovariance t x u v
      ≡
      subtract
        (expectation t x
          (λ y → secondVariation action (effectivePotential action) y u v))
        (covariance t x
          (λ y → firstVariation (effectivePotential action) y u)
          (λ y → firstVariation (effectivePotential action) y v))
  heatHessianIsSamePotentialExpression t x u v = refl

open SameSourceHeatDoobAlgebra public

-- An actual compact-group heat flow must be proved to have the physical
-- static-minus-covariance Hessian. Merely defining this expression does not
-- prove the heat differentiation or positivity theorem.
