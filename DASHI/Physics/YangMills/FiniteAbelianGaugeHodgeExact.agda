module DASHI.Physics.YangMills.FiniteAbelianGaugeHodgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jozef Dodziuk,
-- "Finite-Difference Approach to the Hodge Theory of Harmonic Forms",
-- American Journal of Mathematics 98 (1976), 79--104.
-- DOI: 10.2307/2373615.
--
-- Michael Creutz,
-- "Quarks, Gluons and Lattices", Cambridge University Press, 1983.
-- No DOI is asserted for the cited book edition.
--
-- DASHI CONTRIBUTION
--
-- Instantiate the exact/harmonic/coexact rational Hodge split as a finite
-- abelian gauge model.  Gauge transformations add only an exact component,
-- curvature reads the coexact coordinate, and curvature is therefore exactly
-- gauge invariant.  On the slice with exact and harmonic coordinates zero,
-- the Hodge Laplacian is the identity and its quadratic form equals the norm,
-- giving a finite-volume coercivity constant lambda=1.
--
-- This is an exact finite abelian theorem.  Nonabelian commutators, weighted
-- lattice geometry, reflection positivity, cluster decomposition, volume
-- uniformity and continuum mass-gap transfer remain explicit boundaries.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Unit using (⊤)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Mathematics.LinearAlgebra.RationalThreeWayHodgeDecompositionExact as Hodge

GaugeParameter : Set
GaugeParameter = ℚ

GaugeField : Set
GaugeField = Hodge.HodgeTriple

Curvature : Set
Curvature = ℚ

finiteD0 : GaugeParameter → GaugeField
finiteD0 parameter = Hodge.hodgeTriple parameter 0ℚ 0ℚ

finiteD1 : GaugeField → Curvature
finiteD1 = Hodge.coexactCoordinate

finiteDSquaredZero : ∀ parameter → finiteD1 (finiteD0 parameter) ≡ 0ℚ
finiteDSquaredZero parameter = refl

gaugeTransform : GaugeField → GaugeParameter → GaugeField
gaugeTransform field parameter =
  Hodge.addTriple field (finiteD0 parameter)

curvature : GaugeField → Curvature
curvature = finiteD1

curvatureGaugeInvariant : ∀ field parameter →
  curvature (gaugeTransform field parameter) ≡ curvature field
curvatureGaugeInvariant (Hodge.hodgeTriple exact harmonic coexact) parameter =
  solve (coexact ∷ [])

exactProjectionAfterGauge : ∀ field parameter →
  Hodge.exactProjection (gaugeTransform field parameter)
  ≡ Hodge.addTriple
      (Hodge.exactProjection field)
      (finiteD0 parameter)
exactProjectionAfterGauge
    (Hodge.hodgeTriple exact harmonic coexact) parameter =
  Hodge.tripleExtensionality
    (solve (exact ∷ parameter ∷ [])) refl refl

harmonicProjectionGaugeInvariant : ∀ field parameter →
  Hodge.harmonicProjection (gaugeTransform field parameter)
  ≡ Hodge.harmonicProjection field
harmonicProjectionGaugeInvariant
    (Hodge.hodgeTriple exact harmonic coexact) parameter = refl

coexactProjectionGaugeInvariant : ∀ field parameter →
  Hodge.coexactProjection (gaugeTransform field parameter)
  ≡ Hodge.coexactProjection field
coexactProjectionGaugeInvariant
    (Hodge.hodgeTriple exact harmonic coexact) parameter = refl

curvatureKillsExact : ∀ field →
  curvature (Hodge.exactProjection field) ≡ 0ℚ
curvatureKillsExact (Hodge.hodgeTriple exact harmonic coexact) = refl

curvatureKillsHarmonic : ∀ field →
  curvature (Hodge.harmonicProjection field) ≡ 0ℚ
curvatureKillsHarmonic (Hodge.hodgeTriple exact harmonic coexact) = refl

curvatureDependsOnlyOnCoexact : ∀ field →
  curvature field ≡ curvature (Hodge.coexactProjection field)
curvatureDependsOnlyOnCoexact (Hodge.hodgeTriple exact harmonic coexact) = refl

record MassivePhysicalSlice (field : GaugeField) : Set where
  constructor massivePhysicalSlice
  field
    exactCoordinateZero : Hodge.exactCoordinate field ≡ 0ℚ
    harmonicCoordinateZero : Hodge.harmonicCoordinate field ≡ 0ℚ

open MassivePhysicalSlice public

gaugeFixedHessian : GaugeField → GaugeField
gaugeFixedHessian = Hodge.hodgeLaplacian

massiveSliceHessianIsIdentity : ∀ field →
  MassivePhysicalSlice field →
  gaugeFixedHessian field ≡ field
massiveSliceHessianIsIdentity
    (Hodge.hodgeTriple exact harmonic coexact)
    (massivePhysicalSlice exactZero harmonicZero)
    with exactZero | harmonicZero
... | refl | refl =
  Hodge.tripleExtensionality (solve []) refl (solve (coexact ∷ []))

massiveSliceQuadraticFormEqualsNorm : ∀ field →
  MassivePhysicalSlice field →
  Hodge.innerTriple (gaugeFixedHessian field) field
  ≡ Hodge.innerTriple field field
massiveSliceQuadraticFormEqualsNorm field slice
    with massiveSliceHessianIsIdentity field slice
... | refl = refl

finiteVolumeCoercivityAtOne : ∀ field →
  MassivePhysicalSlice field →
  Hodge.innerTriple (gaugeFixedHessian field) field
  ≡ 1ℚ * Hodge.innerTriple field field
finiteVolumeCoercivityAtOne field slice =
  transitivity
    (massiveSliceQuadraticFormEqualsNorm field slice)
    (solve (Hodge.innerTriple field field ∷ []))
  where
    transitivity : ∀ {A : Set} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
    transitivity refl second = second

coexactUnitField : GaugeField
coexactUnitField = Hodge.hodgeTriple 0ℚ 0ℚ 1ℚ

coexactUnitIsMassivePhysical : MassivePhysicalSlice coexactUnitField
coexactUnitIsMassivePhysical = massivePhysicalSlice refl refl

coexactUnitCurvature : curvature coexactUnitField ≡ 1ℚ
coexactUnitCurvature = refl

coexactUnitGapWitness :
  Hodge.innerTriple (gaugeFixedHessian coexactUnitField) coexactUnitField
  ≡ Hodge.innerTriple coexactUnitField coexactUnitField
coexactUnitGapWitness =
  massiveSliceQuadraticFormEqualsNorm
    coexactUnitField coexactUnitIsMassivePhysical

record NonabelianGaugeHodgeBoundary : Set₁ where
  field
    LieAlgebra : Set
    bracket : LieAlgebra → LieAlgebra → LieAlgebra
    covariantDerivative : Set
    curvatureIncludesBracket : Set
    infinitesimalGaugeCovariance : Set
    weightedAdjointness : Set
    gaugeZeroModeQuotient : Set
    finiteVolumePositiveHessian : Set
    volumeUniformLowerBound : Set
    reflectionPositivityOS2 : Set
    clusterDecompositionOS4 : Set
    largeFieldKPControl : Set
    continuumMassGapTransfer : Set

record FiniteAbelianGaugeCertificate : Set where
  field
    dSquaredZero : ∀ parameter → finiteD1 (finiteD0 parameter) ≡ 0ℚ
    gaugeInvariantCurvature : ∀ field parameter →
      curvature (gaugeTransform field parameter) ≡ curvature field
    exactCurvatureZero : ∀ field →
      curvature (Hodge.exactProjection field) ≡ 0ℚ
    finiteCoercivity : ∀ field →
      MassivePhysicalSlice field →
      Hodge.innerTriple (gaugeFixedHessian field) field
      ≡ 1ℚ * Hodge.innerTriple field field

canonicalFiniteAbelianGaugeCertificate : FiniteAbelianGaugeCertificate
canonicalFiniteAbelianGaugeCertificate = record
  { dSquaredZero = finiteDSquaredZero
  ; gaugeInvariantCurvature = curvatureGaugeInvariant
  ; exactCurvatureZero = curvatureKillsExact
  ; finiteCoercivity = finiteVolumeCoercivityAtOne
  }
