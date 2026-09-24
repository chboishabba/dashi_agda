{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTLocalizedRepulsiveSourceCriterionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 1ℚ; _*_; -[1+_])
open import Agda.Builtin.Nat using (zero; suc)

import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Cut
import DASHI.Physics.Foundations.GRQFTNegativeActiveStressRepulsionRouteExact as Active
import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as Signed

------------------------------------------------------------------------
-- LOCALIZED ACTIVE-SOURCE ADAPTER
--
-- This is the explicit bridge needed to move from cosmological/comoving
-- defocusing to a finite source seen by an external test mass.
--
-- In a stationary weak-field spherical regime, the standard active-mass
-- source is pressure-sensitive.  We do not claim that the finite GRQFT fixture
-- has already proved the full Tolman/Komar theorem.  Instead we expose the
-- exact adapter assumptions and compile their consequence.
------------------------------------------------------------------------

record LocalizedWeakFieldActiveMassAssumptions : Set where
  constructor localized-weak-field-active-mass-assumptions
  field
    stationarySource : Bool
    weakFieldExterior : Bool
    sphericalExteriorComparison : Bool
    localOrthonormalRestFrame : Bool
    positiveVolumeWeight : Bool
    pressureSensitiveActiveSourceLaw : Bool

open LocalizedWeakFieldActiveMassAssumptions public

canonicalLocalizedWeakFieldAssumptions :
  LocalizedWeakFieldActiveMassAssumptions
canonicalLocalizedWeakFieldAssumptions =
  localized-weak-field-active-mass-assumptions
    true true true true true true

------------------------------------------------------------------------
-- ONE-CELL EXACT LOCALIZED FIXTURE
--
-- Unit positive volume weight is enough to make the existing active-stress
-- density into an integrated active-source diagnostic.
------------------------------------------------------------------------

unitVolumeWeight : ℚ
unitVolumeWeight = 1ℚ

localizedActiveMass :
  Cut.RationalTensor4 → ℚ
localizedActiveMass tensor =
  unitVolumeWeight * Active.activeStressSum tensor

finiteGRLocalizedActiveMassIsNegativeTwo :
  localizedActiveMass Cut.finiteGRStressRational
    ≡ -[1+ suc zero ]
finiteGRLocalizedActiveMassIsNegativeTwo = refl

data ActiveMassSign : Set where
  positiveActiveMass : ActiveMassSign
  zeroActiveMass : ActiveMassSign
  negativeActiveMass : ActiveMassSign

finiteGRLocalizedActiveMassSign : ActiveMassSign
finiteGRLocalizedActiveMassSign = negativeActiveMass

------------------------------------------------------------------------
-- EXTERIOR RESPONSE COMPILER
--
-- Under positive gravitational coupling, negative active mass reverses the
-- radial exterior response orientation.
------------------------------------------------------------------------

data ExteriorRadialResponse : Set where
  inwardExteriorAcceleration : ExteriorRadialResponse
  zeroExteriorAcceleration : ExteriorRadialResponse
  outwardExteriorAcceleration : ExteriorRadialResponse

exteriorResponse :
  Signed.CouplingSign → ActiveMassSign → ExteriorRadialResponse
exteriorResponse Signed.zeroCoupling mass = zeroExteriorAcceleration
exteriorResponse coupling zeroActiveMass = zeroExteriorAcceleration
exteriorResponse Signed.positiveCoupling positiveActiveMass =
  inwardExteriorAcceleration
exteriorResponse Signed.positiveCoupling negativeActiveMass =
  outwardExteriorAcceleration
exteriorResponse Signed.negativeCoupling positiveActiveMass =
  outwardExteriorAcceleration
exteriorResponse Signed.negativeCoupling negativeActiveMass =
  inwardExteriorAcceleration

positiveGCouplingNegativeActiveMassRepels :
  exteriorResponse Signed.positiveCoupling negativeActiveMass
    ≡ outwardExteriorAcceleration
positiveGCouplingNegativeActiveMassRepels = refl

finiteGRLocalizedFixtureRepelsExternally :
  exteriorResponse Signed.positiveCoupling finiteGRLocalizedActiveMassSign
    ≡ outwardExteriorAcceleration
finiteGRLocalizedFixtureRepelsExternally = refl

------------------------------------------------------------------------
-- LOCALIZED REPULSIVE-SOURCE WITNESS
------------------------------------------------------------------------

record LocalizedPositiveGRepulsiveSourceWitness : Set where
  constructor localized-positive-g-repulsive-source-witness
  field
    assumptions : LocalizedWeakFieldActiveMassAssumptions

    couplingSign : Signed.CouplingSign
    couplingIsPositive :
      couplingSign ≡ Signed.positiveCoupling

    activeMassValue :
      localizedActiveMass Cut.finiteGRStressRational
        ≡ -[1+ suc zero ]

    activeMassSign : ActiveMassSign
    activeMassIsNegative :
      activeMassSign ≡ negativeActiveMass

    externalResponse : ExteriorRadialResponse
    externalResponseIsOutward :
      externalResponse ≡ outwardExteriorAcceleration

open LocalizedPositiveGRepulsiveSourceWitness public

canonicalLocalizedPositiveGRepulsiveSourceWitness :
  LocalizedPositiveGRepulsiveSourceWitness
canonicalLocalizedPositiveGRepulsiveSourceWitness =
  localized-positive-g-repulsive-source-witness
    canonicalLocalizedWeakFieldAssumptions
    Signed.positiveCoupling
    refl
    finiteGRLocalizedActiveMassIsNegativeTwo
    negativeActiveMass
    refl
    outwardExteriorAcceleration
    refl

------------------------------------------------------------------------
-- BOUNDARY
------------------------------------------------------------------------

record LocalizedRepulsiveSourceBoundary : Set where
  constructor localized-repulsive-source-boundary
  field
    negativeIntegratedActiveStressConstructed : Bool
    positiveGNegativeActiveMassGivesOutwardExteriorResponse : Bool
    externalTestMassRepulsionCriterionConstructed : Bool
    criterionRequiresNegativeG : Bool
    criterionRequiresNegativeInertialMass : Bool
    finiteFixtureProvesTolmanKomarTheorem : Bool
    stationaryWeakFieldSphericalAdapterExplicit : Bool
    fullLocalizedMetricSolutionStillRequiredBeyondCriterion : Bool

canonicalLocalizedRepulsiveSourceBoundary :
  LocalizedRepulsiveSourceBoundary
canonicalLocalizedRepulsiveSourceBoundary =
  localized-repulsive-source-boundary
    true true true false false false true true
