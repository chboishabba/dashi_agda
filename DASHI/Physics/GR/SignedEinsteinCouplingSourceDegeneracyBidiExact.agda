module DASHI.Physics.GR.SignedEinsteinCouplingSourceDegeneracyBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as Signed

------------------------------------------------------------------------
-- EINSTEIN SOURCE-SIDE SIGN PRODUCT
--
-- Schematic continuum equation:
--
--   G_mn + Lambda g_mn = kappa T_mn
--   kappa = 8 pi G / c^4
--
-- For positive 8 pi / c^4, sign(kappa) follows sign(G).  This module tracks
-- only the sign product on the RHS.  It does not identify a negative coupling
-- with a negative physical stress-energy source.
------------------------------------------------------------------------

data SourceSign : Set where
  positiveSource : SourceSign
  zeroSource : SourceSign
  negativeSource : SourceSign

data EffectiveSourceOrientation : Set where
  positiveEffectiveSource : EffectiveSourceOrientation
  zeroEffectiveSource : EffectiveSourceOrientation
  negativeEffectiveSource : EffectiveSourceOrientation

effectiveSourceOrientation :
  Signed.CouplingSign → SourceSign → EffectiveSourceOrientation
effectiveSourceOrientation Signed.zeroCoupling source = zeroEffectiveSource
effectiveSourceOrientation coupling zeroSource = zeroEffectiveSource
effectiveSourceOrientation Signed.positiveCoupling positiveSource = positiveEffectiveSource
effectiveSourceOrientation Signed.positiveCoupling negativeSource = negativeEffectiveSource
effectiveSourceOrientation Signed.negativeCoupling positiveSource = negativeEffectiveSource
effectiveSourceOrientation Signed.negativeCoupling negativeSource = positiveEffectiveSource

------------------------------------------------------------------------
-- Exact coarse collision.
------------------------------------------------------------------------

data SignFixture : Set where
  negativeGPositiveSource : SignFixture
  positiveGNegativeSource : SignFixture

fixtureCoupling : SignFixture → Signed.CouplingSign
fixtureCoupling negativeGPositiveSource = Signed.negativeCoupling
fixtureCoupling positiveGNegativeSource = Signed.positiveCoupling

fixtureSource : SignFixture → SourceSign
fixtureSource negativeGPositiveSource = positiveSource
fixtureSource positiveGNegativeSource = negativeSource

coarseEffectiveSource : SignFixture → EffectiveSourceOrientation
coarseEffectiveSource fixture =
  effectiveSourceOrientation (fixtureCoupling fixture) (fixtureSource fixture)

sourceSideSignCollision :
  coarseEffectiveSource negativeGPositiveSource
    ≡ coarseEffectiveSource positiveGNegativeSource
sourceSideSignCollision = refl

------------------------------------------------------------------------
-- Refined observer restores the missing coordinate.
------------------------------------------------------------------------

record RefinedSignedSource : Set where
  constructor refined-signed-source
  field
    coupling : Signed.CouplingSign
    source : SourceSign

refinedObserve : SignFixture → RefinedSignedSource
refinedObserve fixture = refined-signed-source
  (fixtureCoupling fixture)
  (fixtureSource fixture)

refinedFixturesDistinct :
  refinedObserve negativeGPositiveSource
    ≡ refinedObserve positiveGNegativeSource → ⊥
refinedFixturesDistinct ()

------------------------------------------------------------------------
-- Cosmological-constant coordinate is not part of this sign flip.
------------------------------------------------------------------------

record SignedEinsteinSourceBoundary : Set where
  constructor signed-einstein-source-boundary
  field
    signOfKappaTracksSignOfGUnderPositivePrefactor : Bool
    negativeGPositiveSourceMatchesPositiveGNegativeSourceAtCoarseRHSSign : Bool
    coarseRHSSignDeterminesWhetherCouplingOrSourceWasNegative : Bool
    negativeGEqualsNegativeStressEnergy : Bool
    negativeGAutomaticallyFlipsCosmologicalConstant : Bool
    refinedObserverMustRetainCouplingAndSourceSeparately : Bool
    sameRHSSignImpliesSameMatterDynamics : Bool
    sameRHSSignImpliesSamePhysicalTheory : Bool

canonicalSignedEinsteinSourceBoundary : SignedEinsteinSourceBoundary
canonicalSignedEinsteinSourceBoundary =
  signed-einstein-source-boundary true true false false false true false false
