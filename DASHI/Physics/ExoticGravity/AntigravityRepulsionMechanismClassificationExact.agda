module DASHI.Physics.ExoticGravity.AntigravityRepulsionMechanismClassificationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as Signed
import DASHI.Physics.GR.SignedEinsteinCouplingSourceDegeneracyBidiExact as Source
import DASHI.Physics.GR.SignedNewtonianLimitBidiExact as Newton
import DASHI.Physics.ExoticGravity.EngineeredInertialGravitationalBidiExact as Gravity
import DASHI.Physics.ExoticGravity.AntigravityNegativeGCouplingScopeBidiExact as Scope

------------------------------------------------------------------------
-- REPULSION MECHANISM CLASSIFIER
--
-- Inside the repo's signed Einstein/Newton source-product model, a negative
-- effective source orientation is not mysterious: exactly one of the two sign
-- coordinates must be negative.  The coarse product alone cannot tell which.
------------------------------------------------------------------------

data NegativeEffectiveSourceRoute : Set where
  negativeCouplingPositiveSourceRoute : NegativeEffectiveSourceRoute
  positiveCouplingNegativeSourceRoute : NegativeEffectiveSourceRoute

classifyNegativeEffectiveSource :
  (coupling : Signed.CouplingSign) →
  (source : Source.SourceSign) →
  Source.effectiveSourceOrientation coupling source
    ≡ Source.negativeEffectiveSource →
  NegativeEffectiveSourceRoute
classifyNegativeEffectiveSource Signed.positiveCoupling Source.positiveSource ()
classifyNegativeEffectiveSource Signed.positiveCoupling Source.zeroSource ()
classifyNegativeEffectiveSource Signed.positiveCoupling Source.negativeSource proof =
  positiveCouplingNegativeSourceRoute
classifyNegativeEffectiveSource Signed.zeroCoupling source ()
classifyNegativeEffectiveSource Signed.negativeCoupling Source.positiveSource proof =
  negativeCouplingPositiveSourceRoute
classifyNegativeEffectiveSource Signed.negativeCoupling Source.zeroSource ()
classifyNegativeEffectiveSource Signed.negativeCoupling Source.negativeSource ()

positiveCouplingPositiveSourceCannotProduceNegativeEffectiveSource :
  Source.effectiveSourceOrientation
      Signed.positiveCoupling
      Source.positiveSource
    ≡ Source.negativeEffectiveSource →
  ⊥
positiveCouplingPositiveSourceCannotProduceNegativeEffectiveSource ()

negativeCouplingNegativeSourceCannotProduceNegativeEffectiveSource :
  Source.effectiveSourceOrientation
      Signed.negativeCoupling
      Source.negativeSource
    ≡ Source.negativeEffectiveSource →
  ⊥
negativeCouplingNegativeSourceCannotProduceNegativeEffectiveSource ()

negativeEffectiveSourceRequiresExactlyOneNegativeSign :
  (coupling : Signed.CouplingSign) →
  (source : Source.SourceSign) →
  Source.effectiveSourceOrientation coupling source
    ≡ Source.negativeEffectiveSource →
  NegativeEffectiveSourceRoute
negativeEffectiveSourceRequiresExactlyOneNegativeSign =
  classifyNegativeEffectiveSource

------------------------------------------------------------------------
-- Newtonian local response: positive density plus negative coupling is the
-- direct sign-level repulsive branch already present in the repo.
------------------------------------------------------------------------

negativeCouplingPositiveDensityRepelsInFrozenNewtonianProbe :
  Newton.positiveDensityRadialResponse Signed.negativeCoupling
    ≡ Newton.repulsiveAwayFromPositiveSource
negativeCouplingPositiveDensityRepelsInFrozenNewtonianProbe =
  Newton.negativeGPositiveDensityIsRepulsiveInSignProbe

positiveCouplingPositiveDensityCannotEqualRepulsiveBranch :
  Newton.positiveDensityRadialResponse Signed.positiveCoupling
    ≡ Newton.repulsiveAwayFromPositiveSource →
  ⊥
positiveCouplingPositiveDensityCannotEqualRepulsiveBranch ()

------------------------------------------------------------------------
-- PHYSICAL REALISATION ROUTES FOR THE NEGATIVE-SOURCE BRANCH
--
-- SourceSign is deliberately coarser than a physical stress tensor.  The
-- existing negative-mass BIDI already names the two source-side coordinates
-- that can realise a negative active gravitational source without changing G:
-- active source sign itself, or sufficiently negative pressure/tension.
------------------------------------------------------------------------

data NegativeActiveSourceRealisation : Set where
  activeGravitationalSourceSignReversal :
    NegativeActiveSourceRealisation
  effectiveNegativePressureOrTension :
    NegativeActiveSourceRealisation

negativeActiveSourceTarget :
  NegativeActiveSourceRealisation → Gravity.NegativeMassTarget
negativeActiveSourceTarget activeGravitationalSourceSignReversal =
  Gravity.activeGravitationalSource
negativeActiveSourceTarget effectiveNegativePressureOrTension =
  Gravity.effectiveNegativePressureSource

------------------------------------------------------------------------
-- COUPLING-SIDE REALISATIONS
--
-- The same negative coupling coordinate splits again by scope.  A local
-- material-effective sign reversal is not the universal Newton-G hypothesis.
------------------------------------------------------------------------

data NegativeCouplingRealisation : Set where
  universalNegativeNewtonCoupling : NegativeCouplingRealisation
  materialEffectiveNegativeCoupling : NegativeCouplingRealisation
  sourceSpecificNegativeCoupling : NegativeCouplingRealisation

negativeCouplingScope :
  NegativeCouplingRealisation → Scope.CouplingScope
negativeCouplingScope universalNegativeNewtonCoupling =
  Scope.universalNewtonCoupling
negativeCouplingScope materialEffectiveNegativeCoupling =
  Scope.materialEffectiveCoupling
negativeCouplingScope sourceSpecificNegativeCoupling =
  Scope.sourceSpecificEffectiveCoupling

materialEffectiveRouteIsNotUniversalRoute :
  negativeCouplingScope materialEffectiveNegativeCoupling
    ≡ negativeCouplingScope universalNegativeNewtonCoupling →
  ⊥
materialEffectiveRouteIsNotUniversalRoute ()

------------------------------------------------------------------------
-- MAXIMAL MECHANISM MAP
--
-- This is the useful research split:
--
--   source-product GR/Newton lane:
--     A. negative coupling, positive source
--     B. positive coupling, negative active source
--
--   source-side physical candidates for B:
--     B1. active gravitational source sign reversal
--     B2. negative pressure/tension contribution
--
--   coupling-side scope candidates for A:
--     A1. universal negative G
--     A2. material-effective negative coupling
--     A3. source-specific effective coupling
--
-- If an experiment closes both ordinary positive G and positive active source,
-- then a repulsive signal is outside this two-sign source-product model and
-- must be routed to geometry modification or an additional force channel.
------------------------------------------------------------------------

data RemoteRepulsionMechanismRoute : Set where
  negativeCouplingRoute :
    NegativeCouplingRealisation → RemoteRepulsionMechanismRoute
  negativeActiveSourceRoute :
    NegativeActiveSourceRealisation → RemoteRepulsionMechanismRoute
  modifiedGeometryRoute : RemoteRepulsionMechanismRoute
  additionalForceRoute : RemoteRepulsionMechanismRoute

record StandardPositiveSourceProductClosed : Set where
  constructor standard-positive-source-product-closed
  field
    couplingIsPositive : Signed.CouplingSign
    couplingPositive :
      couplingIsPositive ≡ Signed.positiveCoupling
    activeSourceIsPositive : Source.SourceSign
    sourcePositive :
      activeSourceIsPositive ≡ Source.positiveSource

open StandardPositiveSourceProductClosed public

standardPositiveSourceProductCannotInternallyGenerateRepulsion :
  (closed : StandardPositiveSourceProductClosed) →
  Source.effectiveSourceOrientation
      (couplingIsPositive closed)
      (activeSourceIsPositive closed)
    ≡ Source.negativeEffectiveSource →
  ⊥
standardPositiveSourceProductCannotInternallyGenerateRepulsion
  (standard-positive-source-product-closed .Signed.positiveCoupling refl
                                           .Source.positiveSource refl) ()

record RepulsionMechanismClassificationBoundary : Set where
  constructor repulsion-mechanism-classification-boundary
  field
    positiveGPositiveSourceCanProduceNegativeSourceProduct : Bool
    negativeSourceProductHasTwoSignOrigins : Bool
    negativeCouplingEqualsNegativeActiveSource : Bool
    negativeActiveSourceMustMeanNegativeInertialMass : Bool
    negativePressureTensionIsASeparateSourceRoute : Bool
    materialEffectiveNegativeCouplingEqualsUniversalNegativeG : Bool
    closingBothSignRoutesLeavesGeometryOrExtraForce : Bool

canonicalRepulsionMechanismClassificationBoundary :
  RepulsionMechanismClassificationBoundary
canonicalRepulsionMechanismClassificationBoundary =
  repulsion-mechanism-classification-boundary
    false true false false true false true
