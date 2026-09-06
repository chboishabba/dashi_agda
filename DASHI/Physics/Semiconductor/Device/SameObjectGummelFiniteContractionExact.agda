{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.SameObjectGummelFiniteContractionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Analysis.StrictContractionUniqueness as SCU
import DASHI.Physics.Semiconductor.Device.FinitePoissonGreenCrossPollinationExact as Poisson
import DASHI.Physics.Semiconductor.Device.DriftDiffusionContinuityExact as Transport

------------------------------------------------------------------------
-- SAME-OBJECT RESTRICTED GUMMEL FIXTURE
--
-- This is a deliberately tiny exact fixture for the coupling architecture
--
--   (phi,n,p,Jn,Jp) -> Poisson -> transport -> continuity -> next iterate.
--
-- The three constructors are three states of ONE device-iterate carrier.  The
-- Nat coordinates are normalized synthetic codes, not volts, densities, or
-- amperes from a real TSMC device.  The point is to inhabit an exact finite
-- convergence theorem on the corrected distinct-pair contraction surface.
------------------------------------------------------------------------

data DeviceIterate : Set where
  farIterate nearIterate fixedIterate : DeviceIterate

potentialCode : DeviceIterate → Nat
potentialCode farIterate = 2
potentialCode nearIterate = 4
potentialCode fixedIterate = 5

electronCode : DeviceIterate → Nat
electronCode farIterate = 8
electronCode nearIterate = 6
electronCode fixedIterate = 5

holeCode : DeviceIterate → Nat
holeCode farIterate = 4
holeCode nearIterate = 3
holeCode fixedIterate = 3

electronCurrentCode : DeviceIterate → Nat
electronCurrentCode farIterate = 6
electronCurrentCode nearIterate = 5
electronCurrentCode fixedIterate = 4

holeCurrentCode : DeviceIterate → Nat
holeCurrentCode farIterate = 2
holeCurrentCode nearIterate = 2
holeCurrentCode fixedIterate = 2

record CoupledDeviceCoordinates : Set where
  constructor coupledDeviceCoordinates
  field
    phi : Nat
    n   : Nat
    p   : Nat
    Jn  : Nat
    Jp  : Nat

open CoupledDeviceCoordinates public

coordinates : DeviceIterate → CoupledDeviceCoordinates
coordinates state = coupledDeviceCoordinates
  (potentialCode state)
  (electronCode state)
  (holeCode state)
  (electronCurrentCode state)
  (holeCurrentCode state)

------------------------------------------------------------------------
-- One restricted Gummel sweep.  All coupled coordinates move on the same
-- carrier; there is no separately chosen Poisson state and transport state.
------------------------------------------------------------------------

gummelStep : DeviceIterate → DeviceIterate
gummelStep farIterate = nearIterate
gummelStep nearIterate = fixedIterate
gummelStep fixedIterate = fixedIterate

fixedIsFixed : gummelStep fixedIterate ≡ fixedIterate
fixedIsFixed = refl

farReachesFixedInTwo : gummelStep (gummelStep farIterate) ≡ fixedIterate
farReachesFixedInTwo = refl

nearReachesFixedInOne : gummelStep nearIterate ≡ fixedIterate
nearReachesFixedInOne = refl

------------------------------------------------------------------------
-- Dependency ownership: this fixture is downstream of the already-existing
-- semiconductor Poisson and drift/continuity owners.  Their exact carriers are
-- not identified with this synthetic three-state model.
------------------------------------------------------------------------

record SameObjectGummelDependencyReceipt : Set₁ where
  field
    poissonOwnerAvailable : Set
    transportOwnerAvailable : Set

canonicalDependencies : SameObjectGummelDependencyReceipt
canonicalDependencies = record
  { poissonOwnerAvailable = Poisson.PoissonResidual
  ; transportOwnerAvailable = Transport.TransportResidual
  }

------------------------------------------------------------------------
-- Exact finite metric for the restricted basin.
------------------------------------------------------------------------

data BasinDistance : Set where
  d0 d1 d2 : BasinDistance

distance : DeviceIterate → DeviceIterate → BasinDistance
distance farIterate farIterate = d0
distance nearIterate nearIterate = d0
distance fixedIterate fixedIterate = d0

distance farIterate nearIterate = d2
distance nearIterate farIterate = d2
distance farIterate fixedIterate = d2
distance fixedIterate farIterate = d2

distance nearIterate fixedIterate = d1
distance fixedIterate nearIterate = d1

data StrictlySmaller : BasinDistance → BasinDistance → Set where
  d0<d1 : StrictlySmaller d0 d1
  d1<d2 : StrictlySmaller d1 d2
  d0<d2 : StrictlySmaller d0 d2

strictDistanceIrreflexive :
  SCU.IrreflexiveStrictDistance BasinDistance StrictlySmaller
strictDistanceIrreflexive = record
  { irreflexive = λ where
      d0 ()
      d1 ()
      d2 ()
  }

iterateEquality :
  (left right : DeviceIterate) →
  (left ≡ right) ⊎ SCU.Distinct left right
iterateEquality farIterate farIterate = inj₁ refl
iterateEquality farIterate nearIterate = inj₂ (λ ())
iterateEquality farIterate fixedIterate = inj₂ (λ ())
iterateEquality nearIterate farIterate = inj₂ (λ ())
iterateEquality nearIterate nearIterate = inj₁ refl
iterateEquality nearIterate fixedIterate = inj₂ (λ ())
iterateEquality fixedIterate farIterate = inj₂ (λ ())
iterateEquality fixedIterate nearIterate = inj₂ (λ ())
iterateEquality fixedIterate fixedIterate = inj₁ refl

contractiveDistinct :
  (left right : DeviceIterate) →
  SCU.Distinct left right →
  StrictlySmaller
    (distance (gummelStep left) (gummelStep right))
    (distance left right)
contractiveDistinct farIterate farIterate different = ⊥-elim (different refl)
contractiveDistinct farIterate nearIterate different = d1<d2
contractiveDistinct farIterate fixedIterate different = d1<d2
contractiveDistinct nearIterate farIterate different = d1<d2
contractiveDistinct nearIterate nearIterate different = ⊥-elim (different refl)
contractiveDistinct nearIterate fixedIterate different = d0<d1
contractiveDistinct fixedIterate farIterate different = d1<d2
contractiveDistinct fixedIterate nearIterate different = d0<d1
contractiveDistinct fixedIterate fixedIterate different = ⊥-elim (different refl)

restrictedGummelContraction :
  SCU.SeparatedFiniteContractionCertificate DeviceIterate BasinDistance
restrictedGummelContraction = record
  { step = gummelStep
  ; distance = distance
  ; StrictlySmaller = StrictlySmaller
  ; fixedPoint = fixedIterate
  ; fixed = refl
  ; decideEquality = iterateEquality
  ; contractiveDistinct = contractiveDistinct
  }

restrictedGummelUniqueFixedPoint :
  SCU.SeparatedUniqueFixedPointCertificate restrictedGummelContraction
restrictedGummelUniqueFixedPoint =
  SCU.certifySeparatedUniqueFixedPoint
    restrictedGummelContraction
    strictDistanceIrreflexive

anyRestrictedGummelFixedPointIsCanonical :
  (candidate : DeviceIterate) →
  gummelStep candidate ≡ candidate →
  candidate ≡ fixedIterate
anyRestrictedGummelFixedPointIsCanonical =
  SCU.SeparatedUniqueFixedPointCertificate.unique
    restrictedGummelUniqueFixedPoint

------------------------------------------------------------------------
-- Scientific firewall.
--
-- Exact convergence of this finite synthetic basin does NOT prove convergence
-- of physical Gummel iteration for a real nanosheet/FinFET device.  Promotion
-- requires a physical state space, Poisson and continuity solves on that same
-- object, boundary/contact laws, constitutive charge/mobility/recombination
-- laws, and a contraction/dissipation estimate on the admitted physical basin.
------------------------------------------------------------------------

data PhysicalGummelResidual : Set where
  SameObjectPhysicalPoissonSolve : PhysicalGummelResidual
  SameObjectElectronContinuitySolve : PhysicalGummelResidual
  SameObjectHoleContinuitySolve : PhysicalGummelResidual
  ContactBoundaryLaw : PhysicalGummelResidual
  CarrierStatisticsLaw : PhysicalGummelResidual
  MobilityLaw : PhysicalGummelResidual
  RecombinationLaw : PhysicalGummelResidual
  PhysicalBasinMetric : PhysicalGummelResidual
  PhysicalContractionEstimate : PhysicalGummelResidual
  PhysicalGummelConvergenceReceipt : PhysicalGummelResidual
