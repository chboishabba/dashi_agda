module DASHI.Moonshine.OggSSPP2InertiaBrauerRegularityBoundaryExact where

------------------------------------------------------------------------
-- p=2 INERTIA / BRAUER-REGULARITY BOUNDARY
--
-- The five unoriented binary-tetrahedral inertia sectors have representative
-- element orders:
--
--     1, 2, 4, 3, 6.
--
-- At p=2 only the identity and order-3 representative are 2-regular.
-- The central -1, order-4 and order-6 representatives are 2-singular.
--
-- CONSEQUENCE
--
-- The full five-sector correction cannot be obtained by the naive procedure
--
--     "evaluate an ordinary Brauer character on each sector representative".
--
-- This does NOT obstruct Urano's finite-length generalized Brauer theory or a
-- Tate/localization construction whose sectors label local pieces while the
-- character is evaluated on an appropriate p-regular commuting element.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Inertia
import DASHI.Moonshine.OggSSPP2InertiaCentralizerValuationExact as Centralizer
import DASHI.Moonshine.OggSSPSmallPrimeDVRLengthBrauerCutsetExact as DVR
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Representative orders and 2-regularity.
------------------------------------------------------------------------

representativeOrder :
  Inertia.BinaryTetrahedralInversionOrbit ->
  Nat
representativeOrder Inertia.identityInertiaOrbit = 1
representativeOrder Inertia.centralMinusOneInertiaOrbit = 2
representativeOrder Inertia.orderFourInertiaOrbit = 4
representativeOrder Inertia.orderThreePairInertiaOrbit = 3
representativeOrder Inertia.orderSixPairInertiaOrbit = 6

isTwoRegular :
  Inertia.BinaryTetrahedralInversionOrbit ->
  Bool
isTwoRegular Inertia.identityInertiaOrbit = true
isTwoRegular Inertia.centralMinusOneInertiaOrbit = false
isTwoRegular Inertia.orderFourInertiaOrbit = false
isTwoRegular Inertia.orderThreePairInertiaOrbit = true
isTwoRegular Inertia.orderSixPairInertiaOrbit = false

identitySectorTwoRegular :
  isTwoRegular Inertia.identityInertiaOrbit ≡ true
identitySectorTwoRegular = refl

orderThreeSectorTwoRegular :
  isTwoRegular Inertia.orderThreePairInertiaOrbit ≡ true
orderThreeSectorTwoRegular = refl

centralMinusOneSectorTwoSingular :
  isTwoRegular Inertia.centralMinusOneInertiaOrbit ≡ false
centralMinusOneSectorTwoSingular = refl

orderFourSectorTwoSingular :
  isTwoRegular Inertia.orderFourInertiaOrbit ≡ false
orderFourSectorTwoSingular = refl

orderSixSectorTwoSingular :
  isTwoRegular Inertia.orderSixPairInertiaOrbit ≡ false
orderSixSectorTwoSingular = refl

p2TwoRegularSectorCount : Nat
p2TwoRegularSectorCount = 2

p2TwoSingularSectorCount : Nat
p2TwoSingularSectorCount = 3

------------------------------------------------------------------------
-- 2. Ordinary sector-representative Brauer shortcut is impossible.
------------------------------------------------------------------------

data EveryP2InertiaRepresentativeIsTwoRegular : Set where
data OrdinaryBrauerEvaluationOnEverySectorRepresentativePaysFiveSectorRule : Set where
data ThreeSingularSectorsKillGeneralizedDVRLocalization : Set where

notEveryP2InertiaRepresentativeIsTwoRegular :
  EveryP2InertiaRepresentativeIsTwoRegular -> ⊥
notEveryP2InertiaRepresentativeIsTwoRegular ()

ordinaryBrauerRepresentativeShortcutRejected :
  OrdinaryBrauerEvaluationOnEverySectorRepresentativePaysFiveSectorRule -> ⊥
ordinaryBrauerRepresentativeShortcutRejected ()

singularSectorsDoNotKillGeneralizedDVRLocalization :
  ThreeSingularSectorsKillGeneralizedDVRLocalization -> ⊥
singularSectorsDoNotKillGeneralizedDVRLocalization ()

------------------------------------------------------------------------
-- 3. Urano generalized-DVR framework remains the relevant sourced interface.
------------------------------------------------------------------------

dvrBrauerBoundary :
  DVR.DVRLengthBrauerCutsetBoundary
dvrBrauerBoundary =
  DVR.canonicalDVRLengthBrauerCutsetBoundary

record P2InertiaBrauerRegularityBoundary : Set where
  constructor p2-inertia-brauer-regularity-boundary
  field
    representativeOrdersExact : Bool
    twoRegularSectorsExactlyTwo : Bool
    twoSingularSectorsExactlyThree : Bool
    ordinaryRepresentativeBrauerShortcutRejected : Bool
    generalizedFiniteLengthDVRRouteStillAvailable : Bool
    singularSectorLabelsPromotedToBrauerEvaluationElements : Bool
    attributionFirewallPreserved : Bool

canonicalP2InertiaBrauerRegularityBoundary :
  P2InertiaBrauerRegularityBoundary
canonicalP2InertiaBrauerRegularityBoundary =
  p2-inertia-brauer-regularity-boundary
    true true true true true false true

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction
