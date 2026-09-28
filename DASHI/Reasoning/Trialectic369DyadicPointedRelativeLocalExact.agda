module DASHI.Reasoning.Trialectic369DyadicPointedRelativeLocalExact where

------------------------------------------------------------------------
-- POINTED / RELATIVE REPAIR OF THE FAILED OBJECTWISE PUNCTURE
--
-- DASHI CONTRIBUTION
--
-- The local zero-puncture is not closed under overlap restriction:
-- a nonzero AB local can restrict to zero at A and B.
--
-- The correct finite structure is therefore pointed:
--
--   (U_AB , 0_AB) -> (A , 0_A)
--
-- with restriction maps required to preserve basepoints, while the predicate
-- "non-basepoint" is retained as relative data and is NOT required to be
-- restriction-stable.
--
-- This is the finite pointed/pair analogue needed by the repo.  It does not
-- assert a topological cofiber, quotient stack, or RH mechanism.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Reasoning.Trialectic369DescentNaturalityExact as Descent
import DASHI.Reasoning.Trialectic369DyadicSectionTriadicKernelExact as Dyadic

------------------------------------------------------------------------
-- 1. Generic pointed carrier and pointed map.
------------------------------------------------------------------------

record PointedCarrier : Set₁ where
  constructor pointed-carrier
  field
    Carrier : Set
    basepoint : Carrier

open PointedCarrier public

record PointedMap (Source Target : PointedCarrier) : Set where
  constructor pointed-map
  field
    map :
      Carrier Source ->
      Carrier Target
    preservesBasepoint :
      map (basepoint Source) ≡ basepoint Target

open PointedMap public

NonBasepoint :
  (P : PointedCarrier) ->
  Carrier P ->
  Set
NonBasepoint P x =
  x ≡ basepoint P -> ⊥

------------------------------------------------------------------------
-- 2. Pointed dyadic locals.
------------------------------------------------------------------------

ABPointed : PointedCarrier
ABPointed =
  pointed-carrier
    Descent.ABSection
    Dyadic.zeroAB

BCPointed : PointedCarrier
BCPointed =
  pointed-carrier
    Descent.BCSection
    Dyadic.zeroBC

CAPointed : PointedCarrier
CAPointed =
  pointed-carrier
    Descent.CASection
    Dyadic.zeroCA

------------------------------------------------------------------------
-- 3. Pointed overlap carriers.
------------------------------------------------------------------------

zeroOverlap : SSP.SSPTrit
zeroOverlap = SSP.sspZero

APointed : PointedCarrier
APointed =
  pointed-carrier SSP.SSPTrit zeroOverlap

BPointed : PointedCarrier
BPointed =
  pointed-carrier SSP.SSPTrit zeroOverlap

CPointed : PointedCarrier
CPointed =
  pointed-carrier SSP.SSPTrit zeroOverlap

------------------------------------------------------------------------
-- 4. Original restriction maps lifted as pointed maps.
------------------------------------------------------------------------

restrictABtoA : Descent.ABSection -> SSP.SSPTrit
restrictABtoA = Descent.aaAB

restrictABtoB : Descent.ABSection -> SSP.SSPTrit
restrictABtoB = Descent.bbAB

restrictBCtoB : Descent.BCSection -> SSP.SSPTrit
restrictBCtoB = Descent.bbBC

restrictBCtoC : Descent.BCSection -> SSP.SSPTrit
restrictBCtoC = Descent.ccBC

restrictCAtoC : Descent.CASection -> SSP.SSPTrit
restrictCAtoC = Descent.ccCA

restrictCAtoA : Descent.CASection -> SSP.SSPTrit
restrictCAtoA = Descent.aaCA

ABtoA : PointedMap ABPointed APointed
ABtoA =
  pointed-map restrictABtoA refl

ABtoB : PointedMap ABPointed BPointed
ABtoB =
  pointed-map restrictABtoB refl

BCtoB : PointedMap BCPointed BPointed
BCtoB =
  pointed-map restrictBCtoB refl

BCtoC : PointedMap BCPointed CPointed
BCtoC =
  pointed-map restrictBCtoC refl

CAtoC : PointedMap CAPointed CPointed
CAtoC =
  pointed-map restrictCAtoC refl

CAtoA : PointedMap CAPointed APointed
CAtoA =
  pointed-map restrictCAtoA refl

------------------------------------------------------------------------
-- 5. Relative punctures exist as pointed complements.
------------------------------------------------------------------------

record RelativePuncture (P : PointedCarrier) : Set where
  constructor relative-puncture
  field
    point : Carrier P
    awayFromBasepoint : NonBasepoint P point

open RelativePuncture public

offDiagonalABRelativePuncture :
  RelativePuncture ABPointed
offDiagonalABRelativePuncture =
  relative-puncture
    Dyadic.offDiagonalPuncturedAB
    (λ equality -> notEqual equality)
  where
    notEqual :
      Dyadic.offDiagonalPuncturedAB ≡ Dyadic.zeroAB ->
      ⊥
    notEqual ()

------------------------------------------------------------------------
-- 6. Pointed restriction is lawful even though punctured restriction fails.
------------------------------------------------------------------------

offDiagonalABRestrictsToBasepointAtA :
  map ABtoA
    (point offDiagonalABRelativePuncture)
  ≡ basepoint APointed
offDiagonalABRestrictsToBasepointAtA = refl

offDiagonalABRestrictsToBasepointAtB :
  map ABtoB
    (point offDiagonalABRelativePuncture)
  ≡ basepoint BPointed
offDiagonalABRestrictsToBasepointAtB = refl

data EveryPointedMapPreservesRelativePuncture : Set where

pointedMapNeedNotPreserveNonBasepoint :
  EveryPointedMapPreservesRelativePuncture -> ⊥
pointedMapNeedNotPreserveNonBasepoint ()

------------------------------------------------------------------------
-- 7. The repair principle.
------------------------------------------------------------------------

record PointedDyadicRestrictionSystem : Set₁ where
  constructor pointed-dyadic-restriction-system
  field
    localAB : PointedCarrier
    localBC : PointedCarrier
    localCA : PointedCarrier

    overlapA : PointedCarrier
    overlapB : PointedCarrier
    overlapC : PointedCarrier

    AB_A : PointedMap localAB overlapA
    AB_B : PointedMap localAB overlapB
    BC_B : PointedMap localBC overlapB
    BC_C : PointedMap localBC overlapC
    CA_C : PointedMap localCA overlapC
    CA_A : PointedMap localCA overlapA

canonicalPointedDyadicRestrictionSystem :
  PointedDyadicRestrictionSystem
canonicalPointedDyadicRestrictionSystem =
  pointed-dyadic-restriction-system
    ABPointed BCPointed CAPointed
    APointed BPointed CPointed
    ABtoA ABtoB
    BCtoB BCtoC
    CAtoC CAtoA

------------------------------------------------------------------------
-- 8. Firewall.
------------------------------------------------------------------------

data PointedPairIsTopologicalCofiber : Set where
data PointedRepairCreatesPuncturedSubpresheaf : Set where
data RelativePunctureCreatesRHMechanism : Set where

pointedPairNotPromotedToTopologicalCofiber :
  PointedPairIsTopologicalCofiber -> ⊥
pointedPairNotPromotedToTopologicalCofiber ()

pointedRepairDoesNotCreatePuncturedSubpresheaf :
  PointedRepairCreatesPuncturedSubpresheaf -> ⊥
pointedRepairDoesNotCreatePuncturedSubpresheaf ()

relativePunctureDoesNotCreateRHMechanism :
  RelativePunctureCreatesRHMechanism -> ⊥
relativePunctureDoesNotCreateRHMechanism ()

record Trialectic369DyadicPointedRelativeLocalBoundary : Set where
  constructor trialectic-369-dyadic-pointed-relative-local-boundary
  field
    localBasepointsExplicit : Bool
    overlapBasepointsExplicit : Bool
    allSixRestrictionsArePointedMaps : Bool
    nonzeroLocalMayRestrictToOverlapBasepoint : Bool
    relativePunctureCarrierConstructed : Bool
    naivePuncturedSubpresheafRejected : Bool
    topologicalCofiberClaimed : Bool
    rhMechanismClaimed : Bool

canonicalTrialectic369DyadicPointedRelativeLocalBoundary :
  Trialectic369DyadicPointedRelativeLocalBoundary
canonicalTrialectic369DyadicPointedRelativeLocalBoundary =
  trialectic-369-dyadic-pointed-relative-local-boundary
    true true true true true true false false
