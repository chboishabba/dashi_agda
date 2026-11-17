module DASHI.Combinatorics.TriadFiveFractranIndex where

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Combinatorics.FractranCOL
  using (EV5; get; set)
open import DASHI.Combinatorics.FractranComputationEquivalence
  using (SameOutcome)
open import MonsterOntos using (SSP)
open import Ontology.Hecke.TriadFiveSSPCoordinateBridge
  using
    ( FiveClass
    ; class0; class1; class2; class3; class4
    ; TriadFiveCoordinate
    ; triadFive
    ; sector
    ; localClass
    ; classIndex
    ; sspLabel
    ; coordinateOfSSP
    ; coordinate-label-roundtrip
    )
open import Ontology.Hecke.TriadIndexedDefectOrbitSummaryRefinement
  using (TriadSector; sector0; sector1; sector2)

------------------------------------------------------------------------
-- Index the candidate 3 × 5 carrier on the existing concrete FRACTRAN
-- state representation.
--
-- `FractranCOL.EV5` is already a five-lane prime-exponent state.  The
-- smallest structure-preserving adapter is therefore three EV5 banks:
-- one existing FRACTRAN state per triadic sector.  The sector chooses the
-- bank and the local five-class chooses the existing FRACTRAN lane.
--
-- This is an index/coordinate adapter only.  It does not identify the three
-- banks with three time steps, three rules, or three Monster orbits.

record TriadFractranState : Set where
  constructor triadFractranState
  field
    sector0State : EV5
    sector1State : EV5
    sector2State : EV5

open TriadFractranState public

sectorState : TriadFractranState → TriadSector → EV5
sectorState state sector0 = sector0State state
sectorState state sector1 = sector1State state
sectorState state sector2 = sector2State state

replaceSectorState :
  TriadFractranState → TriadSector → EV5 → TriadFractranState
replaceSectorState state sector0 next =
  triadFractranState next (sector1State state) (sector2State state)
replaceSectorState state sector1 next =
  triadFractranState (sector0State state) next (sector2State state)
replaceSectorState state sector2 next =
  triadFractranState (sector0State state) (sector1State state) next

coordinateExponent : TriadFractranState → TriadFiveCoordinate → Nat
coordinateExponent state coordinate =
  get
    (sectorState state (sector coordinate))
    (classIndex (localClass coordinate))

setCoordinateExponent :
  TriadFractranState → TriadFiveCoordinate → Nat → TriadFractranState
setCoordinateExponent state coordinate value =
  replaceSectorState
    state
    (sector coordinate)
    (set
      (sectorState state (sector coordinate))
      (classIndex (localClass coordinate))
      value)

------------------------------------------------------------------------
-- SSP-labelled view of the same 15 coordinates.

sspExponent : TriadFractranState → SSP → Nat
sspExponent state prime =
  coordinateExponent state (coordinateOfSSP prime)

coordinateExponent-via-ssp :
  ∀ state coordinate →
  sspExponent state (sspLabel coordinate)
    ≡ coordinateExponent state coordinate
coordinateExponent-via-ssp state coordinate =
  cong (coordinateExponent state) (coordinate-label-roundtrip coordinate)

------------------------------------------------------------------------
-- Explicit lane computations.  These receipts show that the adapter really
-- reuses the five existing FRACTRAN lanes in each sector rather than flattening
-- the carrier into an unrelated 15-register convention.

sector0-class0-index :
  ∀ state →
  coordinateExponent state (triadFive sector0 class0)
    ≡ get (sector0State state) 0
sector0-class0-index state = refl

sector0-class4-index :
  ∀ state →
  coordinateExponent state (triadFive sector0 class4)
    ≡ get (sector0State state) 4
sector0-class4-index state = refl

sector1-class0-index :
  ∀ state →
  coordinateExponent state (triadFive sector1 class0)
    ≡ get (sector1State state) 0
sector1-class0-index state = refl

sector1-class4-index :
  ∀ state →
  coordinateExponent state (triadFive sector1 class4)
    ≡ get (sector1State state) 4
sector1-class4-index state = refl

sector2-class0-index :
  ∀ state →
  coordinateExponent state (triadFive sector2 class0)
    ≡ get (sector2State state) 0
sector2-class0-index state = refl

sector2-class4-index :
  ∀ state →
  coordinateExponent state (triadFive sector2 class4)
    ≡ get (sector2State state) 4
sector2-class4-index state = refl

------------------------------------------------------------------------
-- Catalogue bridge.
--
-- The concrete lane adapter above is total.  Turning it into a canonical
-- FRACTRAN catalogue is stronger: a classifier and representative must prove
-- terminal-outcome soundness under the existing `FractranCOL.run` semantics.
-- Those witnesses are kept explicit so a coordinate label cannot silently
-- become a computation-equivalence claim.

record TriadFiveFractranCatalogueIndex : Set₁ where
  field
    classify       : EV5 → TriadFiveCoordinate
    representative : TriadFiveCoordinate → EV5

    representative-sound :
      ∀ state → SameOutcome (representative (classify state)) state

    coordinate-complete-for-outcome :
      ∀ {left right} →
      classify left ≡ classify right →
      SameOutcome left right

open TriadFiveFractranCatalogueIndex public

------------------------------------------------------------------------
-- Dynamic compatibility boundary.
--
-- The three-bank index does not yet provide a FRACTRAN transition over all
-- fifteen coordinates.  A promoted dynamic bridge must state how a concrete
-- FRACTRAN step is lifted and prove that the coordinate observation is
-- preserved or evolves according to the declared Hecke-side law.

record TriadFiveFractranDynamicBridge : Set₁ where
  field
    stepTriad : TriadFractranState → TriadFractranState
    coordinateTransitionLaw : Set
    preservesPromotedHeckeInvariant : Set
    respectsMDLPromotionReceipt : Set

TriadFiveFractranDynamicBridgeTarget : Set₁
TriadFiveFractranDynamicBridgeTarget = TriadFiveFractranDynamicBridge
