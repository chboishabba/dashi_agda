module Ontology.Hecke.TriadFiveSSPCoordinateBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_; _+_)

open import MonsterOntos
  using
    ( SSP
    ; p2; p3; p5; p7; p11
    ; p13; p17; p19; p23; p29
    ; p31; p41; p47; p59; p71
    )
open import Ontology.Hecke.TriadIndexedDefectOrbitSummaryRefinement
  using (TriadSector; sector0; sector1; sector2)

------------------------------------------------------------------------
-- Candidate 3 × 5 coordinate carrier.
--
-- This bridge cross-pollinates the triad-indexed Hecke refinement with the
-- existing 15-element SSP carrier.  The assignment below is explicit and
-- reversible as a finite bookkeeping proposal, but it is not claimed to be a
-- canonical Monster action, representation, or moonshine theorem.

data FiveClass : Set where
  class0 : FiveClass
  class1 : FiveClass
  class2 : FiveClass
  class3 : FiveClass
  class4 : FiveClass

record TriadFiveCoordinate : Set where
  constructor triadFive
  field
    sector : TriadSector
    localClass : FiveClass

open TriadFiveCoordinate public

triadFiveCarrierCount : Nat
triadFiveCarrierCount = 3 * 5

triadFiveCarrierCount≡15 : triadFiveCarrierCount ≡ 15
triadFiveCarrierCount≡15 = refl

------------------------------------------------------------------------
-- Row-major finite coordinate index.

classIndex : FiveClass → Nat
classIndex class0 = 0
classIndex class1 = 1
classIndex class2 = 2
classIndex class3 = 3
classIndex class4 = 4

sectorIndex : TriadSector → Nat
sectorIndex sector0 = 0
sectorIndex sector1 = 1
sectorIndex sector2 = 2

coordinateIndex : TriadFiveCoordinate → Nat
coordinateIndex c = sectorIndex (sector c) * 5 + classIndex (localClass c)

------------------------------------------------------------------------
-- Explicit candidate labeling by the existing SSP carrier.
--
-- The ordering is intentionally transparent.  Any later claim that this is
-- the physically or representation-theoretically correct ordering must be
-- supplied as a separate theorem and cannot be smuggled in through the type.

sspLabel : TriadFiveCoordinate → SSP
sspLabel (triadFive sector0 class0) = p2
sspLabel (triadFive sector0 class1) = p3
sspLabel (triadFive sector0 class2) = p5
sspLabel (triadFive sector0 class3) = p7
sspLabel (triadFive sector0 class4) = p11
sspLabel (triadFive sector1 class0) = p13
sspLabel (triadFive sector1 class1) = p17
sspLabel (triadFive sector1 class2) = p19
sspLabel (triadFive sector1 class3) = p23
sspLabel (triadFive sector1 class4) = p29
sspLabel (triadFive sector2 class0) = p31
sspLabel (triadFive sector2 class1) = p41
sspLabel (triadFive sector2 class2) = p47
sspLabel (triadFive sector2 class3) = p59
sspLabel (triadFive sector2 class4) = p71

coordinateOfSSP : SSP → TriadFiveCoordinate
coordinateOfSSP p2  = triadFive sector0 class0
coordinateOfSSP p3  = triadFive sector0 class1
coordinateOfSSP p5  = triadFive sector0 class2
coordinateOfSSP p7  = triadFive sector0 class3
coordinateOfSSP p11 = triadFive sector0 class4
coordinateOfSSP p13 = triadFive sector1 class0
coordinateOfSSP p17 = triadFive sector1 class1
coordinateOfSSP p19 = triadFive sector1 class2
coordinateOfSSP p23 = triadFive sector1 class3
coordinateOfSSP p29 = triadFive sector1 class4
coordinateOfSSP p31 = triadFive sector2 class0
coordinateOfSSP p41 = triadFive sector2 class1
coordinateOfSSP p47 = triadFive sector2 class2
coordinateOfSSP p59 = triadFive sector2 class3
coordinateOfSSP p71 = triadFive sector2 class4

------------------------------------------------------------------------
-- Both round trips compute definitionally.  This proves only a finite carrier
-- equivalence for the chosen labeling.

coordinate-label-roundtrip :
  ∀ c → coordinateOfSSP (sspLabel c) ≡ c
coordinate-label-roundtrip (triadFive sector0 class0) = refl
coordinate-label-roundtrip (triadFive sector0 class1) = refl
coordinate-label-roundtrip (triadFive sector0 class2) = refl
coordinate-label-roundtrip (triadFive sector0 class3) = refl
coordinate-label-roundtrip (triadFive sector0 class4) = refl
coordinate-label-roundtrip (triadFive sector1 class0) = refl
coordinate-label-roundtrip (triadFive sector1 class1) = refl
coordinate-label-roundtrip (triadFive sector1 class2) = refl
coordinate-label-roundtrip (triadFive sector1 class3) = refl
coordinate-label-roundtrip (triadFive sector1 class4) = refl
coordinate-label-roundtrip (triadFive sector2 class0) = refl
coordinate-label-roundtrip (triadFive sector2 class1) = refl
coordinate-label-roundtrip (triadFive sector2 class2) = refl
coordinate-label-roundtrip (triadFive sector2 class3) = refl
coordinate-label-roundtrip (triadFive sector2 class4) = refl

label-coordinate-roundtrip :
  ∀ p → sspLabel (coordinateOfSSP p) ≡ p
label-coordinate-roundtrip p2  = refl
label-coordinate-roundtrip p3  = refl
label-coordinate-roundtrip p5  = refl
label-coordinate-roundtrip p7  = refl
label-coordinate-roundtrip p11 = refl
label-coordinate-roundtrip p13 = refl
label-coordinate-roundtrip p17 = refl
label-coordinate-roundtrip p19 = refl
label-coordinate-roundtrip p23 = refl
label-coordinate-roundtrip p29 = refl
label-coordinate-roundtrip p31 = refl
label-coordinate-roundtrip p41 = refl
label-coordinate-roundtrip p47 = refl
label-coordinate-roundtrip p59 = refl
label-coordinate-roundtrip p71 = refl

------------------------------------------------------------------------
-- Promotion boundary: a finite equivalence is not yet a Monster theorem.

record MonsterInterpretationObligation : Set₁ where
  field
    actionCarrier : Set
    action : actionCarrier → TriadFiveCoordinate → TriadFiveCoordinate
    preservesHeckeSummary : Set
    representationWitness : Set
    moonshineCompatibility : Set

MonsterBridgeTarget : Set₁
MonsterBridgeTarget = MonsterInterpretationObligation
