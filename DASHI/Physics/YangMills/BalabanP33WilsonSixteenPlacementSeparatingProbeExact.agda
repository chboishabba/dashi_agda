module DASHI.Physics.YangMills.BalabanP33WilsonSixteenPlacementSeparatingProbeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Tadeusz Balaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II", Communications in Mathematical Physics 96 (1984), 223--250.
-- DOI: 10.1007/BF01240221.
--
-- DASHI CONTRIBUTION
-- Make the four diagonal second-jet placements and twelve ordered first--first
-- placements into a literal separating audit family.  Agreement of the total
-- Wilson defect is not enough; agreement on all sixteen probes determines the
-- complete placement vector.  No signed bound or allocation coefficient is
-- supplied by this finite identification theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_+_)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Common.SeparatingProbeFamilyExact as Common

data PlacementProbe : Set where
  diagonal0 : PlacementProbe
  diagonal1 : PlacementProbe
  diagonal2 : PlacementProbe
  diagonal3 : PlacementProbe
  ordered01 : PlacementProbe
  ordered02 : PlacementProbe
  ordered03 : PlacementProbe
  ordered10 : PlacementProbe
  ordered12 : PlacementProbe
  ordered13 : PlacementProbe
  ordered20 : PlacementProbe
  ordered21 : PlacementProbe
  ordered23 : PlacementProbe
  ordered30 : PlacementProbe
  ordered31 : PlacementProbe
  ordered32 : PlacementProbe

data PlacementKind : Set where
  diagonalSecondJet : PlacementKind
  orderedFirstFirst : PlacementKind

placementKind : PlacementProbe → PlacementKind
placementKind diagonal0 = diagonalSecondJet
placementKind diagonal1 = diagonalSecondJet
placementKind diagonal2 = diagonalSecondJet
placementKind diagonal3 = diagonalSecondJet
placementKind ordered01 = orderedFirstFirst
placementKind ordered02 = orderedFirstFirst
placementKind ordered03 = orderedFirstFirst
placementKind ordered10 = orderedFirstFirst
placementKind ordered12 = orderedFirstFirst
placementKind ordered13 = orderedFirstFirst
placementKind ordered20 = orderedFirstFirst
placementKind ordered21 = orderedFirstFirst
placementKind ordered23 = orderedFirstFirst
placementKind ordered30 = orderedFirstFirst
placementKind ordered31 = orderedFirstFirst
placementKind ordered32 = orderedFirstFirst

record PlacementVector : Set where
  constructor placementVector
  field
    diagonalValue0 : ℚ
    diagonalValue1 : ℚ
    diagonalValue2 : ℚ
    diagonalValue3 : ℚ
    orderedValue01 : ℚ
    orderedValue02 : ℚ
    orderedValue03 : ℚ
    orderedValue10 : ℚ
    orderedValue12 : ℚ
    orderedValue13 : ℚ
    orderedValue20 : ℚ
    orderedValue21 : ℚ
    orderedValue23 : ℚ
    orderedValue30 : ℚ
    orderedValue31 : ℚ
    orderedValue32 : ℚ

open PlacementVector public

observePlacement : PlacementProbe → PlacementVector → ℚ
observePlacement diagonal0 vector = diagonalValue0 vector
observePlacement diagonal1 vector = diagonalValue1 vector
observePlacement diagonal2 vector = diagonalValue2 vector
observePlacement diagonal3 vector = diagonalValue3 vector
observePlacement ordered01 vector = orderedValue01 vector
observePlacement ordered02 vector = orderedValue02 vector
observePlacement ordered03 vector = orderedValue03 vector
observePlacement ordered10 vector = orderedValue10 vector
observePlacement ordered12 vector = orderedValue12 vector
observePlacement ordered13 vector = orderedValue13 vector
observePlacement ordered20 vector = orderedValue20 vector
observePlacement ordered21 vector = orderedValue21 vector
observePlacement ordered23 vector = orderedValue23 vector
observePlacement ordered30 vector = orderedValue30 vector
observePlacement ordered31 vector = orderedValue31 vector
observePlacement ordered32 vector = orderedValue32 vector

placementProbesSeparate :
  ∀ left right →
  ((probe : PlacementProbe) →
    observePlacement probe left ≡ observePlacement probe right) →
  left ≡ right
placementProbesSeparate
  (placementVector
    leftD0 leftD1 leftD2 leftD3
    left01 left02 left03 left10 left12 left13
    left20 left21 left23 left30 left31 left32)
  (placementVector
    rightD0 rightD1 rightD2 rightD3
    right01 right02 right03 right10 right12 right13
    right20 right21 right23 right30 right31 right32)
  agreement
  rewrite agreement diagonal0
        | agreement diagonal1
        | agreement diagonal2
        | agreement diagonal3
        | agreement ordered01
        | agreement ordered02
        | agreement ordered03
        | agreement ordered10
        | agreement ordered12
        | agreement ordered13
        | agreement ordered20
        | agreement ordered21
        | agreement ordered23
        | agreement ordered30
        | agreement ordered31
        | agreement ordered32 = refl

sixteenPlacementProbeSystem :
  Common.SeparatingProbeSystem PlacementVector ℚ
sixteenPlacementProbeSystem =
  Common.separatingProbeSystem
    PlacementProbe
    observePlacement
    placementProbesSeparate

diagonalPlacementCount : Nat
diagonalPlacementCount = 4

orderedCrossPlacementCount : Nat
orderedCrossPlacementCount = 12

totalPlacementCount : Nat
totalPlacementCount = diagonalPlacementCount + orderedCrossPlacementCount

totalPlacementCountIsSixteen : totalPlacementCount ≡ 16
totalPlacementCountIsSixteen = refl

record SixteenPlacementBoundary : Set where
  constructor sixteenPlacementBoundary
  field
    unorderedSixPairCountMayReplaceOrderedTwelve : Set
    unorderedSixPairCountMayNotReplaceOrderedTwelve :
      unorderedSixPairCountMayReplaceOrderedTwelve → Set

    separatingPlacementVectorSuppliesSignedWLocalBound : Set
    separatingPlacementVectorDoesNotSupplySignedWLocalBound :
      separatingPlacementVectorSuppliesSignedWLocalBound → Set

canonicalSixteenPlacementBoundary : SixteenPlacementBoundary
canonicalSixteenPlacementBoundary =
  sixteenPlacementBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
