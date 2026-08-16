module DASHI.Moonshine.TernarySevenOggSSPComparisonExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires",
-- Seminaire Delange-Pisot-Poitou 16 (1974-1975), expose 7, pp. 1-8,
-- MR 417184; no DOI assigned.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem",
-- Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine",
-- Bulletin of the London Mathematical Society 11 (1979), 308--339.
-- DOI: 10.1112/blms/11.3.308.
--
-- Richard E. Borcherds,
-- "Monstrous Moonshine and Monstrous Lie Superalgebras",
-- Inventiones Mathematicae 109 (1992), 405--444.
-- DOI: 10.1007/BF01232032.
--
-- DASHI CONTRIBUTION
--
-- Place three already-exact seven-state surfaces side by side:
--
--   * seven nonunit classes after the free C3 output-phase quotient of T^T;
--   * seven S3-conjugacy functional-graph shapes of T^T;
--   * each of the two seven-lane mirrors in the existing Ogg 7+7+1 carrier.
--
-- IMPORTANT ARCHITECTURAL CORRECTION
--
-- The 7+7+1 carrier is a downstream finite comparison surface only. It is NOT
-- used as the explanation or selector of the Ogg/SSP set. The upstream SSP
-- research lane now starts from actual continuous irreps, finite subgroup
-- restriction, branching/fixed-space spectra, non-Ogg controls, and an
-- independent modular/Hecke column. Equal seven-cardinality remains only a
-- comparison datum unless a separate representation-theoretic map is proved.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Foundations.SSPPrimeLaneUnitAction as SSP
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Shape
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase
import DASHI.Moonshine.MonsterOggNonaryProbeAuthorityExact as Probe
import DASHI.Moonshine.MonsterOggNonarySevenSevenOneEquivalenceExact as Ogg

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ rest) = 1 + listCount rest

phaseNonUnitSeven : List Phase.NonUnitPhase7
phaseNonUnitSeven =
  Phase.nonUnitLowLow
  ∷ Phase.nonUnitLowMid
  ∷ Phase.nonUnitLowHigh
  ∷ Phase.nonUnitMidLow
  ∷ Phase.nonUnitMidMid
  ∷ Phase.nonUnitHighLow
  ∷ Phase.nonUnitHighHigh
  ∷ []

shapeOrbitSeven : List Shape.ShapeOrbit7
shapeOrbitSeven =
  Shape.identityShape
  ∷ Shape.threeCycleShape
  ∷ Shape.transpositionShape
  ∷ Shape.constantShape
  ∷ Shape.rank2OneFixedShape
  ∷ Shape.rank2TwoFixedShape
  ∷ Shape.rank2TwoCycleShape
  ∷ []

oggMirrorASeven : List Probe.MirrorA7Lane
oggMirrorASeven =
  Probe.mirrorA2
  ∷ Probe.mirrorA3
  ∷ Probe.mirrorA5
  ∷ Probe.mirrorA7
  ∷ Probe.mirrorA11
  ∷ Probe.mirrorA13
  ∷ Probe.mirrorA17
  ∷ []

oggMirrorBSeven : List Probe.MirrorB7Lane
oggMirrorBSeven =
  Probe.mirrorB19
  ∷ Probe.mirrorB23
  ∷ Probe.mirrorB29
  ∷ Probe.mirrorB31
  ∷ Probe.mirrorB41
  ∷ Probe.mirrorB47
  ∷ Probe.mirrorB59
  ∷ []

phaseNonUnitCountIsSeven : listCount phaseNonUnitSeven ≡ 7
phaseNonUnitCountIsSeven = refl

shapeOrbitCountIsSeven : listCount shapeOrbitSeven ≡ 7
shapeOrbitCountIsSeven = refl

oggMirrorACountIsSeven : listCount oggMirrorASeven ≡ 7
oggMirrorACountIsSeven = refl

oggMirrorBCountIsSeven : listCount oggMirrorBSeven ≡ 7
oggMirrorBCountIsSeven = refl

existingOggSevenSevenOneEquivalence : Ogg.SevenSevenOneCarrierEquivalence
existingOggSevenSevenOneEquivalence = Ogg.canonicalSevenSevenOneCarrierEquivalence

p7GeneratorTriadicStepIsOne : SSP.triadicStep SSP.p7GeneratorUnitActionProfile ≡ 1
p7GeneratorTriadicStepIsOne = SSP.p7GeneratorTriadicStepIs1

p11GeneratorTriadicStepIsOne : SSP.triadicStep SSP.p11GeneratorUnitActionProfile ≡ 1
p11GeneratorTriadicStepIsOne = SSP.p11GeneratorTriadicStepIs1

record TernarySevenOggSSPBoundary : Set where
  field
    phaseSevenConstructed : Bool
    phaseSevenConstructedIsTrue : phaseSevenConstructed ≡ true

    conjugacySevenConstructed : Bool
    conjugacySevenConstructedIsTrue : conjugacySevenConstructed ≡ true

    oggSevenSevenOneReused : Bool
    oggSevenSevenOneReusedIsTrue : oggSevenSevenOneReused ≡ true

    equalSevenCardinalityPromotesCarrierIdentity : Bool
    equalSevenCardinalityPromotesCarrierIdentityIsFalse :
      equalSevenCardinalityPromotesCarrierIdentity ≡ false

    sevenSevenOneUsedAsSSPSelector : Bool
    sevenSevenOneUsedAsSSPSelectorIsFalse :
      sevenSevenOneUsedAsSSPSelector ≡ false

    representationRestrictionMustBeDerivedUpstream : Bool
    representationRestrictionMustBeDerivedUpstreamIsTrue :
      representationRestrictionMustBeDerivedUpstream ≡ true

    oggCarrierPromotedToMonsterRepresentationDecomposition : Bool
    oggCarrierPromotedToMonsterRepresentationDecompositionIsFalse :
      oggCarrierPromotedToMonsterRepresentationDecomposition ≡ false

canonicalTernarySevenOggSSPBoundary : TernarySevenOggSSPBoundary
canonicalTernarySevenOggSSPBoundary =
  record
    { phaseSevenConstructed = true
    ; phaseSevenConstructedIsTrue = refl
    ; conjugacySevenConstructed = true
    ; conjugacySevenConstructedIsTrue = refl
    ; oggSevenSevenOneReused = true
    ; oggSevenSevenOneReusedIsTrue = refl
    ; equalSevenCardinalityPromotesCarrierIdentity = false
    ; equalSevenCardinalityPromotesCarrierIdentityIsFalse = refl
    ; sevenSevenOneUsedAsSSPSelector = false
    ; sevenSevenOneUsedAsSSPSelectorIsFalse = refl
    ; representationRestrictionMustBeDerivedUpstream = true
    ; representationRestrictionMustBeDerivedUpstreamIsTrue = refl
    ; oggCarrierPromotedToMonsterRepresentationDecomposition = false
    ; oggCarrierPromotedToMonsterRepresentationDecompositionIsFalse = refl
    }
