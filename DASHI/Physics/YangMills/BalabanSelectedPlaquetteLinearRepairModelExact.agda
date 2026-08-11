module DASHI.Physics.YangMills.BalabanSelectedPlaquetteLinearRepairModelExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories".
-- DOI: 10.1007/BF01229381.
--
-- Kenneth G. Wilson, "Confinement of Quarks".
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- DASHI CONTRIBUTION
--
-- Construct, rather than postulate, the finite linear algebra behind a local
-- admissible plaquette selector.  Four oriented slot variations are chosen so
-- that one gauge functional and one coarse-constraint functional vanish while
-- the singleton extraction functional equals an arbitrary requested scalar h.
-- The exact charge is h^2/2.
--
-- This is a literal four-slot repair model and a regression target for the
-- physical selected-background construction.  Transport through covariant
-- prefixes and the actual lattice gauge/block operators remains the next
-- physical intertwining theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

zeroQ : ℚ
zeroQ = Int.+ 0 / 1

halfQ : ℚ
halfQ = Int.+ 1 / 2

record PlaquetteVariation4 : Set where
  constructor plaquette-variation4
  field
    slot0 slot1 slot2 slot3 : ℚ

open PlaquetteVariation4 public

gaugeFunctional : PlaquetteVariation4 → ℚ
gaugeFunctional variation =
  slot0 variation + slot1 variation
  - slot2 variation - slot3 variation

constraintFunctional : PlaquetteVariation4 → ℚ
constraintFunctional variation = slot0 variation + slot2 variation

singletonExtractionFunctional : PlaquetteVariation4 → ℚ
singletonExtractionFunctional variation =
  slot0 variation - slot1 variation
  + slot2 variation - slot3 variation

variationCharge : PlaquetteVariation4 → ℚ
variationCharge variation =
  slot0 variation * slot0 variation
  + slot1 variation * slot1 variation
  + slot2 variation * slot2 variation
  + slot3 variation * slot3 variation

selectedPlaquetteVariation : ℚ → PlaquetteVariation4
selectedPlaquetteVariation h =
  plaquette-variation4
    zeroQ
    (- (halfQ * h))
    zeroQ
    (- (halfQ * h))

selectedPlaquetteVariationGaugeAdmissible :
  (h : ℚ) →
  gaugeFunctional (selectedPlaquetteVariation h) ≡ zeroQ
selectedPlaquetteVariationGaugeAdmissible h = solve (h ∷ [])

selectedPlaquetteVariationConstraintTangent :
  (h : ℚ) →
  constraintFunctional (selectedPlaquetteVariation h) ≡ zeroQ
selectedPlaquetteVariationConstraintTangent h = solve (h ∷ [])

selectedPlaquetteVariationExtractsSingleton :
  (h : ℚ) →
  singletonExtractionFunctional (selectedPlaquetteVariation h) ≡ h
selectedPlaquetteVariationExtractsSingleton h = solve (h ∷ [])

selectedPlaquetteVariationChargeExact :
  (h : ℚ) →
  variationCharge (selectedPlaquetteVariation h)
  ≡ halfQ * (h * h)
selectedPlaquetteVariationChargeExact h = solve (h ∷ [])

record LinearPlaquetteSelectionWitness (h : ℚ) : Set where
  constructor linear-plaquette-selection-witness
  field
    variation : PlaquetteVariation4
    gaugeAdmissible : gaugeFunctional variation ≡ zeroQ
    constraintTangent : constraintFunctional variation ≡ zeroQ
    extractsSingleton : singletonExtractionFunctional variation ≡ h
    chargeExact : variationCharge variation ≡ halfQ * (h * h)

open LinearPlaquetteSelectionWitness public

selectLinearPlaquetteVariation :
  (h : ℚ) → LinearPlaquetteSelectionWitness h
selectLinearPlaquetteVariation h =
  linear-plaquette-selection-witness
    (selectedPlaquetteVariation h)
    (selectedPlaquetteVariationGaugeAdmissible h)
    (selectedPlaquetteVariationConstraintTangent h)
    (selectedPlaquetteVariationExtractsSingleton h)
    (selectedPlaquetteVariationChargeExact h)

record LinearRepairModelBoundary : Set where
  constructor linear-repair-model-boundary
  field
    explicitFourSlotSelectorConstructed : Bool
    explicitFourSlotSelectorConstructedIsTrue :
      explicitFourSlotSelectorConstructed ≡ true
    gaugeAndConstraintSolvedSimultaneously : Bool
    gaugeAndConstraintSolvedSimultaneouslyIsTrue :
      gaugeAndConstraintSolvedSimultaneously ≡ true
    physicalCovariantPrefixTransportConstructed : Bool
    physicalCovariantPrefixTransportConstructedIsFalse :
      physicalCovariantPrefixTransportConstructed ≡ false

canonicalLinearRepairModelBoundary : LinearRepairModelBoundary
canonicalLinearRepairModelBoundary =
  linear-repair-model-boundary true refl true refl false refl
