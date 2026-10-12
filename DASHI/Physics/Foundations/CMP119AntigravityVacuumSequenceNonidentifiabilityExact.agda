{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityVacuumSequenceNonidentifiabilityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym)

import DASHI.Physics.Foundations.CMP119AntigravityCanonicalSourceSectorActionExact as Canonical
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4

------------------------------------------------------------------------
-- VACUUM-SEQUENCE NON-IDENTIFIABILITY FROM THE CURRENT SOURCE VIEW
--
-- IMPORTANT COORDINATE CORRECTION
--
-- LocalizedAction has two rational coordinates:
--
--   plaquetteCoefficientField   -- Wilson/plaquette-relevant coefficient
--   irrelevantCoefficientField  -- the non-plaquette remainder coordinate.
--
-- A source vacuum/normalization constant must not be identified with the
-- plaquette coefficient merely because both inhabit LocalizedAction.  The
-- canonical constant-action embedding is
--
--   irrelevantAction V = localizedAction 0 V.
--
-- Therefore the non-identifiability witness below varies only the remainder /
-- constant coordinate: 0 versus 1.  Every coupling, density, background,
-- fluctuation and E/R/B coordinate remains definitionally unchanged.
--
-- This proves that the declared current source view does not determine that
-- constant coordinate.  A separate published-source theorem must still show
-- that the selected CMP119 vacuum-energy/normalization term is encoded by this
-- constant-action coordinate on the physical source.
------------------------------------------------------------------------

replaceVacuum :
  ∀ {Density Background Fluctuation} →
  Canonical.CMP119NormalizedSectorSource Density Background Fluctuation →
  (Nat → T4.LocalizedAction) →
  Canonical.CMP119NormalizedSectorSource Density Background Fluctuation
replaceVacuum source newVacuum = record
  { Canonical.CMP119NormalizedSectorSource.terminalScale =
      Canonical.terminalScale source
  ; Canonical.CMP119NormalizedSectorSource.couplingAt =
      Canonical.couplingAt source
  ; Canonical.CMP119NormalizedSectorSource.densityAt =
      Canonical.densityAt source
  ; Canonical.CMP119NormalizedSectorSource.backgroundAt =
      Canonical.backgroundAt source
  ; Canonical.CMP119NormalizedSectorSource.fluctuationAt =
      Canonical.fluctuationAt source
  ; Canonical.CMP119NormalizedSectorSource.eAt = Canonical.eAt source
  ; Canonical.CMP119NormalizedSectorSource.rAt = Canonical.rAt source
  ; Canonical.CMP119NormalizedSectorSource.bAt = Canonical.bAt source
  ; Canonical.CMP119NormalizedSectorSource.vacuumAt = newVacuum
  }

zeroVacuumSequence : Nat → T4.LocalizedAction
zeroVacuumSequence _ = T4.irrelevantAction 0ℚ

unitVacuumSequence : Nat → T4.LocalizedAction
unitVacuumSequence _ = T4.irrelevantAction 1ℚ

zeroVacuumSource :
  ∀ {Density Background Fluctuation} →
  Canonical.CMP119NormalizedSectorSource Density Background Fluctuation →
  Canonical.CMP119NormalizedSectorSource Density Background Fluctuation
zeroVacuumSource source = replaceVacuum source zeroVacuumSequence

unitVacuumSource :
  ∀ {Density Background Fluctuation} →
  Canonical.CMP119NormalizedSectorSource Density Background Fluctuation →
  Canonical.CMP119NormalizedSectorSource Density Background Fluctuation
unitVacuumSource source = replaceVacuum source unitVacuumSequence

vacuumConstantProjection :
  ∀ {Density Background Fluctuation} →
  Canonical.CMP119NormalizedSectorSource Density Background Fluctuation →
  Nat → ℚ
vacuumConstantProjection source scale =
  T4.irrelevantCoefficientField (Canonical.vacuumAt source scale)

-- Compatibility name retained for downstream consumers.  "Projected vacuum"
-- now means the constant/remainder coordinate, NOT the plaquette coefficient.
projectedVacuum :
  ∀ {Density Background Fluctuation} →
  Canonical.CMP119NormalizedSectorSource Density Background Fluctuation →
  Nat → ℚ
projectedVacuum = vacuumConstantProjection

sameCouplingAfterVacuumReplacement :
  ∀ {Density Background Fluctuation}
    (source : Canonical.CMP119NormalizedSectorSource Density Background Fluctuation)
    replacement scale →
  Canonical.couplingAt (replaceVacuum source replacement) scale
  ≡ Canonical.couplingAt source scale
sameCouplingAfterVacuumReplacement source replacement scale = refl

sameDensityAfterVacuumReplacement :
  ∀ {Density Background Fluctuation}
    (source : Canonical.CMP119NormalizedSectorSource Density Background Fluctuation)
    replacement scale →
  Canonical.densityAt (replaceVacuum source replacement) scale
  ≡ Canonical.densityAt source scale
sameDensityAfterVacuumReplacement source replacement scale = refl

sameBackgroundAfterVacuumReplacement :
  ∀ {Density Background Fluctuation}
    (source : Canonical.CMP119NormalizedSectorSource Density Background Fluctuation)
    replacement scale →
  Canonical.backgroundAt (replaceVacuum source replacement) scale
  ≡ Canonical.backgroundAt source scale
sameBackgroundAfterVacuumReplacement source replacement scale = refl

sameFluctuationAfterVacuumReplacement :
  ∀ {Density Background Fluctuation}
    (source : Canonical.CMP119NormalizedSectorSource Density Background Fluctuation)
    replacement scale →
  Canonical.fluctuationAt (replaceVacuum source replacement) scale
  ≡ Canonical.fluctuationAt source scale
sameFluctuationAfterVacuumReplacement source replacement scale = refl

sameESectorAfterVacuumReplacement :
  ∀ {Density Background Fluctuation}
    (source : Canonical.CMP119NormalizedSectorSource Density Background Fluctuation)
    replacement scale →
  Canonical.eAt (replaceVacuum source replacement) scale
  ≡ Canonical.eAt source scale
sameESectorAfterVacuumReplacement source replacement scale = refl

sameRSectorAfterVacuumReplacement :
  ∀ {Density Background Fluctuation}
    (source : Canonical.CMP119NormalizedSectorSource Density Background Fluctuation)
    replacement scale →
  Canonical.rAt (replaceVacuum source replacement) scale
  ≡ Canonical.rAt source scale
sameRSectorAfterVacuumReplacement source replacement scale = refl

sameBSectorAfterVacuumReplacement :
  ∀ {Density Background Fluctuation}
    (source : Canonical.CMP119NormalizedSectorSource Density Background Fluctuation)
    replacement scale →
  Canonical.bAt (replaceVacuum source replacement) scale
  ≡ Canonical.bAt source scale
sameBSectorAfterVacuumReplacement source replacement scale = refl

zeroVacuumProjectsZero :
  ∀ {Density Background Fluctuation}
    (source : Canonical.CMP119NormalizedSectorSource Density Background Fluctuation)
    scale →
  projectedVacuum (zeroVacuumSource source) scale ≡ 0ℚ
zeroVacuumProjectsZero source scale = refl

unitVacuumProjectsOne :
  ∀ {Density Background Fluctuation}
    (source : Canonical.CMP119NormalizedSectorSource Density Background Fluctuation)
    scale →
  projectedVacuum (unitVacuumSource source) scale ≡ 1ℚ
unitVacuumProjectsOne source scale = refl

zeroBelowOne : 0ℚ < 1ℚ
zeroBelowOne = ℚP.positive⁻¹ 1ℚ

zeroNotOne : 0ℚ ≢ 1ℚ
zeroNotOne equality =
  ℚP.<-irrefl refl
    (subst (λ value → 0ℚ < value) (sym equality) zeroBelowOne)

projectedVacuumSequencesDiffer :
  ∀ {Density Background Fluctuation}
    (source : Canonical.CMP119NormalizedSectorSource Density Background Fluctuation)
    scale →
  projectedVacuum (zeroVacuumSource source) scale
  ≢ projectedVacuum (unitVacuumSource source) scale
projectedVacuumSequencesDiffer source scale equality =
  zeroNotOne
    (subst
      (λ value → value ≡ 1ℚ)
      (zeroVacuumProjectsZero source scale)
      (subst
        (λ value →
          projectedVacuum (zeroVacuumSource source) scale ≡ value)
        (unitVacuumProjectsOne source scale)
        equality))

record VacuumSequenceNonidentifiabilityWitness
    {Density Background Fluctuation : Set}
    (source : Canonical.CMP119NormalizedSectorSource Density Background Fluctuation)
    : Set where
  constructor vacuum-sequence-nonidentifiability-witness
  field
    left right : Canonical.CMP119NormalizedSectorSource Density Background Fluctuation
    sameCoupling : ∀ scale → Canonical.couplingAt left scale ≡ Canonical.couplingAt right scale
    sameDensity : ∀ scale → Canonical.densityAt left scale ≡ Canonical.densityAt right scale
    sameBackground : ∀ scale → Canonical.backgroundAt left scale ≡ Canonical.backgroundAt right scale
    sameFluctuation : ∀ scale → Canonical.fluctuationAt left scale ≡ Canonical.fluctuationAt right scale
    sameE : ∀ scale → Canonical.eAt left scale ≡ Canonical.eAt right scale
    sameR : ∀ scale → Canonical.rAt left scale ≡ Canonical.rAt right scale
    sameB : ∀ scale → Canonical.bAt left scale ≡ Canonical.bAt right scale
    differentProjectedVacuum : ∀ scale → projectedVacuum left scale ≢ projectedVacuum right scale

couplingAndERBDoNotDetermineVacuum :
  ∀ {Density Background Fluctuation}
    (source : Canonical.CMP119NormalizedSectorSource Density Background Fluctuation) →
  VacuumSequenceNonidentifiabilityWitness source
couplingAndERBDoNotDetermineVacuum source =
  vacuum-sequence-nonidentifiability-witness
    (zeroVacuumSource source)
    (unitVacuumSource source)
    (λ _ → refl)
    (λ _ → refl)
    (λ _ → refl)
    (λ _ → refl)
    (λ _ → refl)
    (λ _ → refl)
    (λ _ → refl)
    (projectedVacuumSequencesDiffer source)

plaquetteProjectorIsVacuumConstantCoordinate : Bool
plaquetteProjectorIsVacuumConstantCoordinate = false

constantRemainderCoordinateUsedForVacuumCollision : Bool
constantRemainderCoordinateUsedForVacuumCollision = true

publishedVacuumConstantEncodingStillRequired : Bool
publishedVacuumConstantEncodingStillRequired = true

sourceVacuumSequenceRequiresIndependentPhysicalPayment : Bool
sourceVacuumSequenceRequiresIndependentPhysicalPayment = true
