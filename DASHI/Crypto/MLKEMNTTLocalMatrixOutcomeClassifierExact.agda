module DASHI.Crypto.MLKEMNTTLocalMatrixOutcomeClassifierExact where

------------------------------------------------------------------------
-- ML-KEM NTT: PROOF-REFINED LOCAL MATRIX OUTCOME CLASSIFIER
--
-- Primary cryptographic source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- FIPS 203, 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- PURPOSE
--
-- Discharge the logical seam left open by
-- MLKEMNTTLocalOutcomeBudgetExact.  A local residue is classified from three
-- proof-bearing pieces of evidence:
--
--   * whether the transformed perturbation is zero or active,
--   * whether the local public map is regular (zero-reflecting) or singular,
--   * whether the local public output is zero or survives.
--
-- A regular map carries the exact local law
--
--   map x = 0  ->  x = 0.
--
-- Therefore the branch
--
--   active + regular + killed
--
-- is impossible by contradiction and has no resulting LocalResidueOutcome.
-- This file is intentionally generic in the carrier types.  The next FIPS
-- layer only has to instantiate the regular-map witness for the actual local
-- quadratic/module matrix.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)

open import DASHI.Crypto.MLKEMNTTLocalOutcomeBudgetExact using
  ( LocalResidueOutcome
  ; inactiveRegular
  ; inactiveSingular
  ; activeSurvivesRegular
  ; activeSurvivesSingular
  ; activeKilledSingular
  )

Not : Set → Set
Not A = A → ⊥

------------------------------------------------------------------------
-- Proof-bearing zero/activity/output statuses.
------------------------------------------------------------------------

data LocalActivity {X : Set} (zeroX x : X) : Set where
  inactive : x ≡ zeroX → LocalActivity zeroX x
  active : Not (x ≡ zeroX) → LocalActivity zeroX x

data LocalOutputStatus {Y : Set} (zeroY y : Y) : Set where
  killed : y ≡ zeroY → LocalOutputStatus zeroY y
  survives : Not (y ≡ zeroY) → LocalOutputStatus zeroY y

------------------------------------------------------------------------
-- A regular local map is represented by zero reflection.  For a linear map,
-- injectivity implies this immediately; conversely zero reflection is exactly
-- the fragment needed by the support theorem.
------------------------------------------------------------------------

record ZeroReflectingMap (X Y : Set) : Set where
  constructor zero-reflecting-map
  field
    zeroX : X
    zeroY : Y
    map : X → Y
    reflectsZero :
      (x : X) →
      map x ≡ zeroY →
      x ≡ zeroX

open ZeroReflectingMap public

data LocalMatrixStatus {X Y : Set}
  (zeroX : X) (zeroY : Y) (map : X → Y) : Set where
  regular :
    ((x : X) → map x ≡ zeroY → x ≡ zeroX) →
    LocalMatrixStatus zeroX zeroY map
  singular : LocalMatrixStatus zeroX zeroY map

------------------------------------------------------------------------
-- Generic classifier.
------------------------------------------------------------------------

classifyLocalResidueOutcome :
  ∀ {X Y : Set}
  (zeroX : X) →
  (zeroY : Y) →
  (map : X → Y) →
  (x : X) →
  LocalActivity zeroX x →
  LocalMatrixStatus zeroX zeroY map →
  LocalOutputStatus zeroY (map x) →
  LocalResidueOutcome
classifyLocalResidueOutcome zeroX zeroY map x
  (inactive xZero) (regular reflects) output = inactiveRegular
classifyLocalResidueOutcome zeroX zeroY map x
  (inactive xZero) singular output = inactiveSingular
classifyLocalResidueOutcome zeroX zeroY map x
  (active xNonZero) (regular reflects) (survives outputNonZero) =
  activeSurvivesRegular
classifyLocalResidueOutcome zeroX zeroY map x
  (active xNonZero) singular (survives outputNonZero) =
  activeSurvivesSingular
classifyLocalResidueOutcome zeroX zeroY map x
  (active xNonZero) singular (killed outputZero) =
  activeKilledSingular
classifyLocalResidueOutcome zeroX zeroY map x
  (active xNonZero) (regular reflects) (killed outputZero) =
  ⊥-elim (xNonZero (reflects x outputZero))

------------------------------------------------------------------------
-- Direct constructor from a packaged zero-reflecting map.
------------------------------------------------------------------------

regularStatusFromZeroReflectingMap :
  ∀ {X Y : Set} →
  (local : ZeroReflectingMap X Y) →
  LocalMatrixStatus
    (ZeroReflectingMap.zeroX local)
    (ZeroReflectingMap.zeroY local)
    (ZeroReflectingMap.map local)
regularStatusFromZeroReflectingMap local =
  regular (ZeroReflectingMap.reflectsZero local)

regularActiveKilledImpossible :
  ∀ {X Y : Set}
  (zeroX : X) →
  (zeroY : Y) →
  (map : X → Y) →
  (reflects : (x : X) → map x ≡ zeroY → x ≡ zeroX) →
  (x : X) →
  Not (x ≡ zeroX) →
  map x ≡ zeroY →
  ⊥
regularActiveKilledImpossible zeroX zeroY map reflects x xNonZero outputZero =
  xNonZero (reflects x outputZero)

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
--
-- This module proves no FIPS rank fact.  It proves that once the actual local
-- matrix is shown zero-reflecting, the forbidden active/regular/killed branch
-- is eliminated constructively.  The remaining FIPS-specific task is to build
-- ZeroReflectingMap witnesses from BaseCase/quadratic-field or full local
-- module-matrix invertibility.
------------------------------------------------------------------------
