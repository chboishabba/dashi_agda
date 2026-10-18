{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119ReflectionPolymerGeometryExact where

------------------------------------------------------------------------
-- CMP119 / OS REFLECTION POLYMER GEOMETRY
--
-- This is the first concrete B/E/R support classifier on the repository's
-- literal periodic four-dimensional block carrier.
--
-- It deliberately does NOT identify a CMP119 localized term with one of these
-- block polymers.  That source-to-carrier equality remains the next physical
-- seam.  The purpose here is narrower: once a source polymer has been welded
-- to `PeriodicPolymer n`, its location relative to a selected Euclidean-time
-- cut is executable and unambiguous.
--
-- A block belongs to the positive side when its zero-coordinate rank is
-- strictly below the cut.  The finite classifier is written using
--   suc(rank) <=ᵇ cut,
-- which is definitionally the strict inequality rank < cut on naturals.
-- A polymer is then classified as positive-only, negative-only, empty, or
-- genuinely crossing if it contains blocks on both sides.
--
-- Important boundary: this is OS time-plane geometry.  It is NOT Balaban's
-- "large-field boundary" predicate, and exponential localization near an RG
-- boundary is not promoted to reflection positivity here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.Base using (_≤ᵇ_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic

------------------------------------------------------------------------
-- Literal block side.
------------------------------------------------------------------------

data BlockReflectionSide : Set where
  positiveSide negativeSide : BlockReflectionSide

periodicBlockTimeRank :
  ∀ {n} → Periodic.PeriodicBlock n → Nat
periodicBlockTimeRank block =
  Periodic.cyclicRank (Periodic.blockCoordinate0 block)

periodicBlockPositiveBool :
  ∀ {n} → Nat → Periodic.PeriodicBlock n → Bool
periodicBlockPositiveBool cut block =
  suc (periodicBlockTimeRank block) ≤ᵇ cut

classifyPeriodicBlockAtCut :
  ∀ {n} → Nat → Periodic.PeriodicBlock n → BlockReflectionSide
classifyPeriodicBlockAtCut cut block with periodicBlockPositiveBool cut block
... | true = positiveSide
... | false = negativeSide

------------------------------------------------------------------------
-- Literal finite-polymer support class.
------------------------------------------------------------------------

data PolymerReflectionClass : Set where
  emptySupport positiveOnly negativeOnly crossingSupport :
    PolymerReflectionClass

extendPolymerReflectionClass :
  BlockReflectionSide → PolymerReflectionClass → PolymerReflectionClass
extendPolymerReflectionClass positiveSide emptySupport = positiveOnly
extendPolymerReflectionClass positiveSide positiveOnly = positiveOnly
extendPolymerReflectionClass positiveSide negativeOnly = crossingSupport
extendPolymerReflectionClass positiveSide crossingSupport = crossingSupport
extendPolymerReflectionClass negativeSide emptySupport = negativeOnly
extendPolymerReflectionClass negativeSide positiveOnly = crossingSupport
extendPolymerReflectionClass negativeSide negativeOnly = negativeOnly
extendPolymerReflectionClass negativeSide crossingSupport = crossingSupport

classifyPeriodicPolymerAtCut :
  ∀ {n} → Nat → Periodic.PeriodicPolymer n → PolymerReflectionClass
classifyPeriodicPolymerAtCut cut [] = emptySupport
classifyPeriodicPolymerAtCut cut (block ∷ blocks) =
  extendPolymerReflectionClass
    (classifyPeriodicBlockAtCut cut block)
    (classifyPeriodicPolymerAtCut cut blocks)

------------------------------------------------------------------------
-- Executable predicates used by the source weld.
------------------------------------------------------------------------

polymerPositiveOnly :
  ∀ {n} → Nat → Periodic.PeriodicPolymer n → Set
polymerPositiveOnly cut polymer =
  classifyPeriodicPolymerAtCut cut polymer ≡ positiveOnly

polymerNegativeOnly :
  ∀ {n} → Nat → Periodic.PeriodicPolymer n → Set
polymerNegativeOnly cut polymer =
  classifyPeriodicPolymerAtCut cut polymer ≡ negativeOnly

polymerCrossesReflectionCut :
  ∀ {n} → Nat → Periodic.PeriodicPolymer n → Set
polymerCrossesReflectionCut cut polymer =
  classifyPeriodicPolymerAtCut cut polymer ≡ crossingSupport

polymerEmptyAtReflectionCut :
  ∀ {n} → Nat → Periodic.PeriodicPolymer n → Set
polymerEmptyAtReflectionCut cut polymer =
  classifyPeriodicPolymerAtCut cut polymer ≡ emptySupport

------------------------------------------------------------------------
-- Small exact algebra used by B's sector split.
------------------------------------------------------------------------

positiveExtendsPositive :
  extendPolymerReflectionClass positiveSide positiveOnly ≡ positiveOnly
positiveExtendsPositive = refl

negativeExtendsNegative :
  extendPolymerReflectionClass negativeSide negativeOnly ≡ negativeOnly
negativeExtendsNegative = refl

positiveMeetsNegativeCrosses :
  extendPolymerReflectionClass positiveSide negativeOnly ≡ crossingSupport
positiveMeetsNegativeCrosses = refl

negativeMeetsPositiveCrosses :
  extendPolymerReflectionClass negativeSide positiveOnly ≡ crossingSupport
negativeMeetsPositiveCrosses = refl

crossingIsAbsorbingPositive :
  extendPolymerReflectionClass positiveSide crossingSupport ≡ crossingSupport
crossingIsAbsorbingPositive = refl

crossingIsAbsorbingNegative :
  extendPolymerReflectionClass negativeSide crossingSupport ≡ crossingSupport
crossingIsAbsorbingNegative = refl

------------------------------------------------------------------------
-- Source-facing status firewall.
------------------------------------------------------------------------

reflectionPolymerGeometryCompilerLevel : ProofLevel
reflectionPolymerGeometryCompilerLevel = machineChecked

-- Still required before this classifier says anything about the actual CMP119
-- E_k, R_k or B_k terms: identify every selected localized source support with
-- a literal PeriodicPolymer on the same cutoff and the selected OS time cut.
cmp119LocalizedTermsToPeriodicPolymerLevel : ProofLevel
cmp119LocalizedTermsToPeriodicPolymerLevel = conditional

-- Reflection of source activities / equality of negative and reflected
-- positive terms is independent of this geometric classification.
cmp119OneSidedActivityReflectionLevel : ProofLevel
cmp119OneSidedActivityReflectionLevel = conditional

-- Only source terms classified `crossingSupport` may require an independent
-- cross-plane PSD kernel.  This classifier does not manufacture that kernel.
cmp119CrossingPolymerKernelLevel : ProofLevel
cmp119CrossingPolymerKernelLevel = conditional
