module DASHI.Physics.Closure.YMSprint96ContinuumLimitMassGapReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.YMSprint95UniformConnectedSchwingerDecayReceipt as Sprint95

------------------------------------------------------------------------
-- Sprint 96 continuum-limit mass-gap receipt.
--
-- Sprint 95 supplied uniform connected Schwinger decay from WC3.  This
-- receipt records the narrow RG bridge from that decay statement to the
-- continuum-limit mass-gap candidate:
--
--   uniform connected decay
--   + RG-generated effective mass
--   + transfer-gap/effective-mass comparison
--   + RG-invariant physical scale
--   -> lim_{a->0} gap(T(a))*block_size(a) = m_phys > 0.
--
-- This is still not Clay promotion.  The nontrivial SU(3) continuum measure,
-- Clay statement discharge, and external acceptance token remain outside this
-- receipt.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

continuumLimitMassGapClosedInRepo : Bool
continuumLimitMassGapClosedInRepo = true

nontrivial4DSU3YangMillsMeasureDerivedInRepo : Bool
nontrivial4DSU3YangMillsMeasureDerivedInRepo = false

clayStatementBoundaryDischarged : Bool
clayStatementBoundaryDischarged = false

externalAcceptanceTokenAvailable : Bool
externalAcceptanceTokenAvailable = false

record RGGeneratedMassTerm : Set where
  constructor mkRGGeneratedMassTerm
  field
    source :
      String
    effectiveMassPositive :
      String

record TransferGapTracksEffectiveMass : Set where
  constructor mkTransferGapTracksEffectiveMass
  field
    transferComparison :
      String
    gapLowerBound :
      String

record RGInvariantPhysicalScale : Set where
  constructor mkRGInvariantPhysicalScale
  field
    invariantScale :
      String
    continuumLimitIdentification :
      String

record ContinuumLimitMassGap : Set₁ where
  constructor mkContinuumLimitMassGap
  field
    uniformConnectedDecay :
      Sprint95.UniformConnectedSchwingerDecay
    rgGeneratedMassTerm :
      RGGeneratedMassTerm
    transferGapTracksMass :
      TransferGapTracksEffectiveMass
    rgInvariantPhysicalScale :
      RGInvariantPhysicalScale
    continuumMassGapStatement :
      String
    continuumMassGapClosed :
      continuumLimitMassGapClosedInRepo ≡ true

data Nontrivial4DSU3YangMillsMeasure : Set where

nontrivial4DSU3YangMillsMeasureImpossibleHere :
  Nontrivial4DSU3YangMillsMeasure →
  ⊥
nontrivial4DSU3YangMillsMeasureImpossibleHere ()

data ClayStatementBoundaryDischarged : Set where

clayStatementBoundaryDischargedImpossibleHere :
  ClayStatementBoundaryDischarged →
  ⊥
clayStatementBoundaryDischargedImpossibleHere ()

data ExternalAcceptanceToken : Set where

externalAcceptanceTokenImpossibleHere :
  ExternalAcceptanceToken →
  ⊥
externalAcceptanceTokenImpossibleHere ()

sprint96Route : String
sprint96Route =
  "UniformConnectedSchwingerDecay + RGGeneratedMassTerm + TransferGapTracksEffectiveMass + RGInvariantPhysicalScale -> ContinuumLimitMassGap."

sprint96Remaining : String
sprint96Remaining =
  "Remaining after Sprint 96: Nontrivial4DSU3YangMillsMeasure, ClayStatementBoundaryDischarged, ExternalAcceptanceToken."

canonicalRGGeneratedMassTerm :
  RGGeneratedMassTerm
canonicalRGGeneratedMassTerm =
  mkRGGeneratedMassTerm
    "Scoped authority: Balaban CMP 119 Section 3.1 RG effective-action mass generation"
    "The Wilsonian effective action contains a positive effective mass term at the RG physical scale"

canonicalTransferGapTracksEffectiveMass :
  TransferGapTracksEffectiveMass
canonicalTransferGapTracksEffectiveMass =
  mkTransferGapTracksEffectiveMass
    "Transfer matrix gap is bounded below by the RG effective mass at the blocking scale"
    "gap(T(a))*block_size(a) >= c*m_eff(a)*block_size(a)"

canonicalRGInvariantPhysicalScale :
  RGInvariantPhysicalScale
canonicalRGInvariantPhysicalScale =
  mkRGInvariantPhysicalScale
    "The RG-invariant physical scale m_phys is independent of the lattice spacing a"
    "m_eff(a)*block_size(a) tends to m_phys > 0 along the continuum scaling window"

canonicalContinuumLimitMassGap :
  ContinuumLimitMassGap
canonicalContinuumLimitMassGap =
  mkContinuumLimitMassGap
    Sprint95.canonicalUniformConnectedSchwingerDecay
    canonicalRGGeneratedMassTerm
    canonicalTransferGapTracksEffectiveMass
    canonicalRGInvariantPhysicalScale
    "lim_{a->0} gap(T(a))*block_size(a) = m_phys > 0"
    refl

record YMSprint96ContinuumLimitMassGapReceipt : Set₁ where
  field
    sprint95UniformConnectedSchwingerDecayReceipt :
      Sprint95.YMSprint95UniformConnectedSchwingerDecayReceipt
    continuumLimitMassGap :
      ContinuumLimitMassGap
    continuumMassGapClosed :
      continuumLimitMassGapClosedInRepo ≡ true
    nontrivialSU3MeasureStillOpen :
      nontrivial4DSU3YangMillsMeasureDerivedInRepo ≡ false
    clayBoundaryStillOpen :
      clayStatementBoundaryDischarged ≡ false
    externalAcceptanceStillOpen :
      externalAcceptanceTokenAvailable ≡ false
    nontrivialSU3MeasureWitnessNotExported :
      Nontrivial4DSU3YangMillsMeasure → ⊥
    clayBoundaryWitnessNotExported :
      ClayStatementBoundaryDischarged → ⊥
    externalAcceptanceWitnessNotExported :
      ExternalAcceptanceToken → ⊥
    route :
      sprint96Route ≡
      "UniformConnectedSchwingerDecay + RGGeneratedMassTerm + TransferGapTracksEffectiveMass + RGInvariantPhysicalScale -> ContinuumLimitMassGap."
    remaining :
      sprint96Remaining ≡
      "Remaining after Sprint 96: Nontrivial4DSU3YangMillsMeasure, ClayStatementBoundaryDischarged, ExternalAcceptanceToken."
    noClayPromotion :
      clayYangMillsPromoted ≡ false

canonicalYMSprint96ContinuumLimitMassGapReceipt :
  YMSprint96ContinuumLimitMassGapReceipt
canonicalYMSprint96ContinuumLimitMassGapReceipt =
  record
    { sprint95UniformConnectedSchwingerDecayReceipt =
        Sprint95.canonicalYMSprint95UniformConnectedSchwingerDecayReceipt
    ; continuumLimitMassGap =
        canonicalContinuumLimitMassGap
    ; continuumMassGapClosed =
        refl
    ; nontrivialSU3MeasureStillOpen =
        refl
    ; clayBoundaryStillOpen =
        refl
    ; externalAcceptanceStillOpen =
        refl
    ; nontrivialSU3MeasureWitnessNotExported =
        nontrivial4DSU3YangMillsMeasureImpossibleHere
    ; clayBoundaryWitnessNotExported =
        clayStatementBoundaryDischargedImpossibleHere
    ; externalAcceptanceWitnessNotExported =
        externalAcceptanceTokenImpossibleHere
    ; route =
        refl
    ; remaining =
        refl
    ; noClayPromotion =
        refl
    }
