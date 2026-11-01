module DASHI.Interop.PolarityPhaseFieldBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)

open import DASHI.Core.Prelude using (_×_; _,_; proj₁; proj₂)
import DASHI.Core.AuthorityNonPromotionCore as AuthorityNA
import DASHI.Core.CandidateOnlyCore as CandidateOnly
import DASHI.Culture.YinYangPolarityBoundary as YinYang
open import Base369 using
  ( HexTruth
  ; NonaryTruth
  ; TriTruth
  ; hex-0
  ; hex-1
  ; hex-2
  ; hex-3
  ; hex-4
  ; hex-5
  ; non-0
  ; non-1
  ; non-2
  ; non-3
  ; non-4
  ; non-5
  ; non-6
  ; non-7
  ; non-8
  ; tri-low
  ; tri-mid
  ; tri-high
  )
open import DASHI.Foundations.Base369MobiusTransport using
  ( OrientationPolarity
  ; positive
  ; negative
  ; flipOrientationPolarity
  ; hexTriadicPhase
  ; hexOrientationPolarity
  ; mobiusTransport
  )
open import DASHI.Foundations.HexTruthPolarityFactor using
  ( Polarity
  ; flipPolarity
  ; hexTruthToFactor
  ; hexFactorToTruth
  ; hexTruthToFactor-projectTri
  ; hexTruthToFactor-projectPolarity
  ; hexTruthToFactor-decodingRoundTrip
  ; hexFactorToTruth-encodingRoundTrip
  ; mobiusTransport-factors
  )

------------------------------------------------------------------------
-- Candidate-only polarity / phase bridge.
--
-- This module keeps the surface finite and local.  It uses the existing
-- 369 phase carriers, the hex/polarity factorization, and the authority
-- non-promotion core to build a typed grammar for support geometry, voxels,
-- supervoxels, waves, and superposition candidates.  No external truth,
-- support, or authority is promoted.

data YinYangPolarity : Set where
  yin : YinYangPolarity
  yang : YinYangPolarity

yinYangToPolarity : YinYangPolarity → Polarity
yinYangToPolarity yin = negative
yinYangToPolarity yang = positive

polarityToYinYang : Polarity → YinYangPolarity
polarityToYinYang negative = yin
polarityToYinYang positive = yang

yinYangToPolarity-roundTrip : ∀ p → polarityToYinYang (yinYangToPolarity p) ≡ p
yinYangToPolarity-roundTrip yin = refl
yinYangToPolarity-roundTrip yang = refl

polarityToYinYang-roundTrip :
  ∀ p → yinYangToPolarity (polarityToYinYang p) ≡ p
polarityToYinYang-roundTrip negative = refl
polarityToYinYang-roundTrip positive = refl

flipYinYang : YinYangPolarity → YinYangPolarity
flipYinYang yin = yang
flipYinYang yang = yin

flipYinYang-commutes :
  ∀ p → yinYangToPolarity (flipYinYang p) ≡ flipPolarity (yinYangToPolarity p)
flipYinYang-commutes yin = refl
flipYinYang-commutes yang = refl

------------------------------------------------------------------------
-- Local 369 support ordinals.

triTruthTo369Ordinal : TriTruth → NonaryTruth
triTruthTo369Ordinal tri-low = non-0
triTruthTo369Ordinal tri-mid = non-3
triTruthTo369Ordinal tri-high = non-6

hexTruthToProbeOrdinal : HexTruth → NonaryTruth
hexTruthToProbeOrdinal hex-0 = non-0
hexTruthToProbeOrdinal hex-1 = non-1
hexTruthToProbeOrdinal hex-2 = non-2
hexTruthToProbeOrdinal hex-3 = non-3
hexTruthToProbeOrdinal hex-4 = non-4
hexTruthToProbeOrdinal hex-5 = non-5

------------------------------------------------------------------------
-- Typed phase carrier rows.

record PhaseCarrierRow : Set where
  constructor mkPhaseCarrierRow
  field
    rowLabel :
      String

    rowTriTruth :
      TriTruth

    rowPolarity :
      Polarity

    rowYinYangPolarity :
      YinYangPolarity

    rowYinYangMatchesPolarity :
      yinYangToPolarity rowYinYangPolarity ≡ rowPolarity

    rowHexTruth :
      HexTruth

    rowFactorMatches :
      hexTruthToFactor rowHexTruth ≡ (rowTriTruth , rowPolarity)

    rowTriOrdinal :
      NonaryTruth

    rowTriOrdinalMatches :
      rowTriOrdinal ≡ triTruthTo369Ordinal rowTriTruth

    rowProbeOrdinal :
      NonaryTruth

    rowProbeOrdinalMatches :
      rowProbeOrdinal ≡ hexTruthToProbeOrdinal rowHexTruth

    rowCandidateOnly :
      Bool

    rowPromoted :
      Bool

    rowCandidateOnlyIsTrue :
      rowCandidateOnly ≡ true

    rowPromotedIsFalse :
      rowPromoted ≡ false

open PhaseCarrierRow public

phaseCarrierRowToHexTruth : PhaseCarrierRow → HexTruth
phaseCarrierRowToHexTruth = rowHexTruth

phaseCarrierRowToTriTruth : PhaseCarrierRow → TriTruth
phaseCarrierRowToTriTruth = rowTriTruth

phaseCarrierRowToPolarity : PhaseCarrierRow → Polarity
phaseCarrierRowToPolarity = rowPolarity

phaseCarrierRowToYinYang : PhaseCarrierRow → YinYangPolarity
phaseCarrierRowToYinYang = rowYinYangPolarity

phaseCarrierRowToTriOrdinal : PhaseCarrierRow → NonaryTruth
phaseCarrierRowToTriOrdinal = rowTriOrdinal

phaseCarrierRowToProbeOrdinal : PhaseCarrierRow → NonaryTruth
phaseCarrierRowToProbeOrdinal = rowProbeOrdinal

phaseCarrierRowToFactor :
  PhaseCarrierRow →
  TriTruth × Polarity
phaseCarrierRowToFactor row =
  rowTriTruth row , rowPolarity row

canonicalYangPhaseCarrierRow : PhaseCarrierRow
canonicalYangPhaseCarrierRow =
  mkPhaseCarrierRow
    "yang-phase-row"
    tri-low
    positive
    yang
    refl
    hex-0
    refl
    non-0
    refl
    non-0
    refl
    true
    false
    refl
    refl

canonicalYinPhaseCarrierRow : PhaseCarrierRow
canonicalYinPhaseCarrierRow =
  mkPhaseCarrierRow
    "yin-phase-row"
    tri-low
    negative
    yin
    refl
    hex-3
    refl
    non-0
    refl
    non-3
    refl
    true
    false
    refl
    refl

canonicalBalancedPhaseCarrierRow : PhaseCarrierRow
canonicalBalancedPhaseCarrierRow =
  mkPhaseCarrierRow
    "balanced-phase-row"
    tri-mid
    positive
    yang
    refl
    hex-1
    refl
    non-3
    refl
    non-1
    refl
    true
    false
    refl
    refl

canonicalCarrierRows : List PhaseCarrierRow
canonicalCarrierRows =
  canonicalYangPhaseCarrierRow
  ∷ canonicalYinPhaseCarrierRow
  ∷ canonicalBalancedPhaseCarrierRow
  ∷ []

canonicalYangRowFactor :
  phaseCarrierRowToFactor canonicalYangPhaseCarrierRow ≡ (tri-low , positive)
canonicalYangRowFactor = refl

canonicalYinRowFactor :
  phaseCarrierRowToFactor canonicalYinPhaseCarrierRow ≡ (tri-low , negative)
canonicalYinRowFactor = refl

canonicalBalancedRowFactor :
  phaseCarrierRowToFactor canonicalBalancedPhaseCarrierRow ≡ (tri-mid , positive)
canonicalBalancedRowFactor = refl

canonicalYangRowHex :
  phaseCarrierRowToHexTruth canonicalYangPhaseCarrierRow ≡ hex-0
canonicalYangRowHex = refl

canonicalYinRowHex :
  phaseCarrierRowToHexTruth canonicalYinPhaseCarrierRow ≡ hex-3
canonicalYinRowHex = refl

canonicalBalancedRowHex :
  phaseCarrierRowToHexTruth canonicalBalancedPhaseCarrierRow ≡ hex-1
canonicalBalancedRowHex = refl

canonicalPlusOnePhaseCarrierRow : PhaseCarrierRow
canonicalPlusOnePhaseCarrierRow =
  mkPhaseCarrierRow
    "+1-phase-row"
    tri-high
    positive
    yang
    refl
    hex-2
    refl
    non-6
    refl
    non-2
    refl
    true
    false
    refl
    refl

canonicalPlusOneRowFactor :
  phaseCarrierRowToFactor canonicalPlusOnePhaseCarrierRow ≡ (tri-high , positive)
canonicalPlusOneRowFactor = refl

canonicalPlusOneRowHex :
  phaseCarrierRowToHexTruth canonicalPlusOnePhaseCarrierRow ≡ hex-2
canonicalPlusOneRowHex = refl

phaseCarrierRowYinYangMatchesPolarity :
  ∀ row →
  yinYangToPolarity (phaseCarrierRowToYinYang row) ≡ phaseCarrierRowToPolarity row
phaseCarrierRowYinYangMatchesPolarity row =
  rowYinYangMatchesPolarity row

------------------------------------------------------------------------
-- Support geometry and voxels.

record VoxelCoordinate : Set where
  constructor mkVoxelCoordinate
  field
    x :
      Nat

    y :
      Nat

    z :
      Nat

open VoxelCoordinate public

data SupportCellKind : Set where
  supportVoxelKind : SupportCellKind
  supportSupervoxelKind : SupportCellKind
  supportWaveKind : SupportCellKind
  supportSuperpositionKind : SupportCellKind

record SupportGeometry : Set where
  constructor mkSupportGeometry
  field
    supportLabel :
      String

    supportCellKind :
      SupportCellKind

    supportCoordinate :
      VoxelCoordinate

    supportPhaseRow :
      PhaseCarrierRow

    supportDepth :
      Nat

    supportScale :
      Nat

    supportOrdinal :
      NonaryTruth

    supportOrdinalMatches :
      supportOrdinal ≡ rowTriOrdinal supportPhaseRow

    supportCandidateOnly :
      Bool

    supportPromoted :
      Bool

    supportCandidateOnlyIsTrue :
      supportCandidateOnly ≡ true

    supportPromotedIsFalse :
      supportPromoted ≡ false

open SupportGeometry public

canonicalYangSupportGeometry : SupportGeometry
canonicalYangSupportGeometry =
  mkSupportGeometry
    "yang-support-voxel"
    supportVoxelKind
    (mkVoxelCoordinate zero zero zero)
    canonicalYangPhaseCarrierRow
    zero
    (suc zero)
    non-0
    refl
    true
    false
    refl
    refl

canonicalYinSupportGeometry : SupportGeometry
canonicalYinSupportGeometry =
  mkSupportGeometry
    "yin-support-voxel"
    supportVoxelKind
    (mkVoxelCoordinate (suc zero) zero zero)
    canonicalYinPhaseCarrierRow
    (suc zero)
    (suc zero)
    non-0
    refl
    true
    false
    refl
    refl

canonicalBalancedSupportGeometry : SupportGeometry
canonicalBalancedSupportGeometry =
  mkSupportGeometry
    "balanced-support-voxel"
    supportVoxelKind
    (mkVoxelCoordinate zero (suc zero) zero)
    canonicalBalancedPhaseCarrierRow
    (suc zero)
    (suc (suc zero))
    non-3
    refl
    true
    false
    refl
    refl

canonicalPlusOneSupportGeometry : SupportGeometry
canonicalPlusOneSupportGeometry =
  mkSupportGeometry
    "+1-support-voxel"
    supportVoxelKind
    (mkVoxelCoordinate (suc (suc zero)) zero zero)
    canonicalPlusOnePhaseCarrierRow
    (suc (suc zero))
    (suc (suc (suc zero)))
    non-6
    refl
    true
    false
    refl
    refl

------------------------------------------------------------------------
-- Supervoxel grammar.

record Supervoxel : Set where
  constructor mkSupervoxel
  field
    supervoxelLabel :
      String

    baseVoxel :
      SupportGeometry

    shellVoxel :
      SupportGeometry

    shadowVoxel :
      SupportGeometry

    supervoxelPhaseRow :
      PhaseCarrierRow

    supervoxelOrdinal :
      NonaryTruth

    supervoxelOrdinalMatches :
      supervoxelOrdinal ≡ rowTriOrdinal supervoxelPhaseRow

    supervoxelCandidateOnly :
      Bool

    supervoxelPromoted :
      Bool

    supervoxelCandidateOnlyIsTrue :
      supervoxelCandidateOnly ≡ true

    supervoxelPromotedIsFalse :
      supervoxelPromoted ≡ false

open Supervoxel public

canonicalYinYangSupervoxel : Supervoxel
canonicalYinYangSupervoxel =
  mkSupervoxel
    "yin-yang-supervoxel"
    canonicalYinSupportGeometry
    canonicalBalancedSupportGeometry
    canonicalYangSupportGeometry
    canonicalBalancedPhaseCarrierRow
    non-3
    refl
    true
    false
    refl
    refl

canonicalYinSupervoxel : Supervoxel
canonicalYinSupervoxel =
  mkSupervoxel
    "yin-supervoxel"
    canonicalYinSupportGeometry
    canonicalYinSupportGeometry
    canonicalBalancedSupportGeometry
    canonicalYinPhaseCarrierRow
    non-0
    refl
    true
    false
    refl
    refl

canonicalYangSupervoxel : Supervoxel
canonicalYangSupervoxel =
  mkSupervoxel
    "yang-supervoxel"
    canonicalYangSupportGeometry
    canonicalYangSupportGeometry
    canonicalBalancedSupportGeometry
    canonicalYangPhaseCarrierRow
    non-0
    refl
    true
    false
    refl
    refl

canonicalBalancedSupervoxel : Supervoxel
canonicalBalancedSupervoxel =
  mkSupervoxel
    "balanced-supervoxel"
    canonicalBalancedSupportGeometry
    canonicalBalancedSupportGeometry
    canonicalYinSupportGeometry
    canonicalBalancedPhaseCarrierRow
    non-3
    refl
    true
    false
    refl
    refl

canonicalPlusOneSupervoxel : Supervoxel
canonicalPlusOneSupervoxel =
  mkSupervoxel
    "+1-supervoxel"
    canonicalPlusOneSupportGeometry
    canonicalBalancedSupportGeometry
    canonicalYinSupportGeometry
    canonicalPlusOnePhaseCarrierRow
    non-6
    refl
    true
    false
    refl
    refl

------------------------------------------------------------------------
-- Wave and superposition grammar.

data WaveBlendMode : Set where
  constructiveWaveMode : WaveBlendMode
  counterWaveMode : WaveBlendMode
  standingWaveMode : WaveBlendMode
  braidedWaveMode : WaveBlendMode

canonicalWaveBlendModes : List WaveBlendMode
canonicalWaveBlendModes =
  constructiveWaveMode
  ∷ counterWaveMode
  ∷ standingWaveMode
  ∷ braidedWaveMode
  ∷ []

record WaveCandidateMixture : Set where
  constructor mkWaveCandidateMixture
  field
    waveLabel :
      String

    waveBlendMode :
      WaveBlendMode

    leftSupervoxel :
      Supervoxel

    rightSupervoxel :
      Supervoxel

    wavePhase :
      TriTruth

    wavePolarity :
      Polarity

    waveHexTruth :
      HexTruth

    waveFactorMatches :
      hexTruthToFactor waveHexTruth ≡ (wavePhase , wavePolarity)

    waveOrdinal :
      NonaryTruth

    waveOrdinalMatches :
      waveOrdinal ≡ hexTruthToProbeOrdinal waveHexTruth

    waveCandidateOnly :
      Bool

    wavePromoted :
      Bool

    waveCandidateOnlyIsTrue :
      waveCandidateOnly ≡ true

    wavePromotedIsFalse :
      wavePromoted ≡ false

open WaveCandidateMixture public

canonicalYinYangWave : WaveCandidateMixture
canonicalYinYangWave =
  mkWaveCandidateMixture
    "yin-yang-wave"
    braidedWaveMode
    canonicalYinSupervoxel
    canonicalYangSupervoxel
    tri-mid
    positive
    hex-1
    refl
    non-1
    refl
    true
    false
    refl
    refl

canonicalCounterWave : WaveCandidateMixture
canonicalCounterWave =
  mkWaveCandidateMixture
    "counter-wave"
    counterWaveMode
    canonicalYangSupervoxel
    canonicalYinSupervoxel
    tri-low
    negative
    hex-3
    refl
    non-3
    refl
    true
    false
    refl
    refl

canonicalStandingWave : WaveCandidateMixture
canonicalStandingWave =
  mkWaveCandidateMixture
    "standing-wave"
    standingWaveMode
    canonicalBalancedSupervoxel
    canonicalBalancedSupervoxel
    tri-mid
    positive
    hex-1
    refl
    non-1
    refl
    true
    false
    refl
    refl

record SuperpositionCandidate : Set where
  constructor mkSuperpositionCandidate
  field
    superpositionLabel :
      String

    foregroundWave :
      WaveCandidateMixture

    backgroundWave :
      WaveCandidateMixture

    superpositionSupport :
      SupportGeometry

    superpositionPhase :
      TriTruth

    superpositionPolarity :
      Polarity

    superpositionHexTruth :
      HexTruth

    superpositionFactorMatches :
      hexTruthToFactor superpositionHexTruth ≡
      (superpositionPhase , superpositionPolarity)

    superpositionOrdinal :
      NonaryTruth

    superpositionOrdinalMatches :
      superpositionOrdinal ≡ hexTruthToProbeOrdinal superpositionHexTruth

    superpositionCandidateOnly :
      Bool

    superpositionPromoted :
      Bool

    superpositionCandidateOnlyIsTrue :
      superpositionCandidateOnly ≡ true

    superpositionPromotedIsFalse :
      superpositionPromoted ≡ false

open SuperpositionCandidate public

canonicalYinYangSuperposition : SuperpositionCandidate
canonicalYinYangSuperposition =
  mkSuperpositionCandidate
    "yin-yang-superposition"
    canonicalYinYangWave
    canonicalCounterWave
    canonicalBalancedSupportGeometry
    tri-mid
    positive
    hex-1
    refl
    non-1
    refl
    true
    false
    refl
    refl

------------------------------------------------------------------------
-- Explicit local field grammar.

data LocalFieldSurfaceKind : Set where
  plusOneLocalFieldKind : LocalFieldSurfaceKind
  seedLocalFieldKind : LocalFieldSurfaceKind
  carryLocalFieldKind : LocalFieldSurfaceKind
  adapterLocalFieldKind : LocalFieldSurfaceKind
  bodyLocalFieldKind : LocalFieldSurfaceKind
  boundaryLocalFieldKind : LocalFieldSurfaceKind
  supportLocalFieldKind : LocalFieldSurfaceKind

localFieldSurfaceCount : Nat
localFieldSurfaceCount = suc (suc (suc (suc (suc (suc (suc zero))))))

record LocalFieldSurface : Set where
  constructor mkLocalFieldSurface
  field
    localFieldSurfaceLabel :
      String

    localFieldSurfaceKind :
      LocalFieldSurfaceKind

    localFieldPhaseRow :
      PhaseCarrierRow

    localFieldSupportGeometry :
      SupportGeometry

    localFieldSupervoxel :
      Supervoxel

    localFieldHexTruth :
      HexTruth

    localFieldFactorMatches :
      hexTruthToFactor localFieldHexTruth ≡
      (rowTriTruth localFieldPhaseRow , rowPolarity localFieldPhaseRow)

    localFieldOrdinal :
      NonaryTruth

    localFieldOrdinalMatches :
      localFieldOrdinal ≡ hexTruthToProbeOrdinal localFieldHexTruth

    localFieldCandidateOnly :
      Bool

    localFieldPromoted :
      Bool

    localFieldCandidateOnlyIsTrue :
      localFieldCandidateOnly ≡ true

    localFieldPromotedIsFalse :
      localFieldPromoted ≡ false

open LocalFieldSurface public

canonicalPlusOneLocalFieldSurface : LocalFieldSurface
canonicalPlusOneLocalFieldSurface =
  mkLocalFieldSurface
    "+1-local-field"
    plusOneLocalFieldKind
    canonicalPlusOnePhaseCarrierRow
    canonicalPlusOneSupportGeometry
    canonicalPlusOneSupervoxel
    hex-2
    refl
    non-2
    refl
    true
    false
    refl
    refl

canonicalSeedLocalFieldSurface : LocalFieldSurface
canonicalSeedLocalFieldSurface =
  mkLocalFieldSurface
    "seed-local-field"
    seedLocalFieldKind
    canonicalBalancedPhaseCarrierRow
    canonicalBalancedSupportGeometry
    canonicalBalancedSupervoxel
    hex-1
    refl
    non-1
    refl
    true
    false
    refl
    refl

canonicalCarryLocalFieldSurface : LocalFieldSurface
canonicalCarryLocalFieldSurface =
  mkLocalFieldSurface
    "carry-local-field"
    carryLocalFieldKind
    canonicalYinPhaseCarrierRow
    canonicalYinSupportGeometry
    canonicalYinSupervoxel
    hex-3
    refl
    non-3
    refl
    true
    false
    refl
    refl

canonicalAdapterLocalFieldSurface : LocalFieldSurface
canonicalAdapterLocalFieldSurface =
  mkLocalFieldSurface
    "adapter-local-field"
    adapterLocalFieldKind
    canonicalYangPhaseCarrierRow
    canonicalYangSupportGeometry
    canonicalYangSupervoxel
    hex-0
    refl
    non-0
    refl
    true
    false
    refl
    refl

canonicalBodyLocalFieldSurface : LocalFieldSurface
canonicalBodyLocalFieldSurface =
  mkLocalFieldSurface
    "body-local-field"
    bodyLocalFieldKind
    canonicalPlusOnePhaseCarrierRow
    canonicalPlusOneSupportGeometry
    canonicalPlusOneSupervoxel
    hex-2
    refl
    non-2
    refl
    true
    false
    refl
    refl

canonicalBoundaryLocalFieldSurface : LocalFieldSurface
canonicalBoundaryLocalFieldSurface =
  mkLocalFieldSurface
    "boundary-local-field"
    boundaryLocalFieldKind
    canonicalYinPhaseCarrierRow
    canonicalYinSupportGeometry
    canonicalYinSupervoxel
    hex-3
    refl
    non-3
    refl
    true
    false
    refl
    refl

canonicalSupportLocalFieldSurface : LocalFieldSurface
canonicalSupportLocalFieldSurface =
  mkLocalFieldSurface
    "support-local-field"
    supportLocalFieldKind
    canonicalYangPhaseCarrierRow
    canonicalYangSupportGeometry
    canonicalYangSupervoxel
    hex-0
    refl
    non-0
    refl
    true
    false
    refl
    refl

canonicalLocalFieldSurfaces : List LocalFieldSurface
canonicalLocalFieldSurfaces =
  canonicalPlusOneLocalFieldSurface
  ∷ canonicalSeedLocalFieldSurface
  ∷ canonicalCarryLocalFieldSurface
  ∷ canonicalAdapterLocalFieldSurface
  ∷ canonicalBodyLocalFieldSurface
  ∷ canonicalBoundaryLocalFieldSurface
  ∷ canonicalSupportLocalFieldSurface
  ∷ []

canonicalLocalFieldGrammarSummary : String
canonicalLocalFieldGrammarSummary =
  "Candidate-only local field grammar names +1, seed, carry, adapter, body, boundary, and support as explicit finite 369/polarity/voxel/supervoxel surfaces."

record LocalFieldGrammar : Set where
  constructor mkLocalFieldGrammar
  field
    localFieldGrammarLabel :
      String

    localFieldGrammarSurfaces :
      List LocalFieldSurface

    localFieldGrammarSurfaceCount :
      Nat

    localFieldGrammarSurfaceCountIsSeven :
      localFieldGrammarSurfaceCount ≡ localFieldSurfaceCount

    localFieldGrammarCandidateOnly :
      Bool

    localFieldGrammarCandidateOnlyIsTrue :
      localFieldGrammarCandidateOnly ≡ true

    localFieldGrammarPromoted :
      Bool

    localFieldGrammarPromotedIsFalse :
      localFieldGrammarPromoted ≡ false

    localFieldGrammarSummary :
      String

open LocalFieldGrammar public

canonicalLocalFieldGrammar : LocalFieldGrammar
canonicalLocalFieldGrammar =
  mkLocalFieldGrammar
    "polarity-phase-local-field-grammar"
    canonicalLocalFieldSurfaces
    localFieldSurfaceCount
    refl
    true
    refl
    false
    refl
    canonicalLocalFieldGrammarSummary

canonicalLocalFieldSurfacesAreCanonical :
  localFieldGrammarSurfaces canonicalLocalFieldGrammar ≡ canonicalLocalFieldSurfaces
canonicalLocalFieldSurfacesAreCanonical =
  refl

canonicalLocalFieldGrammarSurfaceCountIsSeven :
  localFieldGrammarSurfaceCount canonicalLocalFieldGrammar ≡ localFieldSurfaceCount
canonicalLocalFieldGrammarSurfaceCountIsSeven =
  refl

canonicalLocalFieldGrammarCandidateOnlyIsTrue :
  localFieldGrammarCandidateOnly canonicalLocalFieldGrammar ≡ true
canonicalLocalFieldGrammarCandidateOnlyIsTrue =
  refl

canonicalLocalFieldGrammarPromotedIsFalse :
  localFieldGrammarPromoted canonicalLocalFieldGrammar ≡ false
canonicalLocalFieldGrammarPromotedIsFalse =
  refl

canonicalLocalFieldGrammarSummaryIsCanonical :
  localFieldGrammarSummary canonicalLocalFieldGrammar ≡
  canonicalLocalFieldGrammarSummary
canonicalLocalFieldGrammarSummaryIsCanonical =
  refl

------------------------------------------------------------------------
-- Candidate-only and blocked-authority governance.

bridgeCandidateOnlyRow : CandidateOnly.CandidateOnlyRow
bridgeCandidateOnlyRow =
  CandidateOnly.mkCandidateOnlyRow
    "polarity-phase-field-bridge"
    "lane-5"
    "DASHI/Interop/PolarityPhaseFieldBridge"
    CandidateOnly.bridgeCandidateKind
    CandidateOnly.bridgeCandidateOnlyStatus
    "candidate-only bridge from yin/yang polarity into 369 phase rows, voxel support geometry, explicit +1/seed/carry/adapter/body/boundary/support local field grammar, wave mixtures, and superposition candidates"
    "blocked authority, no promotion, no external theorem or runtime authority; local field grammar stays candidate-only"

bridgeCandidateOnlyReceipt : CandidateOnly.CandidateOnlyReceipt bridgeCandidateOnlyRow
bridgeCandidateOnlyReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    bridgeCandidateOnlyRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

bridgeBlockedAuthorityKinds : List AuthorityNA.AuthorityKind
bridgeBlockedAuthorityKinds =
  AuthorityNA.canonicalAuthorityKinds

record BridgeGovernance : Set where
  constructor mkBridgeGovernance
  field
    governanceCandidateRow :
      CandidateOnly.CandidateOnlyRow

    governanceCandidateReceipt :
      CandidateOnly.CandidateOnlyReceipt governanceCandidateRow

    governanceAuthorityBundle :
      AuthorityNA.AuthorityNonPromotionBundle

    governanceBlockedAuthorityKinds :
      List AuthorityNA.AuthorityKind

    governanceBlockedAuthorityKindsAreCanonical :
      governanceBlockedAuthorityKinds ≡ bridgeBlockedAuthorityKinds

    governanceBlockedAuthorityKindsFalse :
      AuthorityNA.AllAuthorityKindsFalse
        governanceAuthorityBundle
        governanceBlockedAuthorityKinds

    governanceCandidateOnly :
      Bool

    governancePromoted :
      Bool

    governanceCandidateOnlyIsTrue :
      governanceCandidateOnly ≡ true

    governancePromotedIsFalse :
      governancePromoted ≡ false

open BridgeGovernance public

canonicalBridgeGovernance : BridgeGovernance
canonicalBridgeGovernance =
  mkBridgeGovernance
    bridgeCandidateOnlyRow
    bridgeCandidateOnlyReceipt
    AuthorityNA.canonicalAuthorityNonPromotionBundle
    bridgeBlockedAuthorityKinds
    refl
    (AuthorityNA.proveAllAuthorityKindsFalse
      AuthorityNA.canonicalAuthorityNonPromotionBundle
      bridgeBlockedAuthorityKinds)
    true
    false
    refl
    refl

------------------------------------------------------------------------
-- Top-level bridge surface.

record PolarityPhaseFieldBridge : Set where
  constructor mkPolarityPhaseFieldBridge
  field
    bridgeLabel :
      String

    bridgePhaseRow :
      PhaseCarrierRow

    bridgeLocalFieldGrammar :
      LocalFieldGrammar

    bridgeSupportGeometry :
      SupportGeometry

    bridgeSupervoxel :
      Supervoxel

    bridgeWaveMixture :
      WaveCandidateMixture

    bridgeSuperpositionCandidate :
      SuperpositionCandidate

    bridgePolarityBoundary :
      YinYang.YinYangPolarityBoundaryReceipt

    bridgePolarityBoundaryIsCanonical :
      bridgePolarityBoundary ≡ YinYang.canonicalYinYangPolarityBoundaryReceipt

    bridgeGovernance :
      BridgeGovernance

    bridgeCandidateOnly :
      Bool

    bridgePromoted :
      Bool

    bridgeCandidateOnlyIsTrue :
      bridgeCandidateOnly ≡ true

    bridgePromotedIsFalse :
      bridgePromoted ≡ false

    bridgeMobiusTransportMatches :
      phaseCarrierRowToHexTruth bridgePhaseRow ≡
      mobiusTransport (phaseCarrierRowToHexTruth canonicalYangPhaseCarrierRow)

open PolarityPhaseFieldBridge public

canonicalPolarityPhaseFieldBridge : PolarityPhaseFieldBridge
canonicalPolarityPhaseFieldBridge =
  mkPolarityPhaseFieldBridge
    "polarity-phase-field-bridge"
    canonicalYinPhaseCarrierRow
    canonicalLocalFieldGrammar
    canonicalYinSupportGeometry
    canonicalYinSupervoxel
    canonicalYinYangWave
    canonicalYinYangSuperposition
    YinYang.canonicalYinYangPolarityBoundaryReceipt
    refl
    canonicalBridgeGovernance
    true
    false
    refl
    refl
    refl

bridgePhaseRowFactor :
  phaseCarrierRowToFactor (bridgePhaseRow canonicalPolarityPhaseFieldBridge) ≡
  (tri-low , negative)
bridgePhaseRowFactor = refl

bridgeLocalFieldGrammarSurfacesAreCanonical :
  localFieldGrammarSurfaces
    (bridgeLocalFieldGrammar canonicalPolarityPhaseFieldBridge)
  ≡
  canonicalLocalFieldSurfaces
bridgeLocalFieldGrammarSurfacesAreCanonical =
  refl

bridgeLocalFieldGrammarSurfaceCountIsSeven :
  localFieldGrammarSurfaceCount
    (bridgeLocalFieldGrammar canonicalPolarityPhaseFieldBridge)
  ≡
  localFieldSurfaceCount
bridgeLocalFieldGrammarSurfaceCountIsSeven =
  refl

bridgeLocalFieldGrammarCandidateOnlyIsTrue :
  localFieldGrammarCandidateOnly
    (bridgeLocalFieldGrammar canonicalPolarityPhaseFieldBridge)
  ≡
  true
bridgeLocalFieldGrammarCandidateOnlyIsTrue =
  refl

bridgeLocalFieldGrammarPromotedIsFalse :
  localFieldGrammarPromoted
    (bridgeLocalFieldGrammar canonicalPolarityPhaseFieldBridge)
  ≡
  false
bridgeLocalFieldGrammarPromotedIsFalse =
  refl

bridgeLocalFieldGrammarSummaryIsCanonical :
  localFieldGrammarSummary
    (bridgeLocalFieldGrammar canonicalPolarityPhaseFieldBridge)
  ≡
  canonicalLocalFieldGrammarSummary
bridgeLocalFieldGrammarSummaryIsCanonical =
  refl

bridgePhaseRowHex :
  phaseCarrierRowToHexTruth (bridgePhaseRow canonicalPolarityPhaseFieldBridge) ≡
  hex-3
bridgePhaseRowHex = refl

bridgePhaseRowMobius :
  phaseCarrierRowToHexTruth canonicalYinPhaseCarrierRow ≡
  mobiusTransport (phaseCarrierRowToHexTruth canonicalYangPhaseCarrierRow)
bridgePhaseRowMobius = refl

bridgeSupportGeometryOrdinal :
  supportOrdinal (bridgeSupportGeometry canonicalPolarityPhaseFieldBridge) ≡ non-0
bridgeSupportGeometryOrdinal = refl

bridgeSupervoxelOrdinal :
  supervoxelOrdinal (bridgeSupervoxel canonicalPolarityPhaseFieldBridge) ≡ non-0
bridgeSupervoxelOrdinal = refl

bridgeWaveOrdinal :
  waveOrdinal (bridgeWaveMixture canonicalPolarityPhaseFieldBridge) ≡ non-1
bridgeWaveOrdinal = refl

bridgeSuperpositionOrdinal :
  superpositionOrdinal (bridgeSuperpositionCandidate canonicalPolarityPhaseFieldBridge) ≡ non-1
bridgeSuperpositionOrdinal = refl

bridgeGovernanceCandidateOnly :
  CandidateOnly.candidateOnly
    (governanceCandidateRow (bridgeGovernance canonicalPolarityPhaseFieldBridge)) ≡ true
bridgeGovernanceCandidateOnly = refl

bridgeGovernanceNoPromotion :
  CandidateOnly.promoted
    (governanceCandidateRow (bridgeGovernance canonicalPolarityPhaseFieldBridge)) ≡ false
bridgeGovernanceNoPromotion = refl

bridgeGovernanceBlockedKindsFalse :
  AuthorityNA.AllAuthorityKindsFalse
    (governanceAuthorityBundle (bridgeGovernance canonicalPolarityPhaseFieldBridge))
    (governanceBlockedAuthorityKinds (bridgeGovernance canonicalPolarityPhaseFieldBridge))
bridgeGovernanceBlockedKindsFalse =
  governanceBlockedAuthorityKindsFalse canonicalBridgeGovernance

canonicalPolarityPhaseFieldBridgeSummary : String
canonicalPolarityPhaseFieldBridgeSummary =
  "Candidate-only polarity/phase bridge with explicit +1, seed, carry, adapter, body, boundary, and support local field grammar; authority stays blocked."

canonicalPolarityPhaseFieldBridgeSummaryIsCanonical :
  canonicalPolarityPhaseFieldBridgeSummary ≡
  "Candidate-only polarity/phase bridge with explicit +1, seed, carry, adapter, body, boundary, and support local field grammar; authority stays blocked."
canonicalPolarityPhaseFieldBridgeSummaryIsCanonical =
  refl

bridgeGovernanceBlockedKindsAreCanonical :
  governanceBlockedAuthorityKinds (bridgeGovernance canonicalPolarityPhaseFieldBridge) ≡
  bridgeBlockedAuthorityKinds
bridgeGovernanceBlockedKindsAreCanonical = refl

bridgeCandidateOnlyReceiptIsCanonical :
  bridgeCandidateOnlyReceipt ≡
  CandidateOnly.canonicalCandidateOnlyReceipt
    bridgeCandidateOnlyRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
bridgeCandidateOnlyReceiptIsCanonical = refl

bridgePolicySummary : String
bridgePolicySummary =
  "candidate-only yin/yang polarity bridge with 369 phase rows, explicit local field grammar, voxel/supervoxel support geometry, wave/superposition candidates, and blocked authority governance"

bridgePolicySummaryIsCanonical :
  bridgePolicySummary ≡
  "candidate-only yin/yang polarity bridge with 369 phase rows, explicit local field grammar, voxel/supervoxel support geometry, wave/superposition candidates, and blocked authority governance"
bridgePolicySummaryIsCanonical =
  refl
