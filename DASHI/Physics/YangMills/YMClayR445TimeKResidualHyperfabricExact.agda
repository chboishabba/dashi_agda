module DASHI.Physics.YangMills.YMClayR445TimeKResidualHyperfabricExact where

------------------------------------------------------------------------
-- P0 / #1444 -> #1536: NATIVE time × k INDEXED RESIDUAL HYPERFABRIC.
--
-- Do NOT interpret "R445" as a time value or a renormalisation stage.
-- It is a chronological proof-iteration OWNER. Here time t is a
-- Euclidean-source label, and k is an INDEPENDENT refinement-stage
-- label. Neither is a coordinate of the finite C4/C2 periodic torus.
--
-- The ALREADY ORIGINAL #1444 selected side-four -> side-two time chart is
--    C4  <-> C2(coarse phase) × C2(fine even/odd remainder)
-- with explicit zero and reversible carry. In particular a ONE-fine-
-- site step retains the second component; it is not a failed block
-- identity once this residual is kept. A TWO-step shift descends.
--
-- Already-owned abstract k-stage interface:
--   DASHI.Core.MultiscaleMDL.ResidualCodec, split, join, join-split.
-- Already-owned wave ZERO/SIGN (not a physical YM identification):
--   DASHI.Physics.WaveAlgorithmLift.Trit / tritInvolution / zeroWave.
-- Already-owned physical limit square residual semantics:
--   DASHI.Physics.Limits.PhysicsLimitCommutingSquare.
--
-- This module proves a finite EXACT C4 chart and transport coherence;
-- it does NOT assert the original SU(N) field R445 has been equipped
-- with a physical finite->continuum wave limit or common H_OS.
-- Original native Fin.combine positive-bond source identity and
-- continuum k-stage measure/semigroup compatibility remain open.
-- SOURCE-WRITTEN; local Agda compiler/kernel not available.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.YMClayR445SelectedTimeReflectionForwardExact as Geo
import DASHI.Core.MultiscaleMDL as MDL
import DASHI.Physics.YangMills.YMClayR445OriginalAxialBondParityInjectiveExact as OriginalCodec
import DASHI.Physics.YangMills.YMClayR445OriginalNativeParityPairWeldExact as OriginalNativeOrigin
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as OriginalBond
import DASHI.Physics.YangMills.YMClayNativeBlockedPositiveHolonomyGaugeExact as OriginalBlock
import DASHI.Physics.WaveAlgorithmLift as Wave
import DASHI.Physics.YangMills.YMClayR445CanonicalBondPermutationCodecExact as OriginalBondResiduals
import DASHI.Physics.ShiftDiscreteWaveStep as FiniteWave


C2 : Set
C2 = Geo.C2

C4 : Set
C4 = Geo.C4

zero₂ : C2
zero₂ = Torus.zeroᵢ

one₂ : C2
one₂ = Torus.sucᵢ Torus.zeroᵢ

zero₄ : C4
zero₄ = Torus.zeroᵢ

one₄ : C4
one₄ = Torus.sucᵢ Torus.zeroᵢ

two₄ : C4
two₄ = Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)

three₄ : C4
three₄ = Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))

-- Preserve BOTH coarse time and its source-owned even/odd remainder.
-- This is the finite chart of the ACTUAL 2-link R445 time geometry.
NativeTimeResidual : Set
NativeTimeResidual = Torus.Product C2 C2

-- The coordinate maps are the ORIGINAL R445 proof owners already on
-- master/#1444, NOT a second invented parity calculation.
splitNativeTime : C4 → NativeTimeResidual
splitNativeTime fine =
  Torus.pair (OriginalCodec.coarse fine) (OriginalCodec.phase fine)

joinNativeTime : NativeTimeResidual → C4
joinNativeTime (Torus.pair coarse residue) =
  OriginalCodec.coord coarse residue

joinSplitNativeTime : ∀ fine →
  joinNativeTime (splitNativeTime fine) ≡ fine
joinSplitNativeTime Torus.zeroᵢ = refl
joinSplitNativeTime (Torus.sucᵢ Torus.zeroᵢ) = refl
joinSplitNativeTime (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)) = refl
joinSplitNativeTime
  (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))) = refl

splitJoinNativeTime : ∀ pair →
  splitNativeTime (joinNativeTime pair) ≡ pair
splitJoinNativeTime (Torus.pair Torus.zeroᵢ Torus.zeroᵢ) = refl
splitJoinNativeTime
  (Torus.pair Torus.zeroᵢ (Torus.sucᵢ Torus.zeroᵢ)) = refl
splitJoinNativeTime
  (Torus.pair (Torus.sucᵢ Torus.zeroᵢ) Torus.zeroᵢ) = refl
splitJoinNativeTime
  (Torus.pair (Torus.sucᵢ Torus.zeroᵢ)
              (Torus.sucᵢ Torus.zeroᵢ)) = refl

zeroIsARealNativeState :
  splitNativeTime zero₄ ≡ Torus.pair zero₂ zero₂
zeroIsARealNativeState = refl

evenOriginHasZeroRemainder :
  ∀ coarse →
  Torus.second (splitNativeTime (Geo.evenTime coarse)) ≡ zero₂
evenOriginHasZeroRemainder Torus.zeroᵢ = refl
evenOriginHasZeroRemainder
  (Torus.sucᵢ Torus.zeroᵢ) = refl

-- First reuse the already-original native 16-site Fin.combine theorem.
-- In particular, this is NOT a fresh outstanding original-R445 block
-- origin proof. The only payment below is matching the two separately
-- named original even-origin coordinate presentations.
originalEvenMatchesSelectedEven :
  ∀ coarse → OriginalCodec.even coarse ≡ Geo.evenTime coarse
originalEvenMatchesSelectedEven Torus.zeroᵢ = refl
originalEvenMatchesSelectedEven (Torus.sucᵢ Torus.zeroᵢ) = refl

originalEvenSiteMatchesGeometry :
  ∀ site →
  OriginalNativeOrigin.originalR445EvenFineSite site ≡
  Geo.evenCoarseOrigin site
originalEvenSiteMatchesGeometry
  (Torus.pair (Torus.pair t x) (Torus.pair y z))
  rewrite originalEvenMatchesSelectedEven t
        | originalEvenMatchesSelectedEven x
        | originalEvenMatchesSelectedEven y
        | originalEvenMatchesSelectedEven z = refl

originalNativeBlockOriginIsSelectedGeometry :
  ∀ {Value : Set} (group : OriginalBond.ExactLinkGroup Value)
    (site : Geo.CoarseSite) →
  OriginalBlock.fineBlockOrigin {m = 1} {l = 1} group site ≡
  Geo.evenCoarseOrigin site
originalNativeBlockOriginIsSelectedGeometry group site =
  trans
    (OriginalNativeOrigin.originalR445NativeOriginIsEvenSite site group)
    (originalEvenSiteMatchesGeometry site)

-- Even/odd is an ACTUAL residual bit of C4/C2, distinct from
-- signed/zero ternary evidence. Do not identify it with SU(N) phase.
shiftFineTimeByOne : C4 → C4
shiftFineTimeByOne Torus.zeroᵢ = one₄
shiftFineTimeByOne (Torus.sucᵢ Torus.zeroᵢ) = two₄
shiftFineTimeByOne
  (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)) = three₄
shiftFineTimeByOne
  (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))) = zero₄

-- The non-descending one-fine-step shift has an EXACT coarse carry.
-- It never discards the odd remainder.
carryOneFineStep : NativeTimeResidual → NativeTimeResidual
carryOneFineStep (Torus.pair coarse Torus.zeroᵢ) =
  Torus.pair coarse one₂
carryOneFineStep (Torus.pair coarse (Torus.sucᵢ Torus.zeroᵢ)) =
  Torus.pair (Geo.shiftCoarseTimeByOne coarse) zero₂

oneFineStepKeepsCarryAndResidual :
  ∀ fine →
  splitNativeTime (shiftFineTimeByOne fine) ≡
  carryOneFineStep (splitNativeTime fine)
oneFineStepKeepsCarryAndResidual Torus.zeroᵢ = refl
oneFineStepKeepsCarryAndResidual
  (Torus.sucᵢ Torus.zeroᵢ) = refl
oneFineStepKeepsCarryAndResidual
  (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)) = refl
oneFineStepKeepsCarryAndResidual
  (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))) = refl

twoFineStepsExactlyDescend :
  ∀ pair →
  carryOneFineStep (carryOneFineStep pair)
  ≡
  Torus.pair
    (Geo.shiftCoarseTimeByOne (Torus.first pair))
    (Torus.second pair)
twoFineStepsExactlyDescend
  (Torus.pair Torus.zeroᵢ Torus.zeroᵢ) = refl
twoFineStepsExactlyDescend
  (Torus.pair Torus.zeroᵢ (Torus.sucᵢ Torus.zeroᵢ)) = refl
twoFineStepsExactlyDescend
  (Torus.pair (Torus.sucᵢ Torus.zeroᵢ) Torus.zeroᵢ) = refl
twoFineStepsExactlyDescend
  (Torus.pair (Torus.sucᵢ Torus.zeroᵢ)
              (Torus.sucᵢ Torus.zeroᵢ)) = refl

-- Labels are genuinely INDEPENDENT:
--   t = source/OS1 Euclidean-time index
--   k = changing-cutoff/refinement stage
--   finiteTime = original C4 chart coordinate at one selected stage
--   signedPhase = balanced ternary wave SYMBOL, retaining the zero mode.
-- The latter is optional upstream encoding, NOT a physical SU(N) scalar.
record TimeKFiniteWaveCell : Set where
  constructor timeKFiniteWaveCell
  field
    time : Nat
    stage : Nat
    finiteTime : C4
    signedPhase : Wave.Trit

open TimeKFiniteWaveCell public

recoveredTimeKNativeCell :
  ∀ cell →
  joinNativeTime (splitNativeTime (finiteTime cell))
    ≡ finiteTime cell
recoveredTimeKNativeCell cell =
  joinSplitNativeTime (finiteTime cell)

waveZeroIsNotDeleted :
  Wave.tritInvolution Wave.zero ≡ Wave.zero
waveZeroIsNotDeleted = refl

waveSignedOrientationIsInvolutive :
  ∀ sign →
  Wave.tritInvolution (Wave.tritInvolution sign) ≡ sign
waveSignedOrientationIsInvolutive =
  Wave.tritInvolution²

-- This is the FULL ORIGINAL SOURCE residual-bond enumeration, not
-- merely a parity address and not a new approximation to the Yang-Mills
-- Gibbs measure. The original owner proves 128 selected+896 residual
-- fine positive bonds are disjoint, duplicate-free and complete.
originalAllFineBondSelectedResidual :
  Torus.FiniteEnumeration (Torus.PositiveBond 4)
originalAllFineBondSelectedResidual =
  OriginalBondResiduals.originalR445PairResidualFinite

-- Native finite symbolic wave encoding is a separate producer.
-- It includes the actual zero-amplitude mode and both signs.
-- We do NOT infer that this finite trit encodes the original SU(N)
-- physical Wilson wavefunction or its analytic continuum limit.
indexedFiniteWave : TimeKFiniteWaveCell → FiniteWave.DiscreteWave
indexedFiniteWave cell =
  Wave.encodeTritWave (signedPhase cell)

indexedZeroModeIsExactFiniteZeroWave :
  indexedFiniteWave
    (timeKFiniteWaveCell zero zero zero₄ Wave.zero)
  ≡ Wave.zeroWave
indexedZeroModeIsExactFiniteZeroWave = refl

-- The original generically scale-indexed residual codec ALREADY
-- proves exact reconstruction at EVERY k, with no assumption that
-- k is a fine torus coordinate or that residual vanishes.
timeKScaleResidualRoundTrip :
  (tower : MDL.MultiscaleCarrier)
  (codec : MDL.ResidualCodec tower)
  (t k : Nat)
  (sourceAtStage : MDL.Carrier tower (suc k)) →
  MDL.join codec (MDL.split codec sourceAtStage)
    ≡ sourceAtStage
timeKScaleResidualRoundTrip tower codec t k sourceAtStage =
  MDL.join-split codec sourceAtStage

-- Future actual physical instantiation must supply a same-object
-- embedding from the chosen YM stage-k Wilson source and time index
-- to MDL.Carrier tower k, a SOURCE-preserving reconstruction,
-- k-aware phase/wave map and proven controlled/vanishing residual.
-- The existing Balaban T5 E1 Gram and R278 continuum compilers are
-- the physical endpoint; generic finite wave symbols alone are not.
