module DASHI.Physics.YangMills.YMClayR445Base2ThreeAxis369FibreBIDIExact where

------------------------------------------------------------------------
-- P0 YM x existing binary/base-2 369: SAME original side-four bonds.
--
-- The original 1024 original positive Wilson links have a reversible
-- binary address: (original coarse positive bond, axial phase, three
-- transverse-parity bits).  1024 = 64*2*8.
--
-- 000 transverse parity is exactly the ORIGINAL R445 128 selected
-- fine links, not a newly defined Wilson block.  Seven other sheets
-- give the 896 untouched spectator links. This is a coordinate codec,
-- not a disintegration, an SU(N) character or a physical field estimate.
--
-- Existing original owners:
--   YMClayR445OriginalAxialBondParityInjectiveExact
--   YMClayR445CanonicalBondPermutationCodecExact
--   YMClayOriginalF19R445Full1024LabelsP0Exact
-- Existing binary/ternary owners:
--   Base369BinaryTernaryRefinement (2^a * 3^b)
--   BinaryBalancedTernarySubcarrierExact (bit -> signed nonzero trit)
--
-- SOURCE-WRITTEN candidate; pinned Agda kernel not run.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as T
import DASHI.Physics.YangMills.YMClayR445OriginalAxialBondParityInjectiveExact as R445
import DASHI.Foundations.Base369BinaryTernaryRefinement as Resolution
import DASHI.ComputerScience.BinaryBalancedTernarySubcarrierExact as SignedBit
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Physics.WaveAlgorithmLift as Wave
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as OriginalGauge
open import Agda.Builtin.Nat using (Nat)
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as OriginalBond
import Data.Vec.Base as Vec
open import Data.Empty using (⊥)

Bit : Set
Bit = T.CyclicIndex 2

record ThreeTransverseBits : Set where
  constructor transverse
  field
    t0 t1 t2 : Bit

open ThreeTransverseBits public

zeroTransverse : ThreeTransverseBits
zeroTransverse = transverse T.zeroᵢ T.zeroᵢ T.zeroᵢ

record OriginalBinaryAddress : Set where
  constructor originalAddress
  field
    nativeCoarse : R445.CoarseBond
    nativeAxialPhase : Bit
    transverseResidual : ThreeTransverseBits

open OriginalBinaryAddress public

-- The four cases are the ORIGINAL orientation and side-two site carrier,
-- not a synthetic Fin 1024 substituting for the native original bonds.
encodeOriginalFine : OriginalBinaryAddress → R445.FineBond
encodeOriginalFine
    (originalAddress
      (T.pair (T.pair (T.pair a b) (T.pair c d)) T.zeroᵢ)
      p (transverse u v w)) =
  T.pair
    (T.pair (T.pair (R445.coord a p) (R445.coord b u))
      (T.pair (R445.coord c v) (R445.coord d w)))
    T.zeroᵢ
encodeOriginalFine
    (originalAddress
      (T.pair (T.pair (T.pair a b) (T.pair c d))
        (T.sucᵢ T.zeroᵢ))
      p (transverse u v w)) =
  T.pair
    (T.pair (T.pair (R445.coord a u) (R445.coord b p))
      (T.pair (R445.coord c v) (R445.coord d w)))
    (T.sucᵢ T.zeroᵢ)
encodeOriginalFine
    (originalAddress
      (T.pair (T.pair (T.pair a b) (T.pair c d))
        (T.sucᵢ (T.sucᵢ T.zeroᵢ)))
      p (transverse u v w)) =
  T.pair
    (T.pair (T.pair (R445.coord a u) (R445.coord b v))
      (T.pair (R445.coord c p) (R445.coord d w)))
    (T.sucᵢ (T.sucᵢ T.zeroᵢ))
encodeOriginalFine
    (originalAddress
      (T.pair (T.pair (T.pair a b) (T.pair c d))
        (T.sucᵢ (T.sucᵢ (T.sucᵢ T.zeroᵢ))))
      p (transverse u v w)) =
  T.pair
    (T.pair (T.pair (R445.coord a u) (R445.coord b v))
      (T.pair (R445.coord c w) (R445.coord d p)))
    (T.sucᵢ (T.sucᵢ (T.sucᵢ T.zeroᵢ)))

decodeOriginalFine : R445.FineBond → OriginalBinaryAddress
decodeOriginalFine
    (T.pair (T.pair (T.pair x0 x1) (T.pair x2 x3)) T.zeroᵢ) =
  originalAddress
    (T.pair
      (T.pair
        (T.pair (R445.coarse x0) (R445.coarse x1))
        (T.pair (R445.coarse x2) (R445.coarse x3)))
      T.zeroᵢ)
    (R445.phase x0)
    (transverse (R445.phase x1) (R445.phase x2) (R445.phase x3))
decodeOriginalFine
    (T.pair (T.pair (T.pair x0 x1) (T.pair x2 x3))
      (T.sucᵢ T.zeroᵢ)) =
  originalAddress
    (T.pair
      (T.pair
        (T.pair (R445.coarse x0) (R445.coarse x1))
        (T.pair (R445.coarse x2) (R445.coarse x3)))
      (T.sucᵢ T.zeroᵢ))
    (R445.phase x1)
    (transverse (R445.phase x0) (R445.phase x2) (R445.phase x3))
decodeOriginalFine
    (T.pair (T.pair (T.pair x0 x1) (T.pair x2 x3))
      (T.sucᵢ (T.sucᵢ T.zeroᵢ))) =
  originalAddress
    (T.pair
      (T.pair
        (T.pair (R445.coarse x0) (R445.coarse x1))
        (T.pair (R445.coarse x2) (R445.coarse x3)))
      (T.sucᵢ (T.sucᵢ T.zeroᵢ)))
    (R445.phase x2)
    (transverse (R445.phase x0) (R445.phase x1) (R445.phase x3))
decodeOriginalFine
    (T.pair (T.pair (T.pair x0 x1) (T.pair x2 x3))
      (T.sucᵢ (T.sucᵢ (T.sucᵢ T.zeroᵢ)))) =
  originalAddress
    (T.pair
      (T.pair
        (T.pair (R445.coarse x0) (R445.coarse x1))
        (T.pair (R445.coarse x2) (R445.coarse x3)))
      (T.sucᵢ (T.sucᵢ (T.sucᵢ T.zeroᵢ))))
    (R445.phase x3)
    (transverse (R445.phase x0) (R445.phase x1) (R445.phase x2))

-- Source already proves coarse/phase left inverses; right inverse
-- of the 2-bit coordinate constructor is only four finite cases.
originalCoordReconstructs :
  (x : R445.Quad) →
  R445.coord (R445.coarse x) (R445.phase x) ≡ x
originalCoordReconstructs T.zeroᵢ = refl
originalCoordReconstructs (T.sucᵢ T.zeroᵢ) = refl
originalCoordReconstructs (T.sucᵢ (T.sucᵢ T.zeroᵢ)) = refl
originalCoordReconstructs
    (T.sucᵢ (T.sucᵢ (T.sucᵢ T.zeroᵢ))) = refl

originalFineRoundTrip :
  (fine : R445.FineBond) →
  encodeOriginalFine (decodeOriginalFine fine) ≡ fine
originalFineRoundTrip
    (T.pair (T.pair (T.pair x0 x1) (T.pair x2 x3)) T.zeroᵢ)
  rewrite originalCoordReconstructs x0
        | originalCoordReconstructs x1
        | originalCoordReconstructs x2
        | originalCoordReconstructs x3 = refl
originalFineRoundTrip
    (T.pair (T.pair (T.pair x0 x1) (T.pair x2 x3))
      (T.sucᵢ T.zeroᵢ))
  rewrite originalCoordReconstructs x0
        | originalCoordReconstructs x1
        | originalCoordReconstructs x2
        | originalCoordReconstructs x3 = refl
originalFineRoundTrip
    (T.pair (T.pair (T.pair x0 x1) (T.pair x2 x3))
      (T.sucᵢ (T.sucᵢ T.zeroᵢ)))
  rewrite originalCoordReconstructs x0
        | originalCoordReconstructs x1
        | originalCoordReconstructs x2
        | originalCoordReconstructs x3 = refl
originalFineRoundTrip
    (T.pair (T.pair (T.pair x0 x1) (T.pair x2 x3))
      (T.sucᵢ (T.sucᵢ (T.sucᵢ T.zeroᵢ))))
  rewrite originalCoordReconstructs x0
        | originalCoordReconstructs x1
        | originalCoordReconstructs x2
        | originalCoordReconstructs x3 = refl

originalAddressRoundTrip :
  (address : OriginalBinaryAddress) →
  decodeOriginalFine (encodeOriginalFine address) ≡ address
originalAddressRoundTrip
    (originalAddress
      (T.pair (T.pair (T.pair a b) (T.pair c d)) T.zeroᵢ)
      p (transverse u v w))
  rewrite R445.coarseCoordRoundTrip a p
        | R445.coarseCoordRoundTrip b u
        | R445.coarseCoordRoundTrip c v
        | R445.coarseCoordRoundTrip d w
        | R445.phaseCoordRoundTrip a p
        | R445.phaseCoordRoundTrip b u
        | R445.phaseCoordRoundTrip c v
        | R445.phaseCoordRoundTrip d w = refl
originalAddressRoundTrip
    (originalAddress
      (T.pair (T.pair (T.pair a b) (T.pair c d))
        (T.sucᵢ T.zeroᵢ))
      p (transverse u v w))
  rewrite R445.coarseCoordRoundTrip a u
        | R445.coarseCoordRoundTrip b p
        | R445.coarseCoordRoundTrip c v
        | R445.coarseCoordRoundTrip d w
        | R445.phaseCoordRoundTrip a u
        | R445.phaseCoordRoundTrip b p
        | R445.phaseCoordRoundTrip c v
        | R445.phaseCoordRoundTrip d w = refl
originalAddressRoundTrip
    (originalAddress
      (T.pair (T.pair (T.pair a b) (T.pair c d))
        (T.sucᵢ (T.sucᵢ T.zeroᵢ)))
      p (transverse u v w))
  rewrite R445.coarseCoordRoundTrip a u
        | R445.coarseCoordRoundTrip b v
        | R445.coarseCoordRoundTrip c p
        | R445.coarseCoordRoundTrip d w
        | R445.phaseCoordRoundTrip a u
        | R445.phaseCoordRoundTrip b v
        | R445.phaseCoordRoundTrip c p
        | R445.phaseCoordRoundTrip d w = refl
originalAddressRoundTrip
    (originalAddress
      (T.pair (T.pair (T.pair a b) (T.pair c d))
        (T.sucᵢ (T.sucᵢ (T.sucᵢ T.zeroᵢ))))
      p (transverse u v w))
  rewrite R445.coarseCoordRoundTrip a u
        | R445.coarseCoordRoundTrip b v
        | R445.coarseCoordRoundTrip c w
        | R445.coarseCoordRoundTrip d p
        | R445.phaseCoordRoundTrip a u
        | R445.phaseCoordRoundTrip b v
        | R445.phaseCoordRoundTrip c w
        | R445.phaseCoordRoundTrip d p = refl

-- SAME native original R445 bond for every one of its 64 coarse
-- directions and two axial phases. Nothing is guessed from 128=2^7.
selectedZeroSheetIsOriginalR445 :
  (coarse : R445.CoarseBond) (p : Bit) →
  encodeOriginalFine (originalAddress coarse p zeroTransverse)
    ≡ R445.originalR445SelectedFineBond coarse p
selectedZeroSheetIsOriginalR445
    (T.pair (T.pair (T.pair a b) (T.pair c d)) T.zeroᵢ) p = refl
selectedZeroSheetIsOriginalR445
    (T.pair (T.pair (T.pair a b) (T.pair c d))
      (T.sucᵢ T.zeroᵢ)) p = refl
selectedZeroSheetIsOriginalR445
    (T.pair (T.pair (T.pair a b) (T.pair c d))
      (T.sucᵢ (T.sucᵢ T.zeroᵢ))) p = refl
selectedZeroSheetIsOriginalR445
    (T.pair (T.pair (T.pair a b) (T.pair c d))
      (T.sucᵢ (T.sucᵢ (T.sucᵢ T.zeroᵢ)))) p = refl

originalR445SelectedDecodesToZeroSheet :
  (coarse : R445.CoarseBond) (p : Bit) →
  decodeOriginalFine (R445.originalR445SelectedFineBond coarse p)
    ≡ originalAddress coarse p zeroTransverse
originalR445SelectedDecodesToZeroSheet coarse p =
  trans
    (cong decodeOriginalFine (sym (selectedZeroSheetIsOriginalR445 coarse p)))
    (originalAddressRoundTrip (originalAddress coarse p zeroTransverse))

-- A three-bit binary residual is the eight CORNERS of the balanced
-- ternary cube, not its 27 states. Binary zero is NOT ternary neutral.
bitToBool : Bit → Bool
bitToBool T.zeroᵢ = false
bitToBool (T.sucᵢ T.zeroᵢ) = true

originalSelectedZeroBitIsSignedNegative :
  SignedBit.embedBit (bitToBool T.zeroᵢ) ≡ SSP.sspNegOne
originalSelectedZeroBitIsSignedNegative = refl

originalTenBitCount :
  Resolution.sectorCount (Resolution.resolution23 10 0) ≡ 1024
originalTenBitCount = refl

nativeSevenBitCount :
  Resolution.sectorCount (Resolution.resolution23 7 0) ≡ 128
nativeSevenBitCount = refl

transverseThreeBitCount :
  Resolution.sectorCount (Resolution.resolution23 3 0) ≡ 8
transverseThreeBitCount = refl

------------------------------------------------------------------------
-- Binary cube faces: toggling transverse parity coordinates commutes.
-- This is only a finite ADDRESS cube (not a Wilson action symmetry).
------------------------------------------------------------------------

flip : Bit → Bit
flip T.zeroᵢ = T.sucᵢ T.zeroᵢ
flip (T.sucᵢ T.zeroᵢ) = T.zeroᵢ

toggle0 toggle1 toggle2 : ThreeTransverseBits → ThreeTransverseBits
toggle0 (transverse u v w) = transverse (flip u) v w
toggle1 (transverse u v w) = transverse u (flip v) w
toggle2 (transverse u v w) = transverse u v (flip w)

face01 : ∀ bits → toggle0 (toggle1 bits) ≡ toggle1 (toggle0 bits)
face01 (transverse u v w) = refl

face02 : ∀ bits → toggle0 (toggle2 bits) ≡ toggle2 (toggle0 bits)
face02 (transverse u v w) = refl

face12 : ∀ bits → toggle1 (toggle2 bits) ≡ toggle2 (toggle1 bits)
face12 (transverse u v w) = refl

-- Each equation restricts to either value of the third fixed bit,
-- giving six square faces. They do not imply continuum RP, W1/W3,
-- SU(N) gauge invariance, all-cutoff clustering or Clay mass gap.


------------------------------------------------------------------------
-- RH #1533 -> YM P0: SOURCE 4D SIGNED-NINE MIDPOINT GAUGE FIBRE.
--
-- 4-coordinate native original 4-torus sites are projected to the
-- first four of nine balanced trits; last five are zero. The two
-- original ODD positions 1 and 3 project to the SAME trit ZERO.
-- They are NOT the same SU(N) source gauge vertex. The original
-- C4 coarse bit is the missing, reversible branch on that zero.
--
-- This is attached to the EXISTING full 1024 original-address codec,
-- not a new Yang-Mills field type or independent blocking law.
------------------------------------------------------------------------

projectOriginalQuadToSignedTrit : R445.Quad → Wave.Trit
projectOriginalQuadToSignedTrit T.zeroᵢ = Wave.neg
projectOriginalQuadToSignedTrit (T.sucᵢ T.zeroᵢ) = Wave.zero
projectOriginalQuadToSignedTrit
  (T.sucᵢ (T.sucᵢ T.zeroᵢ)) = Wave.pos
projectOriginalQuadToSignedTrit
  (T.sucᵢ (T.sucᵢ (T.sucᵢ T.zeroᵢ))) = Wave.zero

originalSignedNineSite : R445.Site4 → Vec.Vec Wave.Trit 9
originalSignedNineSite
  (T.pair (T.pair x0 x1) (T.pair x2 x3)) =
  projectOriginalQuadToSignedTrit x0 Vec.∷
  projectOriginalQuadToSignedTrit x1 Vec.∷
  projectOriginalQuadToSignedTrit x2 Vec.∷
  projectOriginalQuadToSignedTrit x3 Vec.∷
  Wave.zero Vec.∷ Wave.zero Vec.∷ Wave.zero Vec.∷
  Wave.zero Vec.∷ Wave.zero Vec.∷ Vec.[]

originalMidpointOne : R445.Quad
originalMidpointOne = T.sucᵢ T.zeroᵢ

originalMidpointThree : R445.Quad
originalMidpointThree =
  T.sucᵢ (T.sucᵢ (T.sucᵢ T.zeroᵢ))

originalTwoOddSitesHaveSameSignedObservation :
  projectOriginalQuadToSignedTrit originalMidpointOne
  ≡ projectOriginalQuadToSignedTrit originalMidpointThree
originalTwoOddSitesHaveSameSignedObservation = refl

originalOddMidpoint : Bit → R445.Quad
originalOddMidpoint b = R445.coord b (T.sucᵢ T.zeroᵢ)

originalOddMidpointHasSignedZero :
  ∀ b → projectOriginalQuadToSignedTrit (originalOddMidpoint b)
       ≡ Wave.zero
originalOddMidpointHasSignedZero T.zeroᵢ = refl
originalOddMidpointHasSignedZero (T.sucᵢ T.zeroᵢ) = refl

-- REPAIR: retain the coarse SOURCE bit on the projected midpoint.
-- This recovers the two physically independent original odd sites.
originalOddMidpointBranchRecovers :
  ∀ b → R445.coarse (originalOddMidpoint b) ≡ b
originalOddMidpointBranchRecovers b =
  R445.coarseCoordRoundTrip b (T.sucᵢ T.zeroᵢ)

originalOddMidpointSourceRecovers :
  ∀ x → R445.phase x ≡ T.sucᵢ T.zeroᵢ →
    originalOddMidpoint (R445.coarse x) ≡ x
originalOddMidpointSourceRecovers x odd =
  trans
    (cong (R445.coord (R445.coarse x)) (sym odd))
    (originalCoordReconstructs x)

-- Exact negative test: there is an original local gauge LABEL that
-- assigns different values at 1 and 3. It therefore cannot factor
-- through ONLY their common signed-zero midpoint. (Boolean labels
-- witness a universal information-loss obstruction; the independent
-- SU(N) local gauge transformation is checked by original source
-- theorems and the noncommutative reference regression.)
originalOddGaugeLabel : R445.Quad → Bool
originalOddGaugeLabel T.zeroᵢ = false
originalOddGaugeLabel (T.sucᵢ T.zeroᵢ) = false
originalOddGaugeLabel (T.sucᵢ (T.sucᵢ T.zeroᵢ)) = false
originalOddGaugeLabel
  (T.sucᵢ (T.sucᵢ (T.sucᵢ T.zeroᵢ))) = true

falseCannotEqualTrue : false ≡ true → ⊥
falseCannotEqualTrue ()

originalSignedNineMidpointGaugeCannotDescend :
  (observedGauge : Wave.Trit → Bool) →
  (preservesEveryOriginalSite : ∀ x →
    observedGauge (projectOriginalQuadToSignedTrit x)
      ≡ originalOddGaugeLabel x) → ⊥
originalSignedNineMidpointGaugeCannotDescend observedGauge preservation =
  falseCannotEqualTrue
    (trans
      (sym (preservation originalMidpointOne))
      (preservation originalMidpointThree))

-- Exact native geometrical START/TARGET on every original positive
-- fine bond. The signed-nine label is only an observation; the real
-- fine site, axis and 128/896-bond residual remain the source labels.
originalSourceOfFullBinaryAddress : OriginalBinaryAddress → R445.Site4
originalSourceOfFullBinaryAddress address =
  T.first (encodeOriginalFine address)

originalTargetOfFullBinaryAddress : OriginalBinaryAddress → R445.Site4
originalTargetOfFullBinaryAddress address =
  OriginalBond.positiveStep
    (T.first (encodeOriginalFine address))
    (T.second (encodeOriginalFine address))

originalSignedNineSourceOfFullBinaryAddress :
  OriginalBinaryAddress → Vec.Vec Wave.Trit 9
originalSignedNineSourceOfFullBinaryAddress address =
  originalSignedNineSite (originalSourceOfFullBinaryAddress address)

originalSignedNineTargetOfFullBinaryAddress :
  OriginalBinaryAddress → Vec.Vec Wave.Trit 9
originalSignedNineTargetOfFullBinaryAddress address =
  originalSignedNineSite (originalTargetOfFullBinaryAddress address)

originalSignedNineSourceCommutingAt :
  ∀ fine →
    originalSignedNineSourceOfFullBinaryAddress
      (decodeOriginalFine fine)
    ≡ originalSignedNineSite (T.first fine)
originalSignedNineSourceCommutingAt fine =
  cong (λ bond → originalSignedNineSite (T.first bond))
    (originalFineRoundTrip fine)

originalSignedNineTargetCommutingAt :
  ∀ fine →
    originalSignedNineTargetOfFullBinaryAddress
      (decodeOriginalFine fine)
    ≡ originalSignedNineSite
        (OriginalBond.positiveStep (T.first fine) (T.second fine))
originalSignedNineTargetCommutingAt fine =
  cong (λ bond → originalSignedNineSite
    (OriginalBond.positiveStep (T.first bond) (T.second bond)))
    (originalFineRoundTrip fine)

-- FULL 1024-link reversible SOURCE field transport. The 128 selected
-- R445 positive bonds AND 896 spectators are indexed by the SAME
-- original 64 × 2 × 8 address. Nothing is quotiented out.
originalFullSignedNineGaugeFibreLift :
  ∀ {Value : Set} → (R445.FineBond → Value) →
  OriginalBinaryAddress → Value
originalFullSignedNineGaugeFibreLift field address =
  field (encodeOriginalFine address)

originalFullSignedNineGaugeFibreRecover :
  ∀ {Value : Set} → (OriginalBinaryAddress → Value) →
  R445.FineBond → Value
originalFullSignedNineGaugeFibreRecover field fine =
  field (decodeOriginalFine fine)

originalFullSignedNineGaugeFibreRecoversEveryLink :
  ∀ {Value : Set} (field : R445.FineBond → Value) fine →
    originalFullSignedNineGaugeFibreRecover
      (originalFullSignedNineGaugeFibreLift field) fine
    ≡ field fine
originalFullSignedNineGaugeFibreRecoversEveryLink field fine =
  cong field (originalFineRoundTrip fine)

originalFullSignedNineGaugeFibreRecoversEveryAddress :
  ∀ {Value : Set} (field : OriginalBinaryAddress → Value) address →
    originalFullSignedNineGaugeFibreLift
      (originalFullSignedNineGaugeFibreRecover field) address
    ≡ field address
originalFullSignedNineGaugeFibreRecoversEveryAddress field address =
  cong field (originalAddressRoundTrip address)

-- The actual SU(N) original 4D gauge action and the original Wilson
-- 1536 plaquette/action/weighted Haar functions are consumed from
-- YMClaySUNConstructedPeriodicGaugeCodecExact and the original
-- Wilson/F19 1024-link physical source BIDI. The pointwise codec
-- proves source-label preservation; no NEW analytic SU(N) Haar law,
-- dynamical 9D graph, CMP119 source T or continuum OS limit follows.


------------------------------------------------------------------------
-- EXACT FULL-1024 PHYSICAL-GAUGE ACTION: transport the source operator
-- THROUGH the proven original 64×2×8 bond address and recover it.
-- The actual SU(N) action is imported from the ORIGINAL periodic
-- Wilson source, not redefined by arbitrary binary/Trit algebra.
------------------------------------------------------------------------

module _
  {Matrix Complex : Set} {N : Nat}
  (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
  where

  Link369 : Set
  Link369 = SUN.SUNMatrixElement theory

  OriginalLinks369 : Set
  OriginalLinks369 = OriginalGauge.SUNPeriodicLinks theory 3

  OriginalGauge369 : Set
  OriginalGauge369 = OriginalGauge.SUNPeriodicGauge theory 3

  sourceLiftedSignedNineGaugeAction :
    OriginalGauge369 →
    (OriginalBinaryAddress → Link369) →
    OriginalBinaryAddress → Link369
  sourceLiftedSignedNineGaugeAction gamma lifted address =
    OriginalGauge.periodicSUNGaugeTransform theory 3
      (originalFullSignedNineGaugeFibreRecover lifted)
      gamma
      (encodeOriginalFine address)

  -- FOR EVERY original positive-bond source label, the recovered
  -- gauge-transformed lifted field is literally the original periodic
  -- SU(N) gauge transformation of the recovered fine Wilson field.
  -- No quotient on a signed midpoint: the address has all 8 residual
  -- sheets, original axial phase, original oriented coarse bond and
  -- source site. This is stronger than a 128-link-only finite square.
  originalFullSignedNineRecoveredGaugeIsOriginalAt :
    (gamma : OriginalGauge369)
    (lifted : OriginalBinaryAddress → Link369)
    (fine : R445.FineBond) →
    originalFullSignedNineGaugeFibreRecover
      (sourceLiftedSignedNineGaugeAction gamma lifted) fine
    ≡
    OriginalGauge.periodicSUNGaugeTransform theory 3
      (originalFullSignedNineGaugeFibreRecover lifted)
      gamma fine
  originalFullSignedNineRecoveredGaugeIsOriginalAt
    gamma lifted fine =
    cong
      (OriginalGauge.periodicSUNGaugeTransform theory 3
        (originalFullSignedNineGaugeFibreRecover lifted) gamma)
      (originalFineRoundTrip fine)

  -- Original SU(N) Wilson action, all 1536 original plaquettes,
  -- Haar measure and normalized marked F19 pushforward are ALREADY
  -- owned separately by the original source modules. Source-written
  -- pointwise gauge naturality here is not a new proof of product-Haar
  -- Fubini on a hypothetical independent nine-dimensional YM model.
