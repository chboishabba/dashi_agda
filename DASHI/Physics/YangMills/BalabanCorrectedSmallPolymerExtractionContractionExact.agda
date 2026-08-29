module DASHI.Physics.YangMills.BalabanCorrectedSmallPolymerExtractionContractionExact where

------------------------------------------------------------------------
-- ROUND66: FINITE SMALL-POLYMER EXTRACTION / AUTOMATIC LARGE-POLYMER DECAY
--
-- PRIMARY SOURCES / CALIBRATION
--
-- David C. Brydges, John Dimock and Thomas R. Hurd,
-- "Estimates on Renormalization Group Transformations",
-- Canadian Journal of Mathematics 50 (1998), 756--793.
-- DOI: 10.4153/CJM-1998-041-5.
--
-- David C. Brydges, P. K. Mitter and B. Scoppola,
-- "Critical (Phi^4)_{3,epsilon}", Communications in Mathematical Physics
-- 240 (2003), 281--327. DOI: 10.1007/s00220-003-0895-4.
--
-- Abdelmalek Abdesselam,
-- "A Complete Renormalization Group Trajectory Between Two Fixed Points",
-- Communications in Mathematical Physics 276 (2007), 727--772.
-- DOI: 10.1007/s00220-007-0352-x.
--
-- P. K. Mitter,
-- contribution "A non trivial fixed point in a three dimensional quantum
-- field theory", in Oberwolfach Report 17/2006,
-- "The Rigorous Renormalization Group".
-- DOI of report: 10.4171/OWR/2006/17.
--
-- Tadeusz Balaban, John Imbrie and Arthur Jaffe,
-- "Renormalization of the Higgs Model: Minimizers, Propagators and the
-- Stability of Mean Field Theory", Communications in Mathematical Physics
-- 97 (1985), 299--329. DOI: 10.1007/BF01206191.
--
-- AUTHORITY / CORRECTION BOUNDARY
--
-- The sources calibrate the relevant/irrelevant extraction architecture and
-- iterative polymer norms.  Mitter explicitly records Abdesselam's detection
-- of an error in the earlier BMS norm definition and a repair leaving the
-- estimates/theorems intact.  Consequently the norm/regulator convention is
-- proof data below: no old contraction theorem can be silently reused after a
-- norm change.
--
-- DASHI CONTRIBUTION
--
-- In d=4, "small" is made finite at the source boundary by the standard 2d
-- threshold: at most eight blocks.  Every polymer is classified small/large.
-- Small polymers carry the finite relevant/marginal Taylor channels that must
-- be extracted; large polymers enter through direct geometric contraction.
--
-- For a dyadic block scale we choose the explicit target 2^{-(d+1)}=1/32 for
-- the large-polymer branch.  This is a Round66 admissible target, not a claim
-- that BDH proves this number for pure Yang--Mills.  Its exact positive margin
-- 31/32 is proved and budgeted separately against Step V/KP.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_; _/_; Positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
import Data.Nat.Base as ℕ

open import DASHI.Physics.YangMills.CompactLieProofLevel

oneThirtySecond thirtyOneThirtySeconds : ℚ
oneThirtySecond = + 1 / 32
thirtyOneThirtySeconds = + 31 / 32

oneThirtySecondPositive : 0ℚ < oneThirtySecond
oneThirtySecondPositive =
  let
    instance
      selectedPositive : Positive oneThirtySecond
      selectedPositive = ℚP.normalize-pos 1 32
  in
  ℚP.positive⁻¹ oneThirtySecond

largePolymerContractionPlusGapIsOne :
  oneThirtySecond + thirtyOneThirtySeconds ≡ 1ℚ
largePolymerContractionPlusGapIsOne = ℚRing.solve []

------------------------------------------------------------------------
-- Finite relevant/marginal channels on small polymers.
------------------------------------------------------------------------

data ExtractionChannel : Set where
  constantChannel : ExtractionChannel
  quadraticConstantChannel : ExtractionChannel
  quadraticLinearChannel : ExtractionChannel
  quarticConstantChannel : ExtractionChannel

smallPolymerBlockThresholdD4 : Nat
smallPolymerBlockThresholdD4 = 8

record CorrectedSmallLargePolymerExtraction
    (Polymer Activity RelevantPart Bound : Set) : Set₁ where
  field
    blockCount : Polymer → Nat
    Small Large : Polymer → Set
    classify : ∀ polymer → Small polymer ⊎ Large polymer
    smallLargeDisjoint : ∀ polymer → Small polymer → Large polymer → ⊥

    -- The finite extraction branch is literally bounded by 2d=8 in d=4.
    smallHasAtMostEightBlocks : ∀ polymer → Small polymer →
      ℕ._≤_ (blockCount polymer) smallPolymerBlockThresholdD4

    activity : Polymer → Activity
    extractedRelevant : Polymer → RelevantPart
    irrelevantRemainder : Polymer → Activity

    ExactDecomposition : Activity → RelevantPart → Activity → Set
    extractionExact : ∀ polymer → Small polymer →
      ExactDecomposition
        (activity polymer)
        (extractedRelevant polymer)
        (irrelevantRemainder polymer)

    NormalizedChannel : Activity → ExtractionChannel → Set
    smallRemainderNormalized : ∀ polymer → Small polymer → channel →
      NormalizedChannel (irrelevantRemainder polymer) channel

    norm : Activity → Bound
    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    smallContraction : Bound
    largeContraction : Bound

    smallRemainderContractive : ∀ polymer → Small polymer →
      LessEqual
        (norm (irrelevantRemainder polymer))
        (multiply smallContraction (norm (activity polymer)))

    largeActivityContractive : ∀ polymer → Large polymer →
      LessEqual
        (norm (activity polymer))
        (multiply largeContraction (norm (activity polymer)))

open CorrectedSmallLargePolymerExtraction public

data PolymerContractionCase
    {Polymer Activity RelevantPart Bound}
    (dataSet : CorrectedSmallLargePolymerExtraction
      Polymer Activity RelevantPart Bound)
    (polymer : Polymer) : Set where
  smallCase : Small dataSet polymer → PolymerContractionCase dataSet polymer
  largeCase : Large dataSet polymer → PolymerContractionCase dataSet polymer

polymerContractionCase :
  ∀ {Polymer Activity RelevantPart Bound}
    (dataSet : CorrectedSmallLargePolymerExtraction
      Polymer Activity RelevantPart Bound)
    polymer → PolymerContractionCase dataSet polymer
polymerContractionCase dataSet polymer with classify dataSet polymer
... | inj₁ small = smallCase small
... | inj₂ large = largeCase large

correctedSmallLargeExtractionCompilerLevel : ProofLevel
correctedSmallLargeExtractionCompilerLevel = machineChecked

dyadicD4LargePolymerArithmeticLevel : ProofLevel
dyadicD4LargePolymerArithmeticLevel = machineChecked

physicalYMSmallPolymerExtractionLevel : ProofLevel
physicalYMSmallPolymerExtractionLevel = conditional

physicalYMLargePolymerContractionLevel : ProofLevel
physicalYMLargePolymerContractionLevel = conditional
