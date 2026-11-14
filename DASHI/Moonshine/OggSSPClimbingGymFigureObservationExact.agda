module DASHI.Moonshine.OggSSPClimbingGymFigureObservationExact where

------------------------------------------------------------------------
-- JMD "MONSTER CLIMBING GYM" FIGURE OBSERVATION SURFACE
--
-- The supplied figure reports finite wall forms, hole counts, mutual-pair
-- counts and shift controls for a sample of Ogg lanes.  This module records
-- those integers as SOURCE-REPORTED FIGURE DATA and proves only structural
-- consequences that do not require reconstructing the underlying zero list or
-- real-valued log/phase calculation.
--
-- In particular:
--   * mutual-nearest pairing is a partial matching once deterministic nearest
--     maps are supplied;
--   * several fine forms visibly saturate at the reported 849-zero sample;
--   * saturation loses wall identity: the mutual-pair count alone cannot
--     recover which canonical Ogg lane produced the row;
--   * saturation is not promoted to a zeta-zero parametrisation or RH result;
--   * the photorealistic poster's 37/43 labels are explicitly rejected using
--     the repo's independently typed non-Ogg controls.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

import DASHI.Foundations.RadixValuationStageBridge as Radix
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.OggSSPSignedRadixClimbingGymExact as Gym
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- 1. Exact integer rows transcribed from the supplied statistics panel.
------------------------------------------------------------------------

record ClimbingGymFigureRow : Set where
  constructor climbing-gym-figure-row
  field
    wallForm : Gym.WallForm
    holes : Nat
    mutualPairs : Nat
    shiftControlLabel : String
    zLabel : String

open ClimbingGymFigureRow public

figureLane : ClimbingGymFigureRow → Lane.MonsterPrimeLane
figureLane row = Gym.formLane (wallForm row)

figureExponent : ClimbingGymFigureRow → Nat
figureExponent row = Gym.formExponent (wallForm row)

figureFormN : ClimbingGymFigureRow → Nat
figureFormN row = Gym.wallFormN (wallForm row)

figureZeroCount : Nat
figureZeroCount = 849

p2Exponent1Row : ClimbingGymFigureRow
p2Exponent1Row =
  climbing-gym-figure-row
    Gym.p2Exponent1 271 270 "270.3 +/- 0.9" "-0.28"

p3Exponent1Row : ClimbingGymFigureRow
p3Exponent1Row =
  climbing-gym-figure-row
    Gym.p3Exponent1 644 581 "594.0 +/- 8.4" "-1.56"

p5Exponent1Row : ClimbingGymFigureRow
p5Exponent1Row =
  climbing-gym-figure-row
    Gym.p5Exponent1 1571 820 "825.4 +/- 3.2" "-1.69"

p7Exponent1Row : ClimbingGymFigureRow
p7Exponent1Row =
  climbing-gym-figure-row
    Gym.p7Exponent1 2660 845 "845.7 +/- 0.9" "-0.83"

p11Exponent1Row : ClimbingGymFigureRow
p11Exponent1Row =
  climbing-gym-figure-row
    Gym.p11Exponent1 5151 849 "848.5 +/- 0.6" "+0.84"

p2Exponent2Row : ClimbingGymFigureRow
p2Exponent2Row =
  climbing-gym-figure-row
    Gym.p2Exponent2 542 513 "519.3 +/- 4.3" "-1.46"

p3Exponent2Row : ClimbingGymFigureRow
p3Exponent2Row =
  climbing-gym-figure-row
    Gym.p3Exponent2 1931 841 "837.4 +/- 2.5" "+1.42"

p2Exponent3Row : ClimbingGymFigureRow
p2Exponent3Row =
  climbing-gym-figure-row
    Gym.p2Exponent3 1083 773 "771.3 +/- 3.9" "+0.44"

p13Exponent1Row : ClimbingGymFigureRow
p13Exponent1Row =
  climbing-gym-figure-row
    Gym.p13Exponent1 6511 849 "848.7 +/- 0.5" "+0.69"

p71Exponent1Row : ClimbingGymFigureRow
p71Exponent1Row =
  climbing-gym-figure-row
    Gym.p71Exponent1 59099 849 "849.0" "0.00"

figureRows : List ClimbingGymFigureRow
figureRows =
  p2Exponent1Row
  ∷ p3Exponent1Row
  ∷ p5Exponent1Row
  ∷ p7Exponent1Row
  ∷ p11Exponent1Row
  ∷ p2Exponent2Row
  ∷ p3Exponent2Row
  ∷ p2Exponent3Row
  ∷ p13Exponent1Row
  ∷ p71Exponent1Row
  ∷ []

------------------------------------------------------------------------
-- 2. Source-visible saturation receipts and exact information loss.
------------------------------------------------------------------------

p11ReportedMutualPairsSaturate :
  mutualPairs p11Exponent1Row ≡ figureZeroCount
p11ReportedMutualPairsSaturate = refl

p13ReportedMutualPairsSaturate :
  mutualPairs p13Exponent1Row ≡ figureZeroCount
p13ReportedMutualPairsSaturate = refl

p71ReportedMutualPairsSaturate :
  mutualPairs p71Exponent1Row ≡ figureZeroCount
p71ReportedMutualPairsSaturate = refl

p11P13MutualCountCollision :
  mutualPairs p11Exponent1Row ≡ mutualPairs p13Exponent1Row
p11P13MutualCountCollision = refl

p11P13LanesDistinct :
  figureLane p11Exponent1Row ≡ figureLane p13Exponent1Row → ⊥
p11P13LanesDistinct ()

record MutualCountLaneDecoder : Set where
  field
    decodeLane : Nat → Lane.MonsterPrimeLane
    recoversLane :
      (row : ClimbingGymFigureRow) →
      decodeLane (mutualPairs row) ≡ figureLane row

open MutualCountLaneDecoder public

noMutualCountLaneDecoder : MutualCountLaneDecoder → ⊥
noMutualCountLaneDecoder decoder =
  p11P13LanesDistinct
    (trans
      (sym (recoversLane decoder p11Exponent1Row))
      (trans
        (cong (decodeLane decoder) p11P13MutualCountCollision)
        (recoversLane decoder p13Exponent1Row)))

------------------------------------------------------------------------
-- 3. Generic deterministic mutual-nearest relation.
--
-- One-way nearest assignment need not be injective.  The MUTUAL relation is
-- nevertheless a partial matching: one zero cannot have two mutual holes and
-- one hole cannot have two mutual zeros.
------------------------------------------------------------------------

record MutualNearestSystem (Zero Hole : Set) : Set₁ where
  constructor mutual-nearest-system
  field
    nearestHole : Zero → Hole
    nearestZero : Hole → Zero

open MutualNearestSystem public

MutualPair :
  ∀ {Zero Hole} →
  MutualNearestSystem Zero Hole →
  Zero → Hole → Set
MutualPair system zero hole =
  (nearestHole system zero ≡ hole)
  ×
  (nearestZero system hole ≡ zero)

mutualHoleUnique :
  ∀ {Zero Hole}
    (system : MutualNearestSystem Zero Hole)
    {zero : Zero} {left right : Hole} →
  MutualPair system zero left →
  MutualPair system zero right →
  left ≡ right
mutualHoleUnique system first second =
  trans (sym (proj₁ first)) (proj₁ second)

mutualZeroUnique :
  ∀ {Zero Hole}
    (system : MutualNearestSystem Zero Hole)
    {left right : Zero} {hole : Hole} →
  MutualPair system left hole →
  MutualPair system right hole →
  left ≡ right
mutualZeroUnique system first second =
  trans (sym (proj₂ first)) (proj₂ second)

------------------------------------------------------------------------
-- 4. Analytic adapter socket.
--
-- This is where a future same-object real/log implementation may pay the JMD
-- formula.  The finite radix tree itself does not pretend to construct logs,
-- pi, real heights, or a zeta-zero list.
------------------------------------------------------------------------

record WallHeightHoleObserver (form : Gym.WallForm) : Set₁ where
  field
    Height : Set
    phaseAddress :
      Height →
      Radix.RadialTreeAddress
        (Gym.oggPrimeRadixChart (Gym.formLane form))
        (Gym.formExponent form)
    holeHeight : Nat → Height
    holeAddress :
      Nat →
      Radix.RadialTreeAddress
        (Gym.oggPrimeRadixChart (Gym.formLane form))
        (Gym.formExponent form)
    holeAtDeclaredVertex :
      (m : Nat) →
      phaseAddress (holeHeight m) ≡ holeAddress m
    phaseFormulaLabel : String
    holeFormulaLabel : String
    spacingFormulaLabel : String

open WallHeightHoleObserver public

jmdPhaseFormulaLabel : String
jmdPhaseFormulaLabel =
  "x_p(t) = frac(t * log(p) / (2*pi)); address_a = floor(p^a * x_p(t))"

jmdHoleFormulaLabel : String
jmdHoleFormulaLabel =
  "holeHeight(p,a,m) = 2*pi*m / (p^a * log(p))"

jmdHoleSpacingFormulaLabel : String
jmdHoleSpacingFormulaLabel =
  "Delta_t(p,a) = 2*pi / (p^a * log(p))"

------------------------------------------------------------------------
-- 5. Poster correction via the independent Ogg/non-Ogg control matrix.
------------------------------------------------------------------------

poster37IsNonOggControl :
  Matrix.externalOggLabel Matrix.prime37 ≡ false
poster37IsNonOggControl = Matrix.prime37ExternallyNegative

poster43IsNonOggControl :
  Matrix.externalOggLabel Matrix.prime43 ≡ false
poster43IsNonOggControl = Matrix.prime43ExternallyNegative

canonical59IsOgg :
  Matrix.externalOggLabel Matrix.prime59 ≡ true
canonical59IsOgg = refl

canonical71IsOgg :
  Matrix.externalOggLabel Matrix.prime71 ≡ true
canonical71IsOgg = refl

------------------------------------------------------------------------
-- 6. Authority boundary.
------------------------------------------------------------------------

record ClimbingGymFigureObservationBoundary : Set where
  constructor climbing-gym-figure-observation-boundary
  field
    sourceReportedIntegerRowsRecorded : Bool
    rowsUseTypedCanonicalOggLane : Bool
    mutualNearestPartialMatchingTheoremPaid : Bool
    saturatedCountCannotRecoverOggLane : Bool
    oneWayNearestAssignmentClaimedInjective : Bool
    fineFormSaturationVisibleInSuppliedRows : Bool
    shiftControlNumbersIndependentlyRecomputed : Bool
    analyticLogHeightAdapterConstructed : Bool
    poster37And43AcceptedAsCanonicalOggLanes : Bool
    poster59And71RetainedAsCanonicalOggLanes : Bool
    figureObservationProvesZetaZeroParametrisation : Bool
    figureObservationProvesRiemannHypothesis : Bool

open ClimbingGymFigureObservationBoundary public

canonicalClimbingGymFigureObservationBoundary :
  ClimbingGymFigureObservationBoundary
canonicalClimbingGymFigureObservationBoundary =
  climbing-gym-figure-observation-boundary
    true true true true false true false false false true false false
