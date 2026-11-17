module DASHI.Biology.IITJFineFourOneFourS3ZetaGaugeExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)
import Base369 as Base
import DASHI.Biology.JFinePhaseQuotientFieldExact as Fine
import DASHI.Moonshine.OggSSPP2F4RecenteredTriXorS3Exact as S3Source
import DASHI.Algebra.TriadicDepthOneCharacters as Characters
import DASHI.Moonshine.C3FourierConjugationExact as Fourier
import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.IITJFineSelectedCrossPunctured79Exact as Previous

------------------------------------------------------------------------
-- EXACT SOURCE TYPE, NEW CONSUMER-RELATIVE SPLITTING:
--   3x3 j-fine phase table = 4 corners + centre + 4 edge sites
--     ≃ F3^4 x F3 x F3^4    (81 * 3 * 81 = 19683).
--
-- TWO LEVELS:
--  (a) literal coordinate split: centre, four edge, four corner trits;
--  (b) centre-gauge split: centre, edge-centre, corner-centre over F3.
-- The second is a genuine C3 torsor trivialisation: uniform translation
-- moves only centre; relative shell data is invariant.
--
-- The existing S3Source recentered additive F3 source (mid = zero)
-- is used as an operator, NOT identified with an F4 elliptic curve
-- or a Monster action by its name. The existing Fourier/Characters
-- modules own exact zeta and inverse-zeta phase statements.
------------------------------------------------------------------------

record FourTrit : Set where
  constructor fourTrit
  field
    a b c d : Base.TriTruth
open FourTrit public

record FourOneFour : Set where
  constructor fourOneFour
  field
    centre : Base.TriTruth
    edges corners : FourTrit
open FourOneFour public

literalSplit : Fine.PhaseFineTable9 → FourOneFour
literalSplit (Fine.phaseFineTable9 nw n ne w v e sw s se) =
  fourOneFour v (fourTrit n e s w) (fourTrit nw ne sw se)

literalJoin : FourOneFour → Fine.PhaseFineTable9
literalJoin
  (fourOneFour v (fourTrit n e s w) (fourTrit nw ne sw se)) =
  Fine.phaseFineTable9 nw n ne w v e sw s se

literalJoinSplit :
  (sheet : Fine.PhaseFineTable9) →
  literalJoin (literalSplit sheet) ≡ sheet
literalJoinSplit (Fine.phaseFineTable9 nw n ne w v e sw s se) = refl

literalSplitJoin :
  (chart : FourOneFour) →
  literalSplit (literalJoin chart) ≡ chart
literalSplitJoin (fourOneFour v (fourTrit n e s w)
  (fourTrit nw ne sw se)) = refl

relativeTrit : Base.TriTruth → Base.TriTruth → Base.TriTruth
relativeTrit origin value =
  S3Source.centerAdd value (S3Source.centerNeg origin)

restoreTrit : Base.TriTruth → Base.TriTruth → Base.TriTruth
restoreTrit origin relative =
  S3Source.centerAdd origin relative

-- Exact additive-group cancellation reused from the already constructed
-- recentered ternary group laws, not all-nine enumeration.
relativeAfterRestore :
  (origin t : Base.TriTruth) →
  relativeTrit origin (restoreTrit origin t) ≡ t
relativeAfterRestore origin t =
  trans
    (cong
      (λ u → S3Source.centerAdd u (S3Source.centerNeg origin))
      (S3Source.centerCommutative origin t))
    (trans
      (sym (S3Source.centerAssociative t origin
        (S3Source.centerNeg origin)))
      (trans
        (cong (S3Source.centerAdd t)
          (S3Source.centerInverseRight origin))
        (S3Source.centerUnitRight t)))

restoreAfterRelative :
  (origin t : Base.TriTruth) →
  restoreTrit origin (relativeTrit origin t) ≡ t
restoreAfterRelative origin t =
  trans
    (S3Source.centerAssociative origin t
      (S3Source.centerNeg origin))
    (relativeAfterRestore origin t)

mapFour : (Base.TriTruth → Base.TriTruth) → FourTrit → FourTrit
mapFour f (fourTrit a b c d) = fourTrit (f a) (f b) (f c) (f d)

relativeGauge : Fine.PhaseFineTable9 → FourOneFour
relativeGauge sheet with literalSplit sheet
... | fourOneFour v edge corner =
  fourOneFour v
    (mapFour (relativeTrit v) edge)
    (mapFour (relativeTrit v) corner)

restoreGauge : FourOneFour → Fine.PhaseFineTable9
restoreGauge (fourOneFour v edge corner) =
  literalJoin (fourOneFour v
    (mapFour (restoreTrit v) edge)
    (mapFour (restoreTrit v) corner))

relativeAfterRestoreGauge :
  (chart : FourOneFour) →
  relativeGauge (restoreGauge chart) ≡ chart
relativeAfterRestoreGauge
  (fourOneFour v (fourTrit a b c d) (fourTrit e f g h))
  rewrite relativeAfterRestore v a | relativeAfterRestore v b
        | relativeAfterRestore v c | relativeAfterRestore v d
        | relativeAfterRestore v e | relativeAfterRestore v f
        | relativeAfterRestore v g | relativeAfterRestore v h = refl

restoreAfterRelativeGauge :
  (sheet : Fine.PhaseFineTable9) →
  restoreGauge (relativeGauge sheet) ≡ sheet
restoreAfterRelativeGauge
  (Fine.phaseFineTable9 a b c d v e f g h)
  rewrite restoreAfterRelative v a | restoreAfterRelative v b
        | restoreAfterRelative v c | restoreAfterRelative v d
        | restoreAfterRelative v e | restoreAfterRelative v f
        | restoreAfterRelative v g | restoreAfterRelative v h = refl

-- Explicit global value S3 = F3 ⋊ {+1,-1} generators.
-- This is the affine permutation group of the THREE balanced ternary
-- values. It is NOT the S3 permutation of three spatial rows.
rotateValues : Fine.PhaseFineTable9 → Fine.PhaseFineTable9
rotateValues (Fine.phaseFineTable9 a b c d e f g h i) =
  Fine.phaseFineTable9
    (S3Source.advance a) (S3Source.advance b) (S3Source.advance c)
    (S3Source.advance d) (S3Source.advance e) (S3Source.advance f)
    (S3Source.advance g) (S3Source.advance h) (S3Source.advance i)

reflectValues : Fine.PhaseFineTable9 → Fine.PhaseFineTable9
reflectValues (Fine.phaseFineTable9 a b c d e f g h i) =
  Fine.phaseFineTable9
    (S3Source.centerNeg a) (S3Source.centerNeg b)
    (S3Source.centerNeg c) (S3Source.centerNeg d)
    (S3Source.centerNeg e) (S3Source.centerNeg f)
    (S3Source.centerNeg g) (S3Source.centerNeg h)
    (S3Source.centerNeg i)

rotateGauge : FourOneFour → FourOneFour
rotateGauge (fourOneFour v edge corner) =
  fourOneFour (S3Source.advance v) edge corner

reflectGauge : FourOneFour → FourOneFour
reflectGauge (fourOneFour v edge corner) =
  fourOneFour (S3Source.centerNeg v)
    (mapFour S3Source.centerNeg edge)
    (mapFour S3Source.centerNeg corner)

-- These are finite 3x3-coordinate algebra checks. The relations
-- are inherited from the source's recentered ternary group structure.
translateRelative :
  ∀ origin value →
  relativeTrit (S3Source.advance origin) (S3Source.advance value)
  ≡ relativeTrit origin value
translateRelative Base.tri-low Base.tri-low = refl
translateRelative Base.tri-low Base.tri-mid = refl
translateRelative Base.tri-low Base.tri-high = refl
translateRelative Base.tri-mid Base.tri-low = refl
translateRelative Base.tri-mid Base.tri-mid = refl
translateRelative Base.tri-mid Base.tri-high = refl
translateRelative Base.tri-high Base.tri-low = refl
translateRelative Base.tri-high Base.tri-mid = refl
translateRelative Base.tri-high Base.tri-high = refl

reflectRelative :
  ∀ origin value →
  relativeTrit (S3Source.centerNeg origin) (S3Source.centerNeg value)
  ≡ S3Source.centerNeg (relativeTrit origin value)
reflectRelative Base.tri-low Base.tri-low = refl
reflectRelative Base.tri-low Base.tri-mid = refl
reflectRelative Base.tri-low Base.tri-high = refl
reflectRelative Base.tri-mid Base.tri-low = refl
reflectRelative Base.tri-mid Base.tri-mid = refl
reflectRelative Base.tri-mid Base.tri-high = refl
reflectRelative Base.tri-high Base.tri-low = refl
reflectRelative Base.tri-high Base.tri-mid = refl
reflectRelative Base.tri-high Base.tri-high = refl

globalValueRotationPreservesRelative :
  (sheet : Fine.PhaseFineTable9) →
  relativeGauge (rotateValues sheet) ≡ rotateGauge (relativeGauge sheet)
globalValueRotationPreservesRelative
  (Fine.phaseFineTable9 a b c d v e f g h)
  rewrite translateRelative v a | translateRelative v b
        | translateRelative v c | translateRelative v d
        | translateRelative v e | translateRelative v f
        | translateRelative v g | translateRelative v h = refl

globalValueReflectionActsByNegation :
  (sheet : Fine.PhaseFineTable9) →
  relativeGauge (reflectValues sheet) ≡ reflectGauge (relativeGauge sheet)
globalValueReflectionActsByNegation
  (Fine.phaseFineTable9 a b c d v e f g h)
  rewrite reflectRelative v a | reflectRelative v b
        | reflectRelative v c | reflectRelative v d
        | reflectRelative v e | reflectRelative v f
        | reflectRelative v g | reflectRelative v h = refl

rotateValueThree : ∀ c →
  S3Source.advance (S3Source.advance (S3Source.advance c)) ≡ c
rotateValueThree Base.tri-low = refl
rotateValueThree Base.tri-mid = refl
rotateValueThree Base.tri-high = refl

negValueTwice : ∀ c →
  S3Source.centerNeg (S3Source.centerNeg c) ≡ c
negValueTwice Base.tri-low = refl
negValueTwice Base.tri-mid = refl
negValueTwice Base.tri-high = refl

rotateGaugeThree :
  (chart : FourOneFour) →
  rotateGauge (rotateGauge (rotateGauge chart)) ≡ chart
rotateGaugeThree (fourOneFour v e k) rewrite rotateValueThree v = refl

reflectGaugeTwice :
  (chart : FourOneFour) →
  reflectGauge (reflectGauge chart) ≡ chart
reflectGaugeTwice
  (fourOneFour v (fourTrit a b c d) (fourTrit e f g h))
  rewrite negValueTwice v | negValueTwice a | negValueTwice b
        | negValueTwice c | negValueTwice d | negValueTwice e
        | negValueTwice f | negValueTwice g | negValueTwice h = refl

reflectAdvanceReflect :
  ∀ c →
  S3Source.centerNeg (S3Source.advance (S3Source.centerNeg c))
  ≡ S3Source.advance (S3Source.advance c)
reflectAdvanceReflect Base.tri-low = refl
reflectAdvanceReflect Base.tri-mid = refl
reflectAdvanceReflect Base.tri-high = refl

s3BraidRelation :
  (chart : FourOneFour) →
  reflectGauge (rotateGauge (reflectGauge chart))
  ≡ rotateGauge (rotateGauge chart)
s3BraidRelation
  (fourOneFour v (fourTrit a b c d) (fourTrit e f g h))
  rewrite reflectAdvanceReflect v
        | negValueTwice a | negValueTwice b
        | negValueTwice c | negValueTwice d
        | negValueTwice e | negValueTwice f
        | negValueTwice g | negValueTwice h = refl

-- Exact site D4 operations, independent of the value S3.
quarterSheet : Fine.PhaseFineTable9 → Fine.PhaseFineTable9
quarterSheet (Fine.phaseFineTable9 a b c d e f g h i) =
  Fine.phaseFineTable9 g d a h e b i f c

mirrorSheet : Fine.PhaseFineTable9 → Fine.PhaseFineTable9
mirrorSheet (Fine.phaseFineTable9 a b c d e f g h i) =
  Fine.phaseFineTable9 c b a f e d i h g

-- D4's fixed centre is a *different* distinguished object from C5's
-- five-slot chosen cyclic order. No unproved identification is imported.
quarterPreservesCentre : ∀ sheet →
  Fine.q11 (quarterSheet sheet) ≡ Fine.q11 sheet
quarterPreservesCentre (Fine.phaseFineTable9 a b c d e f g h i) = refl

mirrorPreservesCentre : ∀ sheet →
  Fine.q11 (mirrorSheet sheet) ≡ Fine.q11 sheet
mirrorPreservesCentre (Fine.phaseFineTable9 a b c d e f g h i) = refl

-- Actual original symbolic zeta characters are reused, not rewritten.
centreZeta : Base.TriTruth → Characters.C3Phase
centreZeta Base.tri-mid = Fourier.one
centreZeta Base.tri-high = Fourier.zeta
centreZeta Base.tri-low = Fourier.zetaSquared

centrePositiveEigenphase : ∀ c →
  centreZeta (S3Source.advance c)
  ≡ Characters.multiplyPhase Fourier.zeta (centreZeta c)
centrePositiveEigenphase Base.tri-low = refl
centrePositiveEigenphase Base.tri-mid = refl
centrePositiveEigenphase Base.tri-high = refl

centreConjugatePhase : ∀ c →
  centreZeta (S3Source.centerNeg c) ≡ Fourier.inversePhase (centreZeta c)
centreConjugatePhase Base.tri-low = refl
centreConjugatePhase Base.tri-mid = refl
centreConjugatePhase Base.tri-high = refl

jFineCardinality414 : 81 * 3 * 81 ≡ 19683
jFineCardinality414 = refl

oneRelativeFibreCardinality : 81 * 81 ≡ 6561
oneRelativeFibreCardinality = refl

pointedRegularZetaMultiplicity : 10 * 6561 ≡ 65610
pointedRegularZetaMultiplicity = refl

pointedThreePhaseSectors : 3 * 65610 ≡ 196830
pointedThreePhaseSectors = refl

-- Distinct D4 spatial and S3 value actions jointly classify
-- three-colourings of the nine-sheet. D4 has site-cycle patterns:
--   identity 9 cycles,
--   2 quarter turns each 3 cycles/2 even cycles,
--   half turn 5 cycles/4 even cycles,
--   4 reflections each 6 cycles/3 even cycles.
-- Over all six S3 value permutations, the two genuine 3-cycles have
-- zero fixed nine-sheet colourings because D4's site cycle lengths are
-- only 1,2,4; the identity fixes 3^cycles, each of 3 reflections on
-- colour values fixes 3^even-site-cycles.
--
-- Burnside numerator 23520 gives 490 simultaneous D4 x S3 orbits.
-- The numerical script independently enumerates all 19683 sheets.
-- Only the integer arithmetic is source-written Agda here; the
-- group fixed-point enumeration is a separately checked finite lemma.

burnsideD4S3Numerator :
  19683 + 2 * 27 + 243 + 4 * 729
    + 3 * (1 + 2 * 9 + 81 + 4 * 27)
  ≡ 23520
burnsideD4S3Numerator = refl

burnsideD4S3Orbits : 48 * 490 ≡ 23520
burnsideD4S3Orbits = refl

record FourOneFourS3ZetaBoundary : Set where
  constructor four-one-four-s3-zeta-boundary
  field
    actualJFineNineSheetCodecPaid : Bool
    centreGaugeRoundTripsSourceWritten : Bool
    globalAffineS3CompatibilitySourceWritten : Bool
    zetaConjugationSourceReused : Bool
    actualMonster3BActionIntertwinerPaid : Bool
    twoCornerEdgeF81MultiplicationsAreCanonical : Bool
    literalAgdaKernelReceiptAvailable : Bool

canonicalBoundary : FourOneFourS3ZetaBoundary
canonicalBoundary =
  four-one-four-s3-zeta-boundary true true true true false false false
