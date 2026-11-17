module DASHI.Biology.IITJFineD4S3MixedCharacterExact where

open import DASHI.Core.Prelude
import Base369 as Base
import DASHI.Biology.JFinePhaseQuotientFieldExact as Fine
import DASHI.Biology.IITJFineFourOneFourS3ZetaGaugeExact as Gauge
import DASHI.Biology.PointedTernaryBulkExact as Pointed
import DASHI.Moonshine.OggSSPP2F4RecenteredTriXorS3Exact as Ternary
import DASHI.Algebra.TriadicDepthOneCharacters as Characters
import DASHI.Moonshine.C3FourierConjugationExact as Fourier

------------------------------------------------------------------------
-- ORIGINAL SOURCE OWNER REUSE:
-- PhaseFineTable9 : literal nine ternary values on a 3x3 sheet.
-- Gauge.quarterSheet / mirrorSheet : actual D4 site operations.
-- Gauge.rotateValues / reflectValues : actual global value S3 = F3 ⋊ C2.
-- Pointed.MarkedOrUnmarkedSite : actual 9 marked + one unmarked marker.
--
-- NEW RESULTS:
-- (a) source-level four commutation theorems for D4 and value-S3;
-- (b) source-level pointed D4 marker moves, not ten inert copies;
-- (c) exact character-data target for complex linearisation, 15 sectors;
-- (d) a concrete obstruction to confusing the ROW/COLUMN S3 with
--     value-permutation S3: row swaps can move the distinguished centre.
--
-- The multiplicity table below was independently checked by finite
-- character arithmetic in scripts/iit_jfine_d4_s3_mixed_character_audit.py.
-- Arithmetical identities here do NOT by themselves prove that the
-- supplied table is the kernel-derived character decomposition; that
-- needs a literal finite permutation representation/character bridge.
-- Neither the Monster 3B normalizer nor physical quantum eigenstates
-- are identified by these computations.
------------------------------------------------------------------------

quarterCommutesWithValueCycle :
  (sheet : Fine.PhaseFineTable9) →
  Gauge.quarterSheet (Gauge.rotateValues sheet)
    ≡ Gauge.rotateValues (Gauge.quarterSheet sheet)
quarterCommutesWithValueCycle
  (Fine.phaseFineTable9 a b c d e f g h i) = refl

mirrorCommutesWithValueCycle :
  (sheet : Fine.PhaseFineTable9) →
  Gauge.mirrorSheet (Gauge.rotateValues sheet)
    ≡ Gauge.rotateValues (Gauge.mirrorSheet sheet)
mirrorCommutesWithValueCycle
  (Fine.phaseFineTable9 a b c d e f g h i) = refl

quarterCommutesWithValueReflection :
  (sheet : Fine.PhaseFineTable9) →
  Gauge.quarterSheet (Gauge.reflectValues sheet)
    ≡ Gauge.reflectValues (Gauge.quarterSheet sheet)
quarterCommutesWithValueReflection
  (Fine.phaseFineTable9 a b c d e f g h i) = refl

mirrorCommutesWithValueReflection :
  (sheet : Fine.PhaseFineTable9) →
  Gauge.mirrorSheet (Gauge.reflectValues sheet)
    ≡ Gauge.reflectValues (Gauge.mirrorSheet sheet)
mirrorCommutesWithValueReflection
  (Fine.phaseFineTable9 a b c d e f g h i) = refl

-- The real pointed marker is a source-typed coordinate, transformed
-- along with the original fine sheet by the same D4 site rotation.
PointedFineChart : Set
PointedFineChart =
  Pointed.MarkedOrUnmarkedSite × Fine.PhaseFineTable9

pointedQuarter : PointedFineChart → PointedFineChart
pointedQuarter (marker , sheet) =
  Pointed.rotateMarkerQuarter marker , Gauge.quarterSheet sheet

pointedMirror : PointedFineChart → PointedFineChart
pointedMirror (marker , sheet) =
  Pointed.reflectMarkerVertical marker , Gauge.mirrorSheet sheet

pointedValueCycle : PointedFineChart → PointedFineChart
pointedValueCycle (marker , sheet) = marker , Gauge.rotateValues sheet

pointedValueReflection : PointedFineChart → PointedFineChart
pointedValueReflection (marker , sheet) = marker , Gauge.reflectValues sheet

pointedQuarterCommutesWithValueCycle :
  (state : PointedFineChart) →
  pointedQuarter (pointedValueCycle state)
    ≡ pointedValueCycle (pointedQuarter state)
pointedQuarterCommutesWithValueCycle
  (marker , Fine.phaseFineTable9 a b c d e f g h i) = refl

pointedMirrorCommutesWithValueReflection :
  (state : PointedFineChart) →
  pointedMirror (pointedValueReflection state)
    ≡ pointedValueReflection (pointedMirror state)
pointedMirrorCommutesWithValueReflection
  (marker , Fine.phaseFineTable9 a b c d e f g h i) = refl

-- The actual D4 mirror treats edge sites and corner sites differently.
verticalFixesNorthEdge :
  Pointed.reflectSiteVertical Pointed.northSite ≡ Pointed.northSite
verticalFixesNorthEdge = refl

verticalMovesNorthWestCorner :
  Pointed.reflectSiteVertical Pointed.northWestSite
  ≡ Pointed.northWestSite → ⊥
verticalMovesNorthWestCorner ()

-- Rows and columns each admit their OWN S3 permutations. This is a
-- different group action from the global balanced-value S3 above.
swapNorthAndMiddleRows : Fine.PhaseFineTable9 → Fine.PhaseFineTable9
swapNorthAndMiddleRows
  (Fine.phaseFineTable9 a b c d e f g h i) =
  Fine.phaseFineTable9 d e f a b c g h i

centreOnlySheet : Fine.PhaseFineTable9
centreOnlySheet =
  Fine.phaseFineTable9
    Base.tri-mid Base.tri-mid Base.tri-mid
    Base.tri-mid Base.tri-high Base.tri-mid
    Base.tri-mid Base.tri-mid Base.tri-mid

rowS3DoesNotPreserveCentre :
  Fine.q11 (swapNorthAndMiddleRows centreOnlySheet)
  ≡ Fine.q11 centreOnlySheet → ⊥
rowS3DoesNotPreserveCentre ()

-- The existing source zeta phase transforms covariantly under the
-- additive C3 and conjugates under value reflection. Characters live
-- in a suitable characteristic-zero / cyclotomic coefficient ring:
-- F3 itself does NOT contain three distinct cubic roots of unity.
sourceCentreZetaCovariant :
  (c : Base.TriTruth) →
  Gauge.centreZeta (Ternary.advance c)
  ≡ Characters.multiplyPhase Fourier.zeta (Gauge.centreZeta c)
sourceCentreZetaCovariant = Gauge.centrePositiveEigenphase

sourceCentreZetaConjugates :
  (c : Base.TriTruth) →
  Gauge.centreZeta (Ternary.centerNeg c)
  ≡ Fourier.inversePhase (Gauge.centreZeta c)
sourceCentreZetaConjugates = Gauge.centreConjugatePhase

------------------------------------------------------------------------
-- SOURCE-SPECIFIC MIXED CHARACTER EXPECTATION.
-- D4 irreps A0,A1,A2,A3 have complex dimension one, E dimension two.
-- Value S3 irreps trivial, sign have dimension one; standard dimension
-- two.  The 15 source-decomposition multiplicities are *numerical
-- character targets*, not assumed Agda-verified representations.
--
-- Important: the POINTED table is not ten times the FINE table, because
-- the original Pointed marker moves under site D4.
------------------------------------------------------------------------

data D4Sector : Set where
  A0 A1 A2 A3 E : D4Sector

data S3Sector : Set where
  trivial sign standard : S3Sector

fineMultiplicity : D4Sector → S3Sector → Nat
fineMultiplicity A0 trivial = 490
fineMultiplicity A0 sign = 464
fineMultiplicity A0 standard = 954
fineMultiplicity A1 trivial = 355
fineMultiplicity A1 sign = 356
fineMultiplicity A1 standard = 711
fineMultiplicity A2 trivial = 418
fineMultiplicity A2 sign = 410
fineMultiplicity A2 standard = 828
fineMultiplicity A3 trivial = 418
fineMultiplicity A3 sign = 410
fineMultiplicity A3 standard = 828
fineMultiplicity E trivial = 800
fineMultiplicity E sign = 820
fineMultiplicity E standard = 1620

pointedMultiplicity : D4Sector → S3Sector → Nat
pointedMultiplicity A0 trivial = 4396
pointedMultiplicity A0 sign = 4316
pointedMultiplicity A0 standard = 8712
pointedMultiplicity A1 trivial = 3856
pointedMultiplicity A1 sign = 3884
pointedMultiplicity A1 standard = 7740
pointedMultiplicity A2 trivial = 4117
pointedMultiplicity A2 sign = 4100
pointedMultiplicity A2 standard = 8217
pointedMultiplicity A3 trivial = 4117
pointedMultiplicity A3 sign = 4100
pointedMultiplicity A3 standard = 8217
pointedMultiplicity E trivial = 8162
pointedMultiplicity E sign = 8200
pointedMultiplicity E standard = 16362

fineD4SectorDimension : D4Sector → Nat
fineD4SectorDimension d =
  fineMultiplicity d trivial
  + fineMultiplicity d sign
  + 2 * fineMultiplicity d standard

pointedD4SectorDimension : D4Sector → Nat
pointedD4SectorDimension d =
  pointedMultiplicity d trivial
  + pointedMultiplicity d sign
  + 2 * pointedMultiplicity d standard

fineTotalMixedDegree :
  fineD4SectorDimension A0 + fineD4SectorDimension A1
  + fineD4SectorDimension A2 + fineD4SectorDimension A3
  + 2 * fineD4SectorDimension E ≡ 19683
fineTotalMixedDegree = refl

pointedTotalMixedDegree :
  pointedD4SectorDimension A0 + pointedD4SectorDimension A1
  + pointedD4SectorDimension A2 + pointedD4SectorDimension A3
  + 2 * pointedD4SectorDimension E ≡ 196830
pointedTotalMixedDegree = refl

fineJointOrbitCount : fineMultiplicity A0 trivial ≡ 490
fineJointOrbitCount = refl

pointedJointOrbitCount : pointedMultiplicity A0 trivial ≡ 4396
pointedJointOrbitCount = refl

-- D4 x S3 fixed-point character is source-checked by finite Python:
-- fine Burnside numerator = 23520, denominator 48 -> 490.
-- for actual moving marker, numerator 211008 / 48 = 4396.
fineBurnsideTarget : 48 * 490 ≡ 23520
fineBurnsideTarget = refl

pointedBurnsideTarget : 48 * 4396 ≡ 211008
pointedBurnsideTarget = refl

-- Spatial row/column wreath S3 wr C2 has 72 site permutations;
-- it is not AGL(1,9), which also has order 72 but contains order-8
-- elements. The wreath site's maximal element order is 6.
-- The larger spatial72 x valueS3 action has 84 fine-sheet orbits.
rowColumnMixedOrbitTarget : 432 * 84 ≡ 36288
rowColumnMixedOrbitTarget = refl

record MixedCharacterAuthorityBoundary : Set where
  constructor mixed-character-authority-boundary
  field
    exactSourceD4ValueS3CommutationConstructed : Bool
    actualPointedMarkerD4Moves : Bool
    fineCharacterAndPointedNumericalTargetSupplied : Bool
    literalCharacterOrthogonalityKernelProved : Bool
    originalMonsterNormalizerRepresentationIdentified : Bool
    S3AlphabetActionEqualsRowColumnS3 : Bool
    physicalQuantumZetaMechanismEstablished : Bool

canonicalBoundary : MixedCharacterAuthorityBoundary
canonicalBoundary =
  mixed-character-authority-boundary
    true true true false false false false
