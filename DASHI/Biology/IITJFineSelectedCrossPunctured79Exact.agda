module DASHI.Biology.IITJFineSelectedCrossPunctured79Exact where

open import DASHI.Core.Prelude
import Base369 as Base
import DASHI.Biology.JFinePhaseQuotientFieldExact as Fine
import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.PointedTernaryBulkExact as Pointed
import DASHI.Biology.DialecticalSheetSpiralExact as Sheet
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Analysis.RiemannQuarticPuncturedKernel4EnumerationExact as Punctured

------------------------------------------------------------------------
-- SOURCE-AWARE IDENTIFICATION, NOT A CARDINALITY COINCIDENCE.
--
-- Earlier DASHI authoritative carriers:
--   Fine.PhaseFineTable9                 = 9 trit positions
--   Harmonic.FineFrequency               = Fin 3^9 = 19683
--   Harmonic.CoarseChannel               = 9 ordinary + completionJ
--   Pointed.MarkedOrUnmarkedSite         = 9 marked + one unmarked
--   Punctured.puncturedKernel4EnumerationLengthIs80
--                                          = 3^4 - 1
--
-- A chosen D4-INVARIANT spatial split puts five profile trits on
-- the cross C,N,E,S,W and four relative trits on the corners NW,NE,SW,SE.
-- This gives a genuine two-sided 5+4 chart for the original JFine
-- frequency carrier and an exact ten-marker correspondence.
--
-- IMPORTANT: the cyclic Z/5 profile of the 5^3 lattice is NOT naturally
-- equivariant to the source C3^2 phase translations or D4 sheet action.
-- The five-site selection is D4-STABLE AS A SET only; its cyclic order
-- is an extra selected registration.
------------------------------------------------------------------------

record SelectedFive : Set where
  constructor selectedFive
  field
    centreSlot northSlot eastSlot southSlot westSlot : Base.TriTruth
open SelectedFive public

record CornerFour : Set where
  constructor cornerFour
  field
    northWestSlot northEastSlot southWestSlot southEastSlot : Base.TriTruth
open CornerFour public

joinNine : SelectedFive → CornerFour → Fine.PhaseFineTable9
joinNine p r =
  Fine.phaseFineTable9
    (northWestSlot r) (northSlot p) (northEastSlot r)
    (westSlot p) (centreSlot p) (eastSlot p)
    (southWestSlot r) (southSlot p) (southEastSlot r)

splitNine : Fine.PhaseFineTable9 → SelectedFive × CornerFour
splitNine sheet =
  selectedFive
    (Fine.q11 sheet) (Fine.q01 sheet) (Fine.q12 sheet)
    (Fine.q21 sheet) (Fine.q10 sheet)
  ,
  cornerFour
    (Fine.q00 sheet) (Fine.q02 sheet)
    (Fine.q20 sheet) (Fine.q22 sheet)

joinSplitNine :
  (sheet : Fine.PhaseFineTable9) →
  joinNine (proj₁ (splitNine sheet)) (proj₂ (splitNine sheet)) ≡ sheet
joinSplitNine (Fine.phaseFineTable9 a b c d e f g h i) = refl

splitJoinNine :
  (p : SelectedFive) (r : CornerFour) →
  splitNine (joinNine p r) ≡ (p , r)
splitJoinNine
  (selectedFive a b c d e)
  (cornerFour f g h i) = refl

-- The chosen missing-profile cyclic order is explicit. It has order five,
-- but unlike the original D4 site rotation it MOVES the centre label.

rotateFive : SelectedFive → SelectedFive
rotateFive (selectedFive a b c d e) = selectedFive e a b c d

rotateFiveFive :
  (profile : SelectedFive) →
  rotateFive (rotateFive (rotateFive (rotateFive (rotateFive profile)))) ≡ profile
rotateFiveFive (selectedFive a b c d e) = refl

markedCentreProfile : SelectedFive
markedCentreProfile =
  selectedFive Base.tri-high
    Base.tri-mid Base.tri-mid Base.tri-mid Base.tri-mid

C5RotationMovesCentre :
  rotateFive markedCentreProfile ≡ markedCentreProfile → ⊥
C5RotationMovesCentre ()

sourceD4RotationFixesCentreSite :
  Pointed.rotateSiteQuarter Pointed.centreSite ≡ Pointed.centreSite
sourceD4RotationFixesCentreSite = refl

-- These different orbit signatures rule out any identification that
-- claims the specific source D4 quarter-turn IS our chosen C5 generator.
-- Another transported action can be defined with an explicit rechart.

-- Composition with the repo's already-proved Fin(3^9) codec.
-- We don't assert that two independently named abstract carriers are equal:
-- both conversions operate on the literal earlier source type.
packJFine : SelectedFive × CornerFour → Harmonic.FineFrequency
packJFine (p , r) =
  Fine.encodeTritDigits (Fine.digitsFromTable (joinNine p r))

unpackJFine : Harmonic.FineFrequency → SelectedFive × CornerFour
unpackJFine fine =
  splitNine (Fine.tableFromDigits (Fine.decodeTritDigits fine))

unpackAfterPackJFine :
  (coordinates : SelectedFive × CornerFour) →
  unpackJFine (packJFine coordinates) ≡ coordinates
unpackAfterPackJFine (p , r)
  rewrite
    Fine.decodeAfterEncodeTritDigits
      (Fine.digitsFromTable (joinNine p r))
  | Fine.tableAfterDigits (joinNine p r)
  = splitJoinNine p r

packAfterUnpackJFine :
  (fine : Harmonic.FineFrequency) →
  packJFine (unpackJFine fine) ≡ fine
packAfterUnpackJFine fine
  rewrite
    joinSplitNine (Fine.tableFromDigits (Fine.decodeTritDigits fine))
  | Fine.digitsAfterTable (Fine.decodeTritDigits fine)
  = Fine.encodeAfterDecodeTritDigits fine

------------------------------------------------------------------------
-- ALSO IDENTIFY the existing 10 pointed labels with the *actual*
-- harmonic coarse labels. This is bijective but does not claim
-- their original actions are equal: transport requires an intertwiner.
------------------------------------------------------------------------

toPointedMarker : Harmonic.CoarseChannel → Pointed.MarkedOrUnmarkedSite
toPointedMarker Harmonic.completionJ = inj₁ tt
toPointedMarker (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.negativeTrit)) = inj₂ Pointed.northWestSite
toPointedMarker (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.zeroTrit)) = inj₂ Pointed.northSite
toPointedMarker (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.positiveTrit)) = inj₂ Pointed.northEastSite
toPointedMarker (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.negativeTrit)) = inj₂ Pointed.westSite
toPointedMarker (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.zeroTrit)) = inj₂ Pointed.centreSite
toPointedMarker (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.positiveTrit)) = inj₂ Pointed.eastSite
toPointedMarker (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.negativeTrit)) = inj₂ Pointed.southWestSite
toPointedMarker (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.zeroTrit)) = inj₂ Pointed.southSite
toPointedMarker (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.positiveTrit)) = inj₂ Pointed.southEastSite

fromPointedMarker : Pointed.MarkedOrUnmarkedSite → Harmonic.CoarseChannel
fromPointedMarker (inj₁ tt) = Harmonic.completionJ
fromPointedMarker (inj₂ Pointed.northWestSite) = Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.negativeTrit)
fromPointedMarker (inj₂ Pointed.northSite) = Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.zeroTrit)
fromPointedMarker (inj₂ Pointed.northEastSite) = Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.positiveTrit)
fromPointedMarker (inj₂ Pointed.westSite) = Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.negativeTrit)
fromPointedMarker (inj₂ Pointed.centreSite) = Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.zeroTrit)
fromPointedMarker (inj₂ Pointed.eastSite) = Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.positiveTrit)
fromPointedMarker (inj₂ Pointed.southWestSite) = Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.negativeTrit)
fromPointedMarker (inj₂ Pointed.southSite) = Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.zeroTrit)
fromPointedMarker (inj₂ Pointed.southEastSite) = Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.positiveTrit)

markerAfterChannel :
  (coarse : Harmonic.CoarseChannel) →
  fromPointedMarker (toPointedMarker coarse) ≡ coarse
markerAfterChannel Harmonic.completionJ = refl
markerAfterChannel (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.negativeTrit)) = refl
markerAfterChannel (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.zeroTrit)) = refl
markerAfterChannel (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.positiveTrit)) = refl
markerAfterChannel (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.negativeTrit)) = refl
markerAfterChannel (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.zeroTrit)) = refl
markerAfterChannel (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.positiveTrit)) = refl
markerAfterChannel (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.negativeTrit)) = refl
markerAfterChannel (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.zeroTrit)) = refl
markerAfterChannel (Harmonic.ordinaryChannel (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.positiveTrit)) = refl

channelAfterMarker :
  (marker : Pointed.MarkedOrUnmarkedSite) →
  toPointedMarker (fromPointedMarker marker) ≡ marker
channelAfterMarker (inj₁ tt) = refl
channelAfterMarker (inj₂ Pointed.northWestSite) = refl
channelAfterMarker (inj₂ Pointed.northSite) = refl
channelAfterMarker (inj₂ Pointed.northEastSite) = refl
channelAfterMarker (inj₂ Pointed.westSite) = refl
channelAfterMarker (inj₂ Pointed.centreSite) = refl
channelAfterMarker (inj₂ Pointed.eastSite) = refl
channelAfterMarker (inj₂ Pointed.southWestSite) = refl
channelAfterMarker (inj₂ Pointed.southSite) = refl
channelAfterMarker (inj₂ Pointed.southEastSite) = refl

toPointedJFine :
  Harmonic.ElementaryHarmonicChannel →
  Pointed.MarkedOrUnmarkedSite × (SelectedFive × CornerFour)
toPointedJFine (coarse , fine) =
  toPointedMarker coarse , unpackJFine fine

fromPointedJFine :
  Pointed.MarkedOrUnmarkedSite × (SelectedFive × CornerFour) →
  Harmonic.ElementaryHarmonicChannel
fromPointedJFine (marker , coordinates) =
  fromPointedMarker marker , packJFine coordinates

toAfterFromPointedJFine :
  (state : Pointed.MarkedOrUnmarkedSite × (SelectedFive × CornerFour)) →
  toPointedJFine (fromPointedJFine state) ≡ state
toAfterFromPointedJFine (marker , coordinates) =
  cong₂ _,_ (channelAfterMarker marker) (unpackAfterPackJFine coordinates)

fromAfterToPointedJFine :
  (state : Harmonic.ElementaryHarmonicChannel) →
  fromPointedJFine (toPointedJFine state) ≡ state
fromAfterToPointedJFine (coarse , fine) =
  cong₂ _,_ (markerAfterChannel coarse) (packAfterUnpackJFine fine)



------------------------------------------------------------------------
-- FULL POINTED-SHEET ISOMORPHISM, not just 10 coarse marker mapping.
-- The source Sheet3 and PhaseFineTable9 use differently named trit types,
-- so give an explicit coordinate codec instead of assuming definitional
-- equality. D4 sheet actions can then be transported through this chart,
-- but source C3^2 translations remain an independent action.
------------------------------------------------------------------------

toKernelTrit : Base.TriTruth → Triadic.KernelTrit
toKernelTrit Base.tri-low = Triadic.negativeTrit
toKernelTrit Base.tri-mid = Triadic.zeroTrit
toKernelTrit Base.tri-high = Triadic.positiveTrit

fromKernelTrit : Triadic.KernelTrit → Base.TriTruth
fromKernelTrit Triadic.negativeTrit = Base.tri-low
fromKernelTrit Triadic.zeroTrit = Base.tri-mid
fromKernelTrit Triadic.positiveTrit = Base.tri-high

baseAfterKernel : (t : Base.TriTruth) → fromKernelTrit (toKernelTrit t) ≡ t
baseAfterKernel Base.tri-low = refl
baseAfterKernel Base.tri-mid = refl
baseAfterKernel Base.tri-high = refl

kernelAfterBase : (t : Triadic.KernelTrit) → toKernelTrit (fromKernelTrit t) ≡ t
kernelAfterBase Triadic.negativeTrit = refl
kernelAfterBase Triadic.zeroTrit = refl
kernelAfterBase Triadic.positiveTrit = refl

toLiteralSheet : Fine.PhaseFineTable9 → Sheet.Sheet3
toLiteralSheet (Fine.phaseFineTable9 a b c d e f g h i) =
  Sheet.sheet3
    (toKernelTrit a) (toKernelTrit b) (toKernelTrit c)
    (toKernelTrit d) (toKernelTrit e) (toKernelTrit f)
    (toKernelTrit g) (toKernelTrit h) (toKernelTrit i)

fromLiteralSheet : Sheet.Sheet3 → Fine.PhaseFineTable9
fromLiteralSheet (Sheet.sheet3 a b c d e f g h i) =
  Fine.phaseFineTable9
    (fromKernelTrit a) (fromKernelTrit b) (fromKernelTrit c)
    (fromKernelTrit d) (fromKernelTrit e) (fromKernelTrit f)
    (fromKernelTrit g) (fromKernelTrit h) (fromKernelTrit i)

fromAfterToLiteralSheet :
  (sheet : Fine.PhaseFineTable9) →
  fromLiteralSheet (toLiteralSheet sheet) ≡ sheet
fromAfterToLiteralSheet (Fine.phaseFineTable9 a b c d e f g h i)
  rewrite baseAfterKernel a | baseAfterKernel b | baseAfterKernel c
        | baseAfterKernel d | baseAfterKernel e | baseAfterKernel f
        | baseAfterKernel g | baseAfterKernel h | baseAfterKernel i = refl

toAfterFromLiteralSheet :
  (sheet : Sheet.Sheet3) →
  toLiteralSheet (fromLiteralSheet sheet) ≡ sheet
toAfterFromLiteralSheet (Sheet.sheet3 a b c d e f g h i)
  rewrite kernelAfterBase a | kernelAfterBase b | kernelAfterBase c
        | kernelAfterBase d | kernelAfterBase e | kernelAfterBase f
        | kernelAfterBase g | kernelAfterBase h | kernelAfterBase i = refl

fineFromTable : Fine.PhaseFineTable9 → Harmonic.FineFrequency
fineFromTable table = Fine.encodeTritDigits (Fine.digitsFromTable table)

tableFromFine : Harmonic.FineFrequency → Fine.PhaseFineTable9
tableFromFine fine = Fine.tableFromDigits (Fine.decodeTritDigits fine)

tableAfterFineFromTable :
  (table : Fine.PhaseFineTable9) →
  tableFromFine (fineFromTable table) ≡ table
tableAfterFineFromTable table =
  trans
    (cong Fine.tableFromDigits
      (Fine.decodeAfterEncodeTritDigits (Fine.digitsFromTable table)))
    (Fine.tableAfterDigits table)

fineAfterTableFromFine :
  (fine : Harmonic.FineFrequency) →
  fineFromTable (tableFromFine fine) ≡ fine
fineAfterTableFromFine fine =
  trans
    (cong Fine.encodeTritDigits
      (Fine.digitsAfterTable (Fine.decodeTritDigits fine)))
    (Fine.encodeAfterDecodeTritDigits fine)

toActualPointedSheet :
  Harmonic.ElementaryHarmonicChannel → Pointed.PointedTernarySheet
toActualPointedSheet (coarse , fine) =
  toPointedMarker coarse , toLiteralSheet (tableFromFine fine)

fromActualPointedSheet :
  Pointed.PointedTernarySheet → Harmonic.ElementaryHarmonicChannel
fromActualPointedSheet (marker , sheet) =
  fromPointedMarker marker , fineFromTable (fromLiteralSheet sheet)

fromAfterToActualPointedSheet :
  (state : Harmonic.ElementaryHarmonicChannel) →
  fromActualPointedSheet (toActualPointedSheet state) ≡ state
fromAfterToActualPointedSheet (coarse , fine) =
  cong₂ _,_
    (markerAfterChannel coarse)
    (trans
      (cong fineFromTable
        (fromAfterToLiteralSheet (tableFromFine fine)))
      (fineAfterTableFromFine fine))

toAfterFromActualPointedSheet :
  (state : Pointed.PointedTernarySheet) →
  toActualPointedSheet (fromActualPointedSheet state) ≡ state
toAfterFromActualPointedSheet (marker , sheet) =
  cong₂ _,_
    (channelAfterMarker marker)
    (trans
      (cong toLiteralSheet
        (tableAfterFineFromTable (fromLiteralSheet sheet)))
      (toAfterFromLiteralSheet sheet))

-- A transported D4 action exists by conjugating the existing Pointed
-- action with the exact codec; it does NOT imply the new C5 rotation
-- is physically or canonically part of the original square symmetry.
transportedQuarterTurn :
  Harmonic.ElementaryHarmonicChannel →
  Harmonic.ElementaryHarmonicChannel
transportedQuarterTurn state =
  fromActualPointedSheet (Pointed.rotatePointedQuarter (toActualPointedSheet state))

------------------------------------------------------------------------
-- 79 is 3^4 - 2.  The F81 inverse theorem is a FINITE-FIELD result
-- tested by scripts/iit_jfine_selected_punctured79_audit.py;
-- the source PuncturedKernel4 has 80 nonzero four-trit states but this
-- module does NOT construct the field's binary multiplication in Agda.
------------------------------------------------------------------------

field81UnitCount : 3 * 3 * 3 * 3 ≡ 80 + 1
field81UnitCount = refl

inverseExponent79 : 79 + 1 ≡ 80
inverseExponent79 = refl

orderedUnequalNinePairs : 9 * 8 ≡ 72
orderedUnequalNinePairs = refl

pointedJFineCount :
  (9 + 1) * (3 * 3 * 3 * 3 * 3) * (3 * 3 * 3 * 3)
  ≡ 196830
pointedJFineCount = refl

record SelectedPunctured79AuthorityBoundary : Set where
  constructor selected-punctured79-authority-boundary
  field
    fivePlusFourExactlyRecoversJFine : Bool
    pointedMarkerIsomorphismConstructed : Bool
    eightyNonzeroFourTritSourceImported : Bool
    multiplicativeF81StructureKernelConstructed : Bool
    C5ActionIdentifiedWithC3SquaredTranslations : Bool
    pointedBulkProvedMonsterInvariant : Bool
    SSPPrime79Exists : Bool

canonicalSelectedPunctured79Boundary : SelectedPunctured79AuthorityBoundary
canonicalSelectedPunctured79Boundary =
  selected-punctured79-authority-boundary
    true true true false false false false
