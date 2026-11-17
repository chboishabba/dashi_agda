module DASHI.Biology.IITJFineHeisenbergFourPairSubgroupExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import Base369 as Base
import DASHI.Biology.JFinePhaseQuotientFieldExact as Fine
import DASHI.Biology.IITJFineFourOneFourS3ZetaGaugeExact as Gauge
import DASHI.Biology.IITJFineD4EquivariantHeisenbergGaugeExact as Spatial
import DASHI.Moonshine.OggSSPP2F4RecenteredTriXorS3Exact as Ternary
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H6

------------------------------------------------------------------------
-- STRONGER SOURCE-SAME-CARRIER INTERPRETATION:
--
-- The actual jFine centre-gauged 4+1+4 carrier has an OPTIONAL group law
-- H4 = F3^4 x F3 x F3^4, size 3^(1+8)=19683, given by the usual
-- Heisenberg cocycle b · a'. Its three-element central coordinate is
-- literally the balanced-value C3 gauge (translation of all nine raw
-- trits). The two four-trit blocks are edge and corner RELATIVE values.
--
-- The existing Monster3BFiniteHeisenbergCentralExtensionExact owns H6
-- with six translation and six modulation coordinates, order 3^13,
-- and already has source-level group-law, cocycle and nondegeneracy work.
-- Embed the H4 coordinate carrier into the FIRST FOUR coordinates of
-- that MODEL; require two trailing zeros. This is a genuine explicit
-- subcarrier of the source model, NOT an intertwiner into the Monster
-- irreducible representation W, or identity with the Monster normalizer.
--
-- IMPORTANT OBSTRUCTIONS:
--  * The original raw value S3 sign x -> -x is NOT an automorphism of
--    this chosen H4 multiplication. Its C3 subgroup acts by CENTRAL
--    left translation, which is not itself a group automorphism.
--  * The original D4 spatial mirror, while preserving the 4+1+4
--    partition, does NOT preserve the chosen edge/corner dot cocycle.
--  * The complex zeta/zetasquared H4 irreps have degree 3^4=81,
--    but F3 itself has no distinct cube roots of unity.
------------------------------------------------------------------------

toModelTrit : Base.TriTruth → Trit
toModelTrit Base.tri-low = neg
toModelTrit Base.tri-mid = zer
toModelTrit Base.tri-high = pos

fromModelTrit : Trit → Base.TriTruth
fromModelTrit neg = Base.tri-low
fromModelTrit zer = Base.tri-mid
fromModelTrit pos = Base.tri-high

fromAfterToTrit :
  (value : Base.TriTruth) →
  fromModelTrit (toModelTrit value) ≡ value
fromAfterToTrit Base.tri-low = refl
fromAfterToTrit Base.tri-mid = refl
fromAfterToTrit Base.tri-high = refl

toAfterFromTrit :
  (value : Trit) → toModelTrit (fromModelTrit value) ≡ value
toAfterFromTrit neg = refl
toAfterFromTrit zer = refl
toAfterFromTrit pos = refl

embedFourCoordinates : Gauge.FourTrit → G.X6
embedFourCoordinates (Gauge.fourTrit a b c d) =
  G.x6 (toModelTrit a) (toModelTrit b)
       (toModelTrit c) (toModelTrit d) zer zer

projectFourCoordinates : G.X6 → Gauge.FourTrit
projectFourCoordinates (G.x6 a b c d e f) =
  Gauge.fourTrit (fromModelTrit a) (fromModelTrit b)
                 (fromModelTrit c) (fromModelTrit d)

projectAfterEmbedFour :
  (x : Gauge.FourTrit) →
  projectFourCoordinates (embedFourCoordinates x) ≡ x
projectAfterEmbedFour (Gauge.fourTrit a b c d)
  rewrite fromAfterToTrit a | fromAfterToTrit b
        | fromAfterToTrit c | fromAfterToTrit d = refl

embedRelativeH4IntoSourceH6 : Gauge.FourOneFour → H6.Heisenberg6
embedRelativeH4IntoSourceH6 (Gauge.fourOneFour c edge corner) =
  H6.heisenberg6
    (H6.symplectic12
      (embedFourCoordinates edge)
      (embedFourCoordinates corner))
    (toModelTrit c)

projectSourceH6ToRelativeH4 : H6.Heisenberg6 → Gauge.FourOneFour
projectSourceH6ToRelativeH4
  (H6.heisenberg6 (H6.symplectic12 translations modulations) phase) =
  Gauge.fourOneFour
    (fromModelTrit phase)
    (projectFourCoordinates translations)
    (projectFourCoordinates modulations)

projectAfterEmbedH4 :
  (q : Gauge.FourOneFour) →
  projectSourceH6ToRelativeH4 (embedRelativeH4IntoSourceH6 q) ≡ q
projectAfterEmbedH4 (Gauge.fourOneFour c
    (Gauge.fourTrit a b d e)
    (Gauge.fourTrit f g h i))
  rewrite fromAfterToTrit c
        | fromAfterToTrit a | fromAfterToTrit b
        | fromAfterToTrit d | fromAfterToTrit e
        | fromAfterToTrit f | fromAfterToTrit g
        | fromAfterToTrit h | fromAfterToTrit i = refl

-- The input is the existing ORIGINAL nine-trit source, not a synthetic
-- newly named 19683-element copy.
sourceSheetToModelH4 :
  Fine.PhaseFineTable9 → H6.Heisenberg6
sourceSheetToModelH4 sheet =
  embedRelativeH4IntoSourceH6 (Gauge.relativeGauge sheet)

modelH4ToSourceSheet :
  H6.Heisenberg6 → Fine.PhaseFineTable9
modelH4ToSourceSheet model =
  Gauge.restoreGauge (projectSourceH6ToRelativeH4 model)

sheetAfterModelRoundTrip :
  (sheet : Fine.PhaseFineTable9) →
  modelH4ToSourceSheet (sourceSheetToModelH4 sheet) ≡ sheet
sheetAfterModelRoundTrip sheet =
  trans
    (cong Gauge.restoreGauge
      (projectAfterEmbedH4 (Gauge.relativeGauge sheet)))
    (Gauge.restoreAfterRelativeGauge sheet)

embeddedTranslationTailZero :
  (q : Gauge.FourOneFour) →
  G.x4 (H6.translationPart
      (H6.quotient (embedRelativeH4IntoSourceH6 q))) ≡ zer
embeddedTranslationTailZero (Gauge.fourOneFour c e k) = refl

embeddedModulationTailZero :
  (q : Gauge.FourOneFour) →
  G.x5 (H6.modulationPart
      (H6.quotient (embedRelativeH4IntoSourceH6 q))) ≡ zer
embeddedModulationTailZero (Gauge.fourOneFour c e k) = refl

-- This group law is pulled back from the SOURCE Heisenberg6 model.
-- The same-law finite numerical script checks all 19683 group states,
-- all 6560 nonzero quotient witnesses, the 729 scalar cocycle cases,
-- and the source six-pair zero-tail embedding.
modelProduct4 : Gauge.FourOneFour → Gauge.FourOneFour → Gauge.FourOneFour
modelProduct4 a b =
  projectSourceH6ToRelativeH4
    (H6.compose (embedRelativeH4IntoSourceH6 a)
                (embedRelativeH4IntoSourceH6 b))

modelIdentity4 : Gauge.FourOneFour
modelIdentity4 =
  Gauge.fourOneFour Base.tri-mid
    (Gauge.fourTrit Base.tri-mid Base.tri-mid
                    Base.tri-mid Base.tri-mid)
    (Gauge.fourTrit Base.tri-mid Base.tri-mid
                    Base.tri-mid Base.tri-mid)

modelCentreGenerator : Gauge.FourOneFour
modelCentreGenerator =
  Gauge.fourOneFour Base.tri-high
    (Gauge.fourTrit Base.tri-mid Base.tri-mid
                    Base.tri-mid Base.tri-mid)
    (Gauge.fourTrit Base.tri-mid Base.tri-mid
                    Base.tri-mid Base.tri-mid)

sourceCentralShift : Gauge.FourOneFour → Gauge.FourOneFour
sourceCentralShift (Gauge.fourOneFour c e k) =
  Gauge.fourOneFour (Ternary.advance c) e k

centralShiftEqualsSourceModelProduct :
  (q : Gauge.FourOneFour) →
  modelProduct4 modelCentreGenerator q ≡ sourceCentralShift q
centralShiftEqualsSourceModelProduct
  (Gauge.fourOneFour Base.tri-low
    (Gauge.fourTrit a b d e) (Gauge.fourTrit f g h i))
  rewrite fromAfterToTrit a | fromAfterToTrit b
        | fromAfterToTrit d | fromAfterToTrit e
        | fromAfterToTrit f | fromAfterToTrit g
        | fromAfterToTrit h | fromAfterToTrit i = refl
centralShiftEqualsSourceModelProduct
  (Gauge.fourOneFour Base.tri-mid
    (Gauge.fourTrit a b d e) (Gauge.fourTrit f g h i))
  rewrite fromAfterToTrit a | fromAfterToTrit b
        | fromAfterToTrit d | fromAfterToTrit e
        | fromAfterToTrit f | fromAfterToTrit g
        | fromAfterToTrit h | fromAfterToTrit i = refl
centralShiftEqualsSourceModelProduct
  (Gauge.fourOneFour Base.tri-high
    (Gauge.fourTrit a b d e) (Gauge.fourTrit f g h i))
  rewrite fromAfterToTrit a | fromAfterToTrit b
        | fromAfterToTrit d | fromAfterToTrit e
        | fromAfterToTrit f | fromAfterToTrit g
        | fromAfterToTrit h | fromAfterToTrit i = refl

-- Concrete noncommutativity / non-equivariance tests use source D4
-- and value-S3 transformations on the original relative gauge.
zeroFour : Gauge.FourTrit
zeroFour =
  Gauge.fourTrit Base.tri-mid Base.tri-mid
                 Base.tri-mid Base.tri-mid

basisFirstFour : Gauge.FourTrit
basisFirstFour =
  Gauge.fourTrit Base.tri-high Base.tri-mid
                 Base.tri-mid Base.tri-mid

modulationNW : Gauge.FourOneFour
modulationNW = Gauge.fourOneFour Base.tri-mid zeroFour basisFirstFour

translationN : Gauge.FourOneFour
translationN = Gauge.fourOneFour Base.tri-mid basisFirstFour zeroFour

sourceD4MirrorDoesNotPreserveChosenProduct :
  Spatial.mirrorRelative (modelProduct4 modulationNW translationN)
  ≡ modelProduct4
       (Spatial.mirrorRelative modulationNW)
       (Spatial.mirrorRelative translationN) → ⊥
sourceD4MirrorDoesNotPreserveChosenProduct ()

sourceValueSignDoesNotPreserveChosenProduct :
  Gauge.reflectGauge (modelProduct4 modulationNW translationN)
  ≡ modelProduct4
       (Gauge.reflectGauge modulationNW)
       (Gauge.reflectGauge translationN) → ⊥
sourceValueSignDoesNotPreserveChosenProduct ()

------------------------------------------------------------------------
-- Character-DIMENSION targets: existing 3B source owns a DIFFERENT
-- six-pair extraspecial group of order 3^13, nonlinear degree 3^6=729.
-- The four-pair SOURCE subgroup model has nonlinear degree 3^4=81,
-- and the 729 basis of its six-pair Schrödinger model decomposes into
-- 3^2=9 coordinate blocks of degree 81, because the first four axis
-- generators preserve the last two coordinates. Actual Monster-module
-- restriction is an independent intertwiner obligation.
------------------------------------------------------------------------

fourPairCharacterDegreeSquareSum :
  6561 + 2 * (81 * 81) ≡ 19683
fourPairCharacterDegreeSquareSum = refl

pointedCentralOrbitLabels :
  10 * 6561 ≡ 65610
pointedCentralOrbitLabels = refl

nestedModelBasisSplit : 9 * 81 ≡ 729
nestedModelBasisSplit = refl

pointedZetaAsFourPairDegrees : 810 * 81 ≡ 65610
pointedZetaAsFourPairDegrees = refl

record HeisenbergFourPairAuthorityBoundary : Set where
  constructor heisenberg-four-pair-authority-boundary
  field
    literalSourceH4CoordinateEmbeddingConstructed : Bool
    exactSheetSourceReopeningConstructed : Bool
    originalSourceH6OwnerReused : Bool
    structuralFourPairGroupLawDerivedFromSourceH6 : Bool
    standaloneAllH4GroupLawsKernelProved : Bool
    sourceS3SignAndD4MirrorAreGroupAutomorphisms : Bool
    originalMonster3BRepresentationIntertwiner : Bool
    actualPhysicalQuantumCentralCharacterProved : Bool

canonicalFourPairBoundary : HeisenbergFourPairAuthorityBoundary
canonicalFourPairBoundary =
  heisenberg-four-pair-authority-boundary
    true true true true false false false false
