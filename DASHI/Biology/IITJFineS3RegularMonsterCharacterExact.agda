module DASHI.Biology.IITJFineS3RegularMonsterCharacterExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (cong; trans)

import Base369 as Base
import DASHI.Biology.JFinePhaseQuotientFieldExact as Fine
import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.IITJFineFourOneFourS3ZetaGaugeExact as Gauge
import DASHI.Moonshine.OggSSPP2F4RecenteredTriXorS3Exact as Ternary
import DASHI.Moonshine.Monster3BRegularC3BulkResidualFiftyThreeBidiExact as Monster

------------------------------------------------------------------------
-- NON-CARDINAL C3 CHAR BRIDGE, with an actual source-typed regular
-- C3 orbit coordinate on the existing Harmonic.ElementaryHarmonicChannel.
--
-- The model's C3 action is *defined* as adding one balanced ternary
-- unit to ALL NINE fine positions; it fixes the coarse marker.
-- The gauge normalization gives actual equivariant coordinates:
--      (coarse, 8 relative trits, centre).
-- The pointed carrier thus has 10 * 3^8 = 65610 free C3 orbits.
-- On complex linearisation this is 65610 copies of Reg(C3).
--
-- Monster's existing, independently attributed 3B CHARACTER states:
--   W|C3 = 53*1 + 65610*Reg(C3).
-- Their C3 characters are the same for the regular bulk, but no
-- chosen C3 intertwiner into the LITERAL Monster W is manufactured.
-- Full Monster or normalizer actions are NOT proved identical.
------------------------------------------------------------------------

ResidualEight : Set
ResidualEight = Gauge.FourTrit × Gauge.FourTrit

OrbitLabel : Set
OrbitLabel = Harmonic.CoarseChannel × ResidualEight

RegularC3State : Set
RegularC3State = OrbitLabel × Base.TriTruth

toRegularC3 :
  Harmonic.ElementaryHarmonicChannel → RegularC3State
toRegularC3 (coarse , fine)
  with Gauge.relativeGauge
    (Fine.tableFromDigits (Fine.decodeTritDigits fine))
... | Gauge.fourOneFour c e k =
  (coarse , (e , k)) , c

fromRegularC3 :
  RegularC3State → Harmonic.ElementaryHarmonicChannel
fromRegularC3 ((coarse , (e , k)) , c) =
  coarse ,
  Fine.encodeTritDigits
    (Fine.digitsFromTable
      (Gauge.restoreGauge (Gauge.fourOneFour c e k)))

regularAfterSource :
  (source : Harmonic.ElementaryHarmonicChannel) →
  fromRegularC3 (toRegularC3 source) ≡ source
regularAfterSource (coarse , fine)
  rewrite
    Gauge.restoreAfterRelativeGauge
      (Fine.tableFromDigits (Fine.decodeTritDigits fine))
  | Fine.digitsAfterTable (Fine.decodeTritDigits fine)
  = cong (λ value → coarse , value)
      (Fine.encodeAfterDecodeTritDigits fine)

sourceAfterRegular :
  (state : RegularC3State) →
  toRegularC3 (fromRegularC3 state) ≡ state
sourceAfterRegular ((coarse , (e , k)) , c)
  rewrite
    Fine.decodeAfterEncodeTritDigits
      (Fine.digitsFromTable
        (Gauge.restoreGauge (Gauge.fourOneFour c e k)))
  | Fine.tableAfterDigits
      (Gauge.restoreGauge (Gauge.fourOneFour c e k))
  | Gauge.relativeAfterRestoreGauge (Gauge.fourOneFour c e k)
  = refl

regularRotate : RegularC3State → RegularC3State
regularRotate (label , c) = label , Ternary.advance c

sourceRotate :
  Harmonic.ElementaryHarmonicChannel →
  Harmonic.ElementaryHarmonicChannel
sourceRotate (coarse , fine) =
  coarse ,
  Fine.encodeTritDigits
    (Fine.digitsFromTable
      (Gauge.rotateValues
        (Fine.tableFromDigits (Fine.decodeTritDigits fine))))

sourceRotationIntertwines :
  (source : Harmonic.ElementaryHarmonicChannel) →
  toRegularC3 (sourceRotate source)
  ≡ regularRotate (toRegularC3 source)
sourceRotationIntertwines (coarse , fine)
  rewrite
    Fine.decodeAfterEncodeTritDigits
      (Fine.digitsFromTable
        (Gauge.rotateValues
          (Fine.tableFromDigits (Fine.decodeTritDigits fine))))
  | Fine.tableAfterDigits
      (Gauge.rotateValues
        (Fine.tableFromDigits (Fine.decodeTritDigits fine)))
  | Gauge.globalValueRotationPreservesRelative
      (Fine.tableFromDigits (Fine.decodeTritDigits fine))
  = refl

regularRotationThree :
  (state : RegularC3State) →
  regularRotate (regularRotate (regularRotate state)) ≡ state
regularRotationThree ((coarse , (e , k)) , c)
  rewrite Gauge.rotateValueThree c = refl

------------------------------------------------------------------------
-- Character multiplicity identity only. No linearisation of the entire
-- literal Monster ambient module is assumed in the statements below.
------------------------------------------------------------------------

oneFineRelativeFibreIs6561 : 81 * 81 ≡ 6561
oneFineRelativeFibreIs6561 = refl

pointedOrbitLabelsAre65610 : 10 * 6561 ≡ Monster.regularC3Multiplicity
pointedOrbitLabelsAre65610 = refl

threeRegularPhaseDimensionsAre196830 :
  3 * Monster.regularC3Multiplicity ≡ 196830
threeRegularPhaseDimensionsAre196830 =
  Monster.regularC3BulkDimensionIs196830

fixedPhaseHasResidual53 :
  Monster.regularC3Multiplicity + 53 ≡ Monster.fixedPhaseMultiplicity
fixedPhaseHasResidual53 = Monster.fixedPhaseIsRegularPlusResidual

zetaSectorIsRegular :
  Monster.zetaPhaseMultiplicity ≡ Monster.regularC3Multiplicity
zetaSectorIsRegular = Monster.zetaPhaseIsRegular

inverseZetaSectorIsRegular :
  Monster.zetaSquaredPhaseMultiplicity ≡ Monster.regularC3Multiplicity
inverseZetaSectorIsRegular = Monster.zetaSquaredPhaseIsRegular

-- Character counts for the global *value-S3* permutation action.
-- Identity: 19683 fixed fine sheets.
-- 3-cycle: 0 (no globally translation-fixed sheet).
-- transposition: 1 (the unique constant sheet of its fixed value).
-- Standard character inner products give:
--   trivial = (19683+3)/6 = 3281
--   sign    = (19683-3)/6 = 3280
--   Std2    = 19683/3 = 6561.
-- These are numerical character formulas; a literal S3 representation
-- algebra/complex-module proof is an independent promotion gate.

s3TrivialMultiplicity : 6 * 3281 ≡ 19683 + 3
s3TrivialMultiplicity = refl

s3SignMultiplicity : 6 * 3280 + 3 ≡ 19683
s3SignMultiplicity = refl

s3StandardMultiplicity : 3 * 6561 ≡ 19683
s3StandardMultiplicity = refl

pointedStandardMatchesMonsterRegular : 10 * 6561 ≡ Monster.regularC3Multiplicity
pointedStandardMatchesMonsterRegular = refl

record S3C3CharacterIdentificationBoundary : Set where
  constructor s3-c3-character-identification-boundary
  field
    literalOriginalPointedC3SetCodecSourceWritten : Bool
    sourceRotationIntertwinerSourceWritten : Bool
    characterMultiplicityMatchesMonsterBulk : Bool
    originalMonster3BLiteralStateIntertwinerConstructed : Bool
    matchedNormalizerReflectionActionConstructed : Bool
    complexSemisimpleLinearisationKernelCertified : Bool
    F3EigenvaluesOneZetaZetaSquaredDistinct : Bool

canonicalBoundary : S3C3CharacterIdentificationBoundary
canonicalBoundary =
  s3-c3-character-identification-boundary
    true true true false false false false
