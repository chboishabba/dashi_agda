{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalB12Round446Exact where

------------------------------------------------------------------------
-- B / ROUND446: PREFERRED B1+B2 SOURCE OBJECT.
--
-- R444 makes retained fibres nonempty and both J/source marks structural.
-- R445 identifies the absolute selected R429 boundary with the embedded literal
-- mixed-log magnitude and compiles that to the exact finite connected covariance.
--
-- This owner packages those two independent source facts on ONE canonical
-- twice-marked four-stage object.  No new estimate is introduced.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.BalabanCMP116CanonicalTwiceMarkedFourStageRound444Exact as R444
import DASHI.Physics.YangMills.BalabanCMP116R429MixedLogResponseRound445Exact as R445
import DASHI.Physics.YangMills.BalabanCMP116CanonicalSelectedBSourceRound435Exact as R435

record CanonicalB12Source
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base)
    (embedding : Embed.OrderedRationalRealEmbedding)
    : Set₁ where
  field
    response :
      R445.R429LiteralMixedLogResponse
        (R444.asR429 data)
        embedding

open CanonicalB12Source public

canonicalSelectedSource :
  ∀ {Measure TestObservable dataSet extension base data embedding} →
  CanonicalB12Source
    {Measure = Measure} {TestObservable = TestObservable}
    {dataSet = dataSet} {extension = extension} {base = base}
    data embedding →
  R435.CanonicalSelectedBSource (R444.asR429 data)
canonicalSelectedSource {data = data} source =
  R444.asR435 data

round446B1MixedLogResponseLevel : ProofLevel
round446B1MixedLogResponseLevel = machineChecked

round446B2TwiceMarkedNonemptyLevel : ProofLevel
round446B2TwiceMarkedNonemptyLevel = machineChecked

-- Remaining physical/source input represented by this package:
--   * construct the literal twice-marked CMP116 terms and canonical R410 replay;
--   * identify the resulting selected boundary magnitude with the literal
--     mixed two-J log response.
-- B2 itself is no longer an independent theorem on this preferred carrier.
literalRound446CanonicalB12SourceLevel : ProofLevel
literalRound446CanonicalB12SourceLevel = conditional
