{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R429MixedLogResponseRound445Exact where

------------------------------------------------------------------------
-- B / ROUND445: CANONICAL R429 SELECTED BOUNDARY = LITERAL TWO-J RESPONSE
-- AT THE MAGNITUDE STRENGTH ACTUALLY CONSUMED BY THE MASS-GAP ROUTE.
--
-- R429's selectedBoundaryIntegrand lives on the abstract real carrier, while
-- the finite T5 mixed-log response/covariance lives on ℚ.  The mass-gap proof
-- never needs a signed carrier equality across that boundary: R406/R405 and all
-- downstream clustering estimates consume |selectedBoundaryIntegrand|.
--
-- Therefore the honest same-object theorem is
--
--   |selectedBoundaryIntegrand|
--     = embed ( magnitude (D_{J_L} D_{J_R} log Z) ).
--
-- R341 already proves the literal mixed-log magnitude is exactly the selected
-- finite connected-covariance magnitude.  This owner transports that compiler
-- through the ordered rational->real embedding.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (absℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116CanonicalFourStageR406Round429Exact as R429
import DASHI.Physics.YangMills.BalabanCMP116R281ModeSelectedDirectRound341Exact as R341
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed

record R429LiteralMixedLogResponse
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (fourStage :
      R429.CanonicalFourStageR406Data
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base)
    (embedding : Embed.OrderedRationalRealEmbedding)
    : Set₁ where
  field
    cutoff : Nat

    -- The genuine B1 same-object payment, stated at exactly the magnitude
    -- strength consumed by the selected localization/clustering chain.
    selectedBoundaryMagnitudeIsLiteralMixedLogMagnitude :
      absℝ (R429.selectedBoundaryIntegrand fourStage)
      ≡
      Embed.embed embedding
        (R278.magnitude extension
          (Cumulant.literalMixedSecondLogDerivative (R318.meaning base)
            (R429.leftJ fourStage)
            (R429.rightJ fourStage)
            cutoff))

open R429LiteralMixedLogResponse public

literalDirectionsMagnitudeIsFiniteSelectedCovariance :
  ∀ {Measure TestObservable dataSet extension base fourStage embedding}
    (response :
      R429LiteralMixedLogResponse
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        fourStage embedding) →
  R278.magnitude extension
    (Cumulant.literalMixedSecondLogDerivative (R318.meaning base)
      (R429.leftJ fourStage)
      (R429.rightJ fourStage)
      (cutoff response))
  ≡
  R278.connectedCovarianceMagnitude extension
    (Gram.measureSequence dataSet (cutoff response))
    (R429.leftObservable fourStage)
    (R429.rightObservable fourStage)
literalDirectionsMagnitudeIsFiniteSelectedCovariance
    {base = base} {fourStage = fourStage} response
  rewrite R429.leftJIsObservableIndexed fourStage
        | R429.rightJIsObservableIndexed fourStage =
  R341.mixedLogMagnitudeIsFiniteSelectedCovarianceMagnitude
    base
    (cutoff response)
    (R429.leftObservable fourStage)
    (R429.rightObservable fourStage)

selectedBoundaryMagnitudeIsEmbeddedFiniteCovariance :
  ∀ {Measure TestObservable dataSet extension base fourStage embedding}
    (response :
      R429LiteralMixedLogResponse
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        fourStage embedding) →
  absℝ (R429.selectedBoundaryIntegrand fourStage)
  ≡
  Embed.embed embedding
    (R278.connectedCovarianceMagnitude extension
      (Gram.measureSequence dataSet (cutoff response))
      (R429.leftObservable fourStage)
      (R429.rightObservable fourStage))
selectedBoundaryMagnitudeIsEmbeddedFiniteCovariance
    {embedding = embedding} response =
  trans
    (selectedBoundaryMagnitudeIsLiteralMixedLogMagnitude response)
    (cong (Embed.embed embedding)
      (literalDirectionsMagnitudeIsFiniteSelectedCovariance response))

round445MixedLogToFiniteCovarianceCompilerLevel : ProofLevel
round445MixedLogToFiniteCovarianceCompilerLevel = R341.round341CompilerLevel

round445RationalRealResponseTransportLevel : ProofLevel
round445RationalRealResponseTransportLevel = machineChecked

-- B1 is now reduced to exactly one physical/source identity at the correct
-- carrier strength: the absolute canonical R429 selected boundary is the
-- embedded magnitude of the literal twice-J mixed log response.
literalRound445R429SelectedBoundaryMixedLogIdentificationLevel : ProofLevel
literalRound445R429SelectedBoundaryMixedLogIdentificationLevel = conditional
