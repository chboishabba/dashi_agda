{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonDomainSourceRound338Exact where

------------------------------------------------------------------------
-- ROUND338 / CANONICAL COMMON-DOMAIN SOURCE ABI
--
-- R335/R337 correctly refuse to infer an abstract `AdmissibleSourcePair` from
-- bibliographic metadata.  R327, however, already shows that the selected
-- physical application needs no independent pair-membership theorem when the
-- admissibility predicate is chosen to be the canonical CMP116 common domain.
--
-- The least-privilege source-facing statement is therefore not
--
--   published localization + separate theorem connecting an abstract pair
--   predicate to the common J-domain,
--
-- but one published localization theorem stated directly on the canonical
-- common U,J domain manufactured by R104/R114.
--
-- On the selected physical carrier the bound values are rational and every
-- downstream consumer uses the ordinary rational order.  Therefore this ABI
-- also fixes the source order to `_≤_`; carrying a second abstract order and a
-- one-way order interpretation would be derived-intermediate inflation.
--
-- This owner packages exactly that source theorem shape and compiles it into
-- both the generic source ABI and the R335 pair-domain authority.  It adds no
-- analytic estimate and does not manufacture the source theorem by citation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Common
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as R104
import DASHI.Physics.YangMills.BalabanCMP116CanonicalRadiusToCommonDomainRound114Exact as R114
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116SelectedJPairDomainSourceFactorRound335Exact as R335

record CanonicalCommonDomainCMP116Source
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (demands : R104.CMP116FiniteNormalizedAnalyticDemands)
    : Set₁ where
  field
    differentiatedMagnitude :
      R318.Scale base → R318.Volume base →
      R318.SourceDirection base → R318.SourceDirection base → ℚ

    sourceRoot :
      R318.Scale base → R318.Volume base →
      R318.SourceDirection base → R318.SourceDirection base → R318.Root base

    sourceDistance :
      R318.SourceDirection base → R318.SourceDirection base → Nat

    sourceEnvelope :
      R318.Scale base → R318.Volume base → R318.Root base → Nat → ℚ

    SourceEnvelopeHasPositiveExponentialTreeDecay : Set
    sourceEnvelopeHasPositiveExponentialTreeDecay :
      SourceEnvelopeHasPositiveExponentialTreeDecay

    -- One source theorem payment, directly on the canonical common domain and
    -- directly in the selected rational order.
    differentiatedLocalizationOnCanonicalCommonDomain :
      ∀ scale volume leftJ rightJ →
      Common.SourceCoordinateInside
        (R114.canonicalCMP116CommonDomain
          {R318.Scale base} {R318.Volume base} demands)
        scale volume →
      differentiatedMagnitude scale volume leftJ rightJ
      ≤
      sourceEnvelope scale volume
        (sourceRoot scale volume leftJ rightJ)
        (sourceDistance leftJ rightJ)

open CanonicalCommonDomainCMP116Source public

canonicalSourceBuildsGenericPublishedSource :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands} →
  CanonicalCommonDomainCMP116Source base demands →
  Source.PublishedCMP116DifferentiatedLocalization
    (R318.Scale base)
    (R318.Volume base)
    (R318.Root base)
    (R318.SourceDirection base)
    ℚ
canonicalSourceBuildsGenericPublishedSource {base = base} {demands = demands} source = record
  { Source.PublishedCMP116DifferentiatedLocalization.LessEqual = _≤_
  ; Source.PublishedCMP116DifferentiatedLocalization.AdmissibleSourcePair =
      λ scale volume leftJ rightJ →
        Common.SourceCoordinateInside
          (R114.canonicalCMP116CommonDomain
            {R318.Scale base} {R318.Volume base} demands)
          scale volume
  ; Source.PublishedCMP116DifferentiatedLocalization.differentiatedMagnitude =
      differentiatedMagnitude source
  ; Source.PublishedCMP116DifferentiatedLocalization.sourceRoot =
      sourceRoot source
  ; Source.PublishedCMP116DifferentiatedLocalization.sourceDistance =
      sourceDistance source
  ; Source.PublishedCMP116DifferentiatedLocalization.sourceEnvelope =
      sourceEnvelope source
  ; Source.PublishedCMP116DifferentiatedLocalization.SourceEnvelopeHasPositiveExponentialTreeDecay =
      SourceEnvelopeHasPositiveExponentialTreeDecay source
  ; Source.PublishedCMP116DifferentiatedLocalization.sourceEnvelopeHasPositiveExponentialTreeDecay =
      sourceEnvelopeHasPositiveExponentialTreeDecay source
  ; Source.PublishedCMP116DifferentiatedLocalization.differentiatedLocalization =
      differentiatedLocalizationOnCanonicalCommonDomain source
  }

canonicalSourceBuildsPairDomainAuthority :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    (source : CanonicalCommonDomainCMP116Source base demands) →
  R335.PublishedCMP116CommonJPairDomainAuthority
    base
    (canonicalSourceBuildsGenericPublishedSource source)
    demands
canonicalSourceBuildsPairDomainAuthority source = record
  { R335.PublishedCMP116CommonJPairDomainAuthority.commonDeclaredJDomainAdmitsLiteralSourcePair =
      λ scale volume leftJ rightJ commonInside → commonInside
  }

record Round338Boundary : Set where
  constructor round338-boundary
  field
    abstractPairDomainReplayMandatoryAfterCanonicalSourceAlignment : Bool
    abstractPairDomainReplayMandatoryAfterCanonicalSourceAlignmentIsFalse :
      abstractPairDomainReplayMandatoryAfterCanonicalSourceAlignment ≡ false

    abstractSourceOrderTransportMandatoryOnSelectedRationalCarrier : Bool
    abstractSourceOrderTransportMandatoryOnSelectedRationalCarrierIsFalse :
      abstractSourceOrderTransportMandatoryOnSelectedRationalCarrier ≡ false

    canonicalCommonDomainMembershipCompilerOwned : Bool
    canonicalCommonDomainMembershipCompilerOwnedIsTrue :
      canonicalCommonDomainMembershipCompilerOwned ≡ true

    sourceDifferentiatedLocalizationStillProofBearing : Bool
    sourceDifferentiatedLocalizationStillProofBearingIsTrue :
      sourceDifferentiatedLocalizationStillProofBearing ≡ true

    citationMetadataCreatesCanonicalSourceTheorem : Bool
    citationMetadataCreatesCanonicalSourceTheoremIsFalse :
      citationMetadataCreatesCanonicalSourceTheorem ≡ false

    freshYMDecayEstimateIntroduced : Bool
    freshYMDecayEstimateIntroducedIsFalse :
      freshYMDecayEstimateIntroduced ≡ false

canonicalRound338Boundary : Round338Boundary
canonicalRound338Boundary =
  round338-boundary
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl

-- The source theorem is externally established at the CMP116 source boundary;
-- local construction/replay into this exact ABI remains an alignment task.
round338CanonicalSourceStatementAuthorityLevel : ProofLevel
round338CanonicalSourceStatementAuthorityLevel =
  Source.cmp116DifferentiatedLocalizationAuthorityLevel

round338CanonicalCommonDomainCompilerLevel : ProofLevel
round338CanonicalCommonDomainCompilerLevel =
  R114.cmp116FiniteDemandsToCommonRadiusObjectLevel

round338LocalCanonicalSourceAlignmentLevel : ProofLevel
round338LocalCanonicalSourceAlignmentLevel = conditional

round338CompilerLevel : ProofLevel
round338CompilerLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
