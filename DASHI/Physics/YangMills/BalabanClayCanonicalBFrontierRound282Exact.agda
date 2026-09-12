{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound282Exact where

------------------------------------------------------------------------
-- ROUND282 / CANONICAL B FRONTIER AFTER R280-R281
--
-- R280 removes a coarse finite-covariance equality from the theorem ledger:
-- once F, G and FG expectations are same-object at each cutoff, covariance
-- equality is compiler algebra.
--
-- R281 removes the post-hoc continuum-covariance/spectrum equality: construct
-- the reconstructed spectrum with `connectedCorrelation` definitionally equal
-- to the exact continuum connected-covariance magnitude.
--
-- The canonical B consumer is still only:
--   (B1) quantitative continuum clustering upper;
--   (B2) positivity of the selected gap candidate.
--
-- On the finite-RG/expectation producer route, the surviving representation
-- work is now smaller and must not be confused with either theorem:
--   * exact finite T5/RG moment identity for F,G,FG;
--   * selected-test meaning;
--   * finite uniform clustering upper / good+exceptional control;
--   * spectral lower/rate semantics on the same continuum covariance carrier.
--
-- IMPORTANT CIRCULARITY FIREWALL:
-- Older `ReconstructedTransferTheory` records contain `spectralGapPositive` as
-- an INPUT.  Such a record cannot pay B2 unless an independent reconstruction
-- theorem shows that its stored gap/positivity is exactly the canonical gap
-- candidate without assuming the mass-gap conclusion.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Interop.IntrospectiveProofLoopExact as Introspective
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound275Exact as R275
import DASHI.Physics.YangMills.BalabanFiniteRGExpectationCovarianceSameObjectRound280Exact as R280
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281

data BSearchObject282 : Set where
  quantitativeContinuumClusteringUpper : BSearchObject282
  positiveCanonicalGapCandidate : BSearchObject282

  finiteExpectationMomentSameObject : BSearchObject282
  selectedCovarianceTestMeaning : BSearchObject282
  finiteUniformCorrelationUpper : BSearchObject282
  continuumSpectralRepresentationAndRate : BSearchObject282

  covarianceAlgebra : BSearchObject282
  continuumCovarianceSpectrumIdentity : BSearchObject282
  positiveTransferGap : BSearchObject282

searchRole282 : BSearchObject282 → Introspective.ProofSearchTargetRole
searchRole282 quantitativeContinuumClusteringUpper =
  Introspective.canonicalConsumerResidual
searchRole282 positiveCanonicalGapCandidate =
  Introspective.canonicalConsumerResidual

searchRole282 finiteExpectationMomentSameObject =
  Introspective.optionalProducerTactic
searchRole282 selectedCovarianceTestMeaning =
  Introspective.optionalProducerTactic
searchRole282 finiteUniformCorrelationUpper =
  Introspective.optionalProducerTactic
searchRole282 continuumSpectralRepresentationAndRate =
  Introspective.optionalProducerTactic

searchRole282 covarianceAlgebra = Introspective.compilerConsequence
searchRole282 continuumCovarianceSpectrumIdentity = Introspective.compilerConsequence
searchRole282 positiveTransferGap = Introspective.compilerConsequence

------------------------------------------------------------------------
-- Circularity firewall for legacy prepackaged positive-gap records.
------------------------------------------------------------------------

data StoredGapPositivityPaysCanonicalB2Permission : Set where

storedGapPositivityDoesNotPayCanonicalB2 :
  StoredGapPositivityPaysCanonicalB2Permission → ⊥
storedGapPositivityDoesNotPayCanonicalB2 ()

record Round282Boundary : Set where
  constructor round282-boundary
  field
    canonicalBStillTwoCoordinates : Bool
    canonicalBStillTwoCoordinatesIsTrue :
      canonicalBStillTwoCoordinates ≡ true

    finiteCovarianceEqualityPrimitive : Bool
    finiteCovarianceEqualityPrimitiveIsFalse :
      finiteCovarianceEqualityPrimitive ≡ false

    continuumSpectrumEqualityPrimitive : Bool
    continuumSpectrumEqualityPrimitiveIsFalse :
      continuumSpectrumEqualityPrimitive ≡ false

    finiteMomentIdentityIsRepresentationDebt : Bool
    finiteMomentIdentityIsRepresentationDebtIsTrue :
      finiteMomentIdentityIsRepresentationDebt ≡ true

    spectralLowerRateSemanticsStillPhysical : Bool
    spectralLowerRateSemanticsStillPhysicalIsTrue :
      spectralLowerRateSemanticsStillPhysical ≡ true

    storedLegacyGapPositivityCanCloseB2 : Bool
    storedLegacyGapPositivityCanCloseB2IsFalse :
      storedLegacyGapPositivityCanCloseB2 ≡ false

canonicalRound282Boundary : Round282Boundary
canonicalRound282Boundary =
  round282-boundary true refl false refl false refl true refl true refl false refl

round282FiniteCovarianceCompilerLevel : ProofLevel
round282FiniteCovarianceCompilerLevel = R280.round280FiniteMomentToCovarianceCompilerLevel

round282ContinuumSpectrumIdentityCompilerLevel : ProofLevel
round282ContinuumSpectrumIdentityCompilerLevel =
  R281.round281ContinuumCovarianceSpectrumConstructorLevel

round282CanonicalBCompilerLevel : ProofLevel
round282CanonicalBCompilerLevel = R275.round275CanonicalBCompilerLevel

round282QuantitativeClusteringLevel : ProofLevel
round282QuantitativeClusteringLevel = R275.round275QuantitativeClusteringLevel

round282PositiveGapCandidateLevel : ProofLevel
round282PositiveGapCandidateLevel = R275.round275PositiveGapCandidateLevel
