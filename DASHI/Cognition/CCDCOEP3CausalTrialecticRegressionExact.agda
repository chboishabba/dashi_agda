module DASHI.Cognition.CCDCOEP3CausalTrialecticRegressionExact where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import Base369 as Base
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Foundations.TernaryPermutationS3LawsExact as S3
import DASHI.Cognition.CCDCOEP3CausalTrialecticInteractionExact as P3
import DASHI.Cognition.CCDCOEP3SourcePowerEvidenceWeldExact as Source
import DASHI.Culture.JohnAnthonyBrownChildReligiousPowerBidiExact as Brown
import DASHI.Wikimedia.IbrahimSnowballAnthropologyClimateDenialPoliticalTheologyExact as Climate

twoPlusTwoPreserved :
  P3.additiveModel true true ≡ 4
twoPlusTwoPreserved = P3.literalArithmeticIntact

interactionAddsIndependentDimension :
  P3.jointModel true true ≡ 5
interactionAddsIndependentDimension = P3.selectedNonadditiveOutcome

interactionCannotFactor :
  NF.FactorsThrough P3.reportedAdditive P3.situatedOutcome → ⊥
interactionCannotFactor =
  P3.interactionCannotBeRecoveredFromAdditiveReport

originalS3Reverse :
  Perm.applyPermutation
    (Perm.inversePermutation Perm.permRotate)
    (Perm.applyPermutation Perm.permRotate Base.tri-low)
  ≡ Base.tri-low
originalS3Reverse =
  P3.sixReorientationsReversible Perm.permRotate Base.tri-low

originalS3OrderObstruction :
  S3._∙_ Perm.permRotate Perm.permSwapLowMid
  ≡ S3._∙_ Perm.permSwapLowMid Perm.permRotate → ⊥
originalS3OrderObstruction = P3.orderOfS3OperationsMatters

causalWorldsLookIdentical :
  P3.observedPairFor P3.directEffect
  ≡ P3.observedPairFor P3.commonCause
causalWorldsLookIdentical = P3.observedDistributionsIdentical

selectedProbeDoesSeparate :
  Discriminator.BundleSeparates
    P3.counterfactualDistinguishingProbe
    P3.directEffect P3.commonCause
selectedProbeDoesSeparate = P3.counterfactualProbeSeparates

noCausalInferenceFromObservationsAlone :
  NF.FactorsThrough P3.observedPairFor P3.interventionalProbe → ⊥
noCausalInferenceFromObservationsAlone =
  P3.observationalAssociationDoesNotIdentifyCausation

noIntentFromMeasuredEffectAlone :
  NF.FactorsThrough P3.observedEffect P3.worldPurpose → ⊥
noIntentFromMeasuredEffectAlone =
  P3.effectCannotIdentifyHostilePurpose

coherenceDoesNotFixEpistemicRevision :
  NF.FactorsThrough P3.publicCoherence P3.evidenceRevision → ⊥
coherenceDoesNotFixEpistemicRevision =
  P3.narrativeCoherenceDoesNotDetermineRevisability

denialSurfaceCannotIdentifyMeaning :
  NF.FactorsThrough Climate.projectDenialSurface
    Climate.denialSocialReading → ⊥
denialSurfaceCannotIdentifyMeaning =
  Source.climateDenialLabelCannotIdentifySocialCause

brownInstitutionalPowerIsOriginalAxis :
  Brown.BrownPaperClaim.axis Brown.institutionalHegemonyClaim
  ≡ Brown.institutionalPower
brownInstitutionalPowerIsOriginalAxis =
  Source.brownPaperContainsInstitutionalHegemonyAxis
