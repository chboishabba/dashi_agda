module DASHI.Cognition.PNF.SensibLawAuthorityTransformationMinimalCutExact where

------------------------------------------------------------------------
-- AUTHORITY TRANSFORMATIONS / MINIMAL LEGAL CUT SETS
--
-- This module implements the attachment's full-corpus target:
--   Authority = prerequisites + conclusion + exceptions + defeaters
--             + authority level + temporal scope.
-- It then classifies the minimum transformation needed to move a legal target
-- from unreachable to reachable without pretending that normative desirability
-- supplies an existing legal path.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawTypedLegalAuthorityEdgeExact as Edge
import DASHI.Cognition.PNF.SensibLawMaboRecognitionCreationFootholdExact as Mabo
import DASHI.Cognition.PNF.SensibLawClimateDutyRouteSearchExact as Climate

data AuthorityLevel : Set where
  constitutionalSupremacy : AuthorityLevel
  statute : AuthorityLevel
  bindingCase : AuthorityLevel
  persuasiveCase : AuthorityLevel
  commonLawRule : AuthorityLevel
  judicialPolicy : AuthorityLevel
  factualFinding : AuthorityLevel
  interpretiveInput : AuthorityLevel


data TemporalScope : Set where
  historical : TemporalScope
  current : TemporalScope
  prospective : TemporalScope
  sourceSpecific : TemporalScope


record AuthorityTransformation : Set where
  constructor authority-transformation
  field
    ruleId : String
    prerequisites : String
    conclusion : String
    exceptions : String
    defeaters : String
    level : AuthorityLevel
    temporalScope : TemporalScope
    source : Edge.SourceIdentity
    directSourceSupport : Bool
    dashReconstruction : Bool

open AuthorityTransformation public

------------------------------------------------------------------------
-- Priority / interaction. This is intentionally modest: where valid legislation
-- displaces inconsistent common law, the legal source graph must record the
-- displacement rather than flatten both to `Law`.
------------------------------------------------------------------------

data StatuteAndCommonLawAreSameAuthorityKind : Set where
statuteAndCommonLawStayTyped : StatuteAndCommonLawAreSameAuthorityKind → ⊥
statuteAndCommonLawStayTyped ()

record AuthorityInteraction : Set where
  constructor authority-interaction
  field
    higherRule : AuthorityTransformation
    lowerRule : AuthorityTransformation
    inconsistentOnTarget : Bool
    higherRuleControlsIfValidAndApplicable : Bool

open AuthorityInteraction public

------------------------------------------------------------------------
-- Minimal legal transformation taxonomy requested in the attachment.
------------------------------------------------------------------------

data TransformationClass : Set where
  newLegislationRequired : TransformationClass
  existingStatuteAlternativeConstruction : TransformationClass
  existingCommonLawCategoryExtension : TransformationClass
  precedentDistinctionUnstable : TransformationClass
  constitutionalConstraintChangesResult : TransformationClass
  internationalInterpretiveInputOnly : TransformationClass
  newCognisableHarmCategoryRequired : TransformationClass
  noChangeNeededExistingPath : TransformationClass


record MinimalCutResult : Set where
  constructor minimal-cut-result
  field
    target : String
    obstructionSet : String
    transformation : TransformationClass
    authorityToReopen : Edge.SourceIdentity
    reachableUnderCurrentAuthorities : Bool
    proofStillRequired : Bool

open MinimalCutResult public

maboPositiveCalibration : MinimalCutResult
maboPositiveCalibration = minimal-cut-result
  "recognition/survival of pre-existing native title"
  "automatic weld: sovereignty -> beneficial ownership of all land"
  noChangeNeededExistingPath
  Edge.maboAuthority
  true
  false

pabaiNegativeCalibration : MinimalCutResult
pabaiNegativeCalibration = minimal-cut-result
  "candidate Commonwealth duty for specified climate-attributed physical injury/death"
  "current negligence/public-authority duty cut set to be reconstructed from controlling authorities"
  existingCommonLawCategoryExtension
  Edge.pabaiAuthority
  false
  true

------------------------------------------------------------------------
-- Structural proof queries the system is allowed to answer.
------------------------------------------------------------------------

data MathematicsDecidesJustice : Set where
data NormativeStrengthMakesLegalPathReachable : Set where
data ParserCandidateIsAuthoritativeRule : Set where

mathDoesNotDecideJustice : MathematicsDecidesJustice → ⊥
mathDoesNotDecideJustice ()

normativeStrengthDoesNotCreatePath : NormativeStrengthMakesLegalPathReachable → ⊥
normativeStrengthDoesNotCreatePath ()

parserCandidateDoesNotBecomeAuthority : ParserCandidateIsAuthoritativeRule → ⊥
parserCandidateDoesNotBecomeAuthority ()

record StructuralProofCapability : Set where
  constructor structural-proof-capability
  field
    provePremisesSufficient : Bool
    proveEncodedPremiseNecessary : Bool
    detectEncodedAuthorityConflict : Bool
    proveEdgeRemovalCreatesPath : Bool
    proveNoPathWithoutRuleChangeOrLegislation : Bool
    decidesNormativeJustice : Bool

open StructuralProofCapability public

sensibLawStructuralCapability : StructuralProofCapability
sensibLawStructuralCapability = structural-proof-capability
  true true true true true false

------------------------------------------------------------------------
-- Positive / negative calibration pair.
------------------------------------------------------------------------

record CalibrationPair : Set where
  constructor calibration-pair
  field
    positiveCase : String
    positiveExpectedOperation : String
    negativeCase : String
    negativeExpectedOperation : String

open CalibrationPair public

maboPabaiCalibration : CalibrationPair
maboPabaiCalibration = calibration-pair
  "Mabo v Queensland (No 2)"
  "identify how a previously closed path reopens by decomposing an unnecessary common-law weld while preserving the sovereignty boundary"
  "Pabai v Commonwealth of Australia (No 2)"
  "identify the exact no-duty cut set and classify which changes are judicially available versus legislative"

------------------------------------------------------------------------
-- Direct cross-pollination into prior owners.
------------------------------------------------------------------------

maboKnownFootholdAlreadyEstablished :
  Mabo.resultAlreadyEstablished Mabo.maboKnownPositive ≡ true
maboKnownFootholdAlreadyEstablished = refl

climateCandidateStillNeedsProof :
  Mabo.resultAlreadyEstablished Mabo.climateCandidateSearch ≡ false
climateCandidateStillNeedsProof = refl

climateLargeClassStillNotLogicallyIndeterminate :
  Climate.LargeClassIsIndeterminateByDefinition → ⊥
climateLargeClassStillNotLogicallyIndeterminate =
  Climate.australianPopulationSizeDoesNotDefineIndeterminacy
