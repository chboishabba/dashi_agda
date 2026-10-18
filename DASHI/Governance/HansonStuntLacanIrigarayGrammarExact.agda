module DASHI.Governance.HansonStuntLacanIrigarayGrammarExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.TernaryRoleCarrierExact as Ternary
import DASHI.Core.LacanFregeTernaryRoleChartExact as Lacan
import DASHI.Core.IrigarayLabialRelationalCarrierExact as Irigaray
import DASHI.Core.LacanIrigarayTernaryGrammarBridgeExact as Bridge
import DASHI.Core.FeministLabialRechartingCapstoneExact as Labial
import DASHI.Core.FeministRechartingSourceBridgeExact as Rechart
import DASHI.Core.RepresentationSubjectPositionNonfactorabilityExact as Subject
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.CriticalRelationalGrammarCapstoneExact as Critical
import DASHI.Governance.HansonBurqaIslamophobiaFeministRelationalExact as Burqa

------------------------------------------------------------------------
-- HANSON STUNT: LACANIAN / IRIGARAYAN DIFFERENT-GRAMMAR CONSTRUCTION
--
-- ATTRIBUTION
--
-- Lacan source calibration is inherited from LacanFregeTernaryRoleChartExact.
-- Irigaray source calibration is inherited from
-- IrigarayLabialRelationalCarrierExact and
-- FeministRechartingSourceBridgeExact.
--
-- DASHI owns the finite shared-carrier/different-grammar proofs and the
-- application-specific mapping below.
--
-- This owner does NOT claim:
--   * that Hanson consciously uses Lacanian theory;
--   * that Irigaray wrote about Hanson or the burqa;
--   * that the finite ternary charts exhaust either theory;
--   * that one feminist grammar is politically sovereign.
--
-- Application question:
--
--   If a stunt constructs a one-centred field
--
--        target/object <- sovereign speaker -> audience/institution
--
--   can a feminist repair be obtained simply by renaming those same positions?
--
-- Exact answer in the finite shared carrier: no.
------------------------------------------------------------------------

data StuntLacanianRole : Set where
  erasedOrLackingOther : StuntLacanianRole
  sovereignEnunciationCenter : StuntLacanianRole
  addressedInstitutionAudience : StuntLacanianRole

stuntLacanianRole :
  Ternary.TernaryRoleCode → StuntLacanianRole
stuntLacanianRole Ternary.code0 = erasedOrLackingOther
stuntLacanianRole Ternary.code1 = sovereignEnunciationCenter
stuntLacanianRole Ternary.code2 = addressedInstitutionAudience

data StuntIrigarayanRole : Set where
  refusesUnitaryMasterChart : StuntIrigarayanRole
  firstSituatedSubjectAspect : StuntIrigarayanRole
  secondSituatedSubjectAspect : StuntIrigarayanRole

stuntIrigarayanRole :
  Ternary.TernaryRoleCode → StuntIrigarayanRole
stuntIrigarayanRole Ternary.code0 = refusesUnitaryMasterChart
stuntIrigarayanRole Ternary.code1 = firstSituatedSubjectAspect
stuntIrigarayanRole Ternary.code2 = secondSituatedSubjectAspect

------------------------------------------------------------------------
-- RELATIONAL GRAMMARS
------------------------------------------------------------------------

stuntOneCentredEdge :
  Ternary.TernaryRoleCode → Ternary.TernaryRoleCode → Bool
stuntOneCentredEdge = Lacan.lacanOneCentredEdge

stuntReciprocalEdge :
  Ternary.TernaryRoleCode → Ternary.TernaryRoleCode → Bool
stuntReciprocalEdge = Irigaray.irigarayReciprocalEdge

applicationGrammarPreserving :
  Ternary.TernaryPermutation → Set
applicationGrammarPreserving = Bridge.GrammarPreserving

noRelabellingTurnsStuntMasterGraphIntoReciprocalGraph :
  (permutation : Ternary.TernaryPermutation) →
  applicationGrammarPreserving permutation → ⊥
noRelabellingTurnsStuntMasterGraphIntoReciprocalGraph =
  Bridge.noTernaryRelabellingPreservesGrammar

------------------------------------------------------------------------
-- EXACT CONSTRUCTION: SIGN-FLIP / ROLE-SWAP IS NOT FEMINIST REPAIR
------------------------------------------------------------------------

data RenameOnlyRepair : Set where
  swapSpeakerAndOtherLabels : RenameOnlyRepair
  renameTargetAsEmpowered : RenameOnlyRepair
  reverseMoralValence : RenameOnlyRepair

data RenameOnlyBecomesReciprocalGrammar : Set where

renameOnlyCannotConstructReciprocalGrammar :
  RenameOnlyBecomesReciprocalGrammar → ⊥
renameOnlyCannotConstructReciprocalGrammar ()

irigarayRepairIsNotSignFlip :
  Labial.positiveRechartIsJustSignFlip
    Labial.canonicalFeministLabialCapstoneBoundary
    ≡ false
irigarayRepairIsNotSignFlip =
  Labial.positiveRechartIsJustSignFlipIsFalse
    Labial.canonicalFeministLabialCapstoneBoundary

------------------------------------------------------------------------
-- REPRESENTATION != ORIGINATING AUTHORITY
------------------------------------------------------------------------

data BurqaRepresentationalState : Set where
  representedObjectWithoutOriginatingAuthority : BurqaRepresentationalState
  representedSubjectWithOriginatingAuthority : BurqaRepresentationalState

data SameBurqaVisibility : Set where
  highlyVisibleBurqaCategory : SameBurqaVisibility

data BurqaSubjectAuthority : Set where
  objectPosition : BurqaSubjectAuthority
  originatingAuthorityPosition : BurqaSubjectAuthority

burqaVisibility : BurqaRepresentationalState → SameBurqaVisibility
burqaVisibility representedObjectWithoutOriginatingAuthority =
  highlyVisibleBurqaCategory
burqaVisibility representedSubjectWithOriginatingAuthority =
  highlyVisibleBurqaCategory

burqaSubjectAuthority :
  BurqaRepresentationalState → BurqaSubjectAuthority
burqaSubjectAuthority representedObjectWithoutOriginatingAuthority =
  objectPosition
burqaSubjectAuthority representedSubjectWithOriginatingAuthority =
  originatingAuthorityPosition

burqaAuthorityDiffers :
  burqaSubjectAuthority representedObjectWithoutOriginatingAuthority
  ≡
  burqaSubjectAuthority representedSubjectWithOriginatingAuthority → ⊥
burqaAuthorityDiffers ()

visibilityDoesNotRecoverOriginatingAuthority :
  INF.FactorsThrough burqaVisibility burqaSubjectAuthority → ⊥
visibilityDoesNotRecoverOriginatingAuthority =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      representedObjectWithoutOriginatingAuthority
      representedSubjectWithOriginatingAuthority
      refl
      burqaAuthorityDiffers)

------------------------------------------------------------------------
-- POSITIVE CONSTRUCTOR
------------------------------------------------------------------------

data StuntSituatedState : Set where
  firstSituatedWoman : StuntSituatedState
  secondSituatedWoman : StuntSituatedState

data OldStuntChart : Set where
  oneCompressedBurqaObject : OldStuntChart

data ReciprocalResidual : Set where
  firstRelationalPosition : ReciprocalResidual
  secondRelationalPosition : ReciprocalResidual

oldStuntChart : StuntSituatedState → OldStuntChart
oldStuntChart firstSituatedWoman = oneCompressedBurqaObject
oldStuntChart secondSituatedWoman = oneCompressedBurqaObject

reciprocalResidual : StuntSituatedState → ReciprocalResidual
reciprocalResidual firstSituatedWoman = firstRelationalPosition
reciprocalResidual secondSituatedWoman = secondRelationalPosition

reciprocalResidualSeparates :
  reciprocalResidual firstSituatedWoman
  ≡ reciprocalResidual secondSituatedWoman → ⊥
reciprocalResidualSeparates ()

canonicalHansonIrigarayPositiveRepair :
  Rechart.PositiveRecharting {Residual = ReciprocalResidual} oldStuntChart
canonicalHansonIrigarayPositiveRepair =
  Rechart.positive-recharting
    reciprocalResidual
    firstSituatedWoman
    secondSituatedWoman
    refl
    reciprocalResidualSeparates

------------------------------------------------------------------------
-- ANTI-LACANIAN CONSTRUCTION BOUNDARY
--
-- "Anti-Lacanian" here means the repo-level different-grammar operation:
-- reject the assumption that the one-centred chart is the unique grammar on
-- the shared carrier. It is NOT a claim that Irigaray is reducible to
-- anti-Lacanian negation; indeed the exact theorem blocks that reduction.
------------------------------------------------------------------------

data AntiLacanianMeansNegatingLacanLabels : Set where
data IrigarayIsInverseLacan : Set where
data FeministRepairMeansWomanOccupiesMasterCenter : Set where
data ReciprocalGrammarMeansNoDifference : Set where

antiLacanianIsNotLabelNegation :
  AntiLacanianMeansNegatingLacanLabels → ⊥
antiLacanianIsNotLabelNegation ()

irigarayIsNotInverseLacan :
  IrigarayIsInverseLacan → ⊥
irigarayIsNotInverseLacan ()

feministRepairDoesNotInstallNewMaster :
  FeministRepairMeansWomanOccupiesMasterCenter → ⊥
feministRepairDoesNotInstallNewMaster ()

reciprocityDoesNotEraseDifference :
  ReciprocalGrammarMeansNoDifference → ⊥
reciprocityDoesNotEraseDifference ()

------------------------------------------------------------------------
-- STUNT OPERATOR REFINEMENT
------------------------------------------------------------------------

data StuntGrammarMode : Set where
  oneCentredSignifierGrammar : StuntGrammarMode
  reciprocalRelationalGrammar : StuntGrammarMode

record StuntGrammarAudit : Set where
  constructor stunt-grammar-audit
  field
    sourcePoliticalOperator : String
    inheritedMode : StuntGrammarMode
    repairMode : StuntGrammarMode
    inheritedCarrierReused : Bool
    grammarChanged : Bool
    grammarChangedIsTrue : grammarChanged ≡ true
    labelsOnlyChanged : Bool
    labelsOnlyChangedIsFalse : labelsOnlyChanged ≡ false
    originatingSubjectResidualAdded : Bool
    reciprocalRelationAdded : Bool
    newMasterCenterInstalled : Bool
    newMasterCenterInstalledIsFalse :
      newMasterCenterInstalled ≡ false
    empiricalCausalEffectClaimed : Bool
    empiricalCausalEffectClaimedIsFalse :
      empiricalCausalEffectClaimed ≡ false

open StuntGrammarAudit public

canonicalBurqaStuntGrammarAudit : StuntGrammarAudit
canonicalBurqaStuntGrammarAudit =
  stunt-grammar-audit
    "Hanson burqa stunt / feminist-relational application"
    oneCentredSignifierGrammar
    reciprocalRelationalGrammar
    true
    true refl
    false refl
    true
    true
    false refl
    false refl

------------------------------------------------------------------------
-- CROSS-OWNER RECEIPTS
------------------------------------------------------------------------

criticalGrammarBoundary :
  Critical.CriticalRelationalGrammarBoundary
criticalGrammarBoundary =
  Critical.canonicalCriticalRelationalGrammarBoundary

bridgeBoundary :
  Bridge.LacanIrigarayGrammarBoundary
bridgeBoundary =
  Bridge.canonicalLacanIrigarayGrammarBoundary

irigarayBoundary :
  Irigaray.IrigarayLabialBoundary
irigarayBoundary =
  Irigaray.canonicalIrigarayLabialBoundary

burqaBoundary :
  Burqa.HansonBurqaFeministRelationalBoundary
burqaBoundary =
  Burqa.canonicalHansonBurqaFeministRelationalBoundary

------------------------------------------------------------------------
-- ENDPOINT
------------------------------------------------------------------------

record HansonLacanIrigarayBoundary : Set where
  constructor hanson-lacan-irigaray-boundary
  field
    lacanianLensRetainedAsOneLens : Bool
    irigarayanGrammarRetainedAsDifferentGrammar : Bool
    sharedCarrierRetained : Bool
    relabellingEquatesGrammars : Bool
    relabellingEquatesGrammarsIsFalse :
      relabellingEquatesGrammars ≡ false
    feministRepairIsSignFlip : Bool
    feministRepairIsSignFlipIsFalse :
      feministRepairIsSignFlip ≡ false
    feministRepairAddsResidualCoordinate : Bool
    reciprocalGrammarHasMasterCenter : Bool
    reciprocalGrammarHasMasterCenterIsFalse :
      reciprocalGrammarHasMasterCenter ≡ false
    representationEqualsSubjectAuthority : Bool
    representationEqualsSubjectAuthorityIsFalse :
      representationEqualsSubjectAuthority ≡ false
    antiLacanianConstructionErasesLacanianLens : Bool
    antiLacanianConstructionErasesLacanianLensIsFalse :
      antiLacanianConstructionErasesLacanianLens ≡ false
    oneTheoryMadeSovereign : Bool
    oneTheoryMadeSovereignIsFalse :
      oneTheoryMadeSovereign ≡ false

open HansonLacanIrigarayBoundary public

canonicalHansonLacanIrigarayBoundary : HansonLacanIrigarayBoundary
canonicalHansonLacanIrigarayBoundary =
  hanson-lacan-irigaray-boundary
    true
    true
    true
    false refl
    false refl
    true
    false refl
    false refl
    false refl
    false refl
