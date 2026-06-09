module DASHI.Physics.Closure.NSSprint153LocalizedVortexStretchingSourceReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSSprint151LocalizedEnstrophyIdentityReceipt as S151

------------------------------------------------------------------------
-- Sprint 153 localized vortex-stretching source receipt.
--
-- Anchor:
--
--   Sprint 151 localized-enstrophy receipt remains the controlling
--   scale-delta surface.  Its LocalizedEnstrophyIdentityAtScaleDelta gate
--   is still false/open.
--
-- Support:
--
--   Sprint 152 annular leakage domination is recorded here only as
--   support/conditional.  This receipt does not claim that domination as
--   an unconditional theorem, and it does not use it to promote the
--   annular row in Sprint 151.
--
-- Live target:
--
--   LocalizedVortexStretchingSourceBound is the Sprint 153 target.  The
--   checked content below records the dependency ledger and exact guards
--   that keep all promotion flags fail-closed.

sprint153LocalizedVortexStretchingLedgerClosed : Bool
sprint153LocalizedVortexStretchingLedgerClosed = true

sprint151LocalizedEnstrophyAnchored : Bool
sprint151LocalizedEnstrophyAnchored = true

sprint151LocalizedEnstrophyStillFalse : Bool
sprint151LocalizedEnstrophyStillFalse =
  S151.LocalizedEnstrophyIdentityAtScaleDelta

sprint151LocalizedEnstrophyStillOpen : Bool
sprint151LocalizedEnstrophyStillOpen =
  S151.LocalizedEnstrophyIdentityAtScaleDeltaOpen

sprint151VortexStretchingSourceTermStillOpen : Bool
sprint151VortexStretchingSourceTermStillOpen =
  S151.vortexStretchingSourceTermOpen

sprint151AnnularBoundaryTermStillOpen : Bool
sprint151AnnularBoundaryTermStillOpen =
  S151.annularBoundaryTermOpen

Sprint152AnnularLeakageDominationSupport : Bool
Sprint152AnnularLeakageDominationSupport = true

Sprint152AnnularLeakageDominationConditional : Bool
Sprint152AnnularLeakageDominationConditional = true

Sprint152AnnularLeakageDominationTheorem : Bool
Sprint152AnnularLeakageDominationTheorem = false

annularLeakageDominationMaySupportSourceLocalization : Bool
annularLeakageDominationMaySupportSourceLocalization = true

annularLeakageDominationPromotesAnnularBoundaryTerm : Bool
annularLeakageDominationPromotesAnnularBoundaryTerm = false

LocalizedVortexStretchingSourceBound : Bool
LocalizedVortexStretchingSourceBound = false

LocalizedVortexStretchingSourceBoundProved : Bool
LocalizedVortexStretchingSourceBoundProved = false

LocalizedVortexStretchingSourceBoundOpen : Bool
LocalizedVortexStretchingSourceBoundOpen = true

LocalizedVortexStretchingSourceBoundIsLiveTarget : Bool
LocalizedVortexStretchingSourceBoundIsLiveTarget = true

localizedVortexStretchingSourceBound : Bool
localizedVortexStretchingSourceBound = false

localizedVortexStretchingSourceBoundProved : Bool
localizedVortexStretchingSourceBoundProved = false

localizedVortexStretchingSourceBoundOpen : Bool
localizedVortexStretchingSourceBoundOpen = true

BiotSavartNonlocalClosureAtScaleDelta : Bool
BiotSavartNonlocalClosureAtScaleDelta = false

BiotSavartNonlocalClosureAtScaleDeltaProved : Bool
BiotSavartNonlocalClosureAtScaleDeltaProved = false

BiotSavartNonlocalClosureAtScaleDeltaOpen : Bool
BiotSavartNonlocalClosureAtScaleDeltaOpen = true

SimultaneousConstantsCompatibility : Bool
SimultaneousConstantsCompatibility = false

SimultaneousConstantsCompatibilityProved : Bool
SimultaneousConstantsCompatibilityProved = false

SimultaneousConstantsCompatibilityOpen : Bool
SimultaneousConstantsCompatibilityOpen = true

ModelValidityForWidthODE : Bool
ModelValidityForWidthODE = false

ModelValidityForWidthODEProved : Bool
ModelValidityForWidthODEProved = false

ModelValidityForWidthODEOpen : Bool
ModelValidityForWidthODEOpen = true

SymmetricHouLuoBKMFinite : Bool
SymmetricHouLuoBKMFinite = false

SymmetricHouLuoBKMFiniteProved : Bool
SymmetricHouLuoBKMFiniteProved = false

SymmetricHouLuoBKMFiniteOpen : Bool
SymmetricHouLuoBKMFiniteOpen = true

fullClayNSSolved : Bool
fullClayNSSolved = false

full_clay_ns_solved : Bool
full_clay_ns_solved = false

fullNavierStokesSolutionConstructed : Bool
fullNavierStokesSolutionConstructed = false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

sprint151AnchorKeepsLocalizedEnstrophyFalse :
  sprint151LocalizedEnstrophyStillFalse ≡ false
sprint151AnchorKeepsLocalizedEnstrophyFalse = refl

sprint151AnchorKeepsLocalizedEnstrophyOpen :
  sprint151LocalizedEnstrophyStillOpen ≡ true
sprint151AnchorKeepsLocalizedEnstrophyOpen = refl

sprint152AnnularLeakageRecordedConditional :
  Sprint152AnnularLeakageDominationConditional ≡ true
sprint152AnnularLeakageRecordedConditional = refl

sprint152AnnularLeakageNotClaimedAsTheorem :
  Sprint152AnnularLeakageDominationTheorem ≡ false
sprint152AnnularLeakageNotClaimedAsTheorem = refl

sprint153KeepsLocalizedVortexStretchingSourceBoundFalse :
  localizedVortexStretchingSourceBound ≡ false
sprint153KeepsLocalizedVortexStretchingSourceBoundFalse = refl

sprint153KeepsLocalizedVortexStretchingSourceBoundOpen :
  localizedVortexStretchingSourceBoundOpen ≡ true
sprint153KeepsLocalizedVortexStretchingSourceBoundOpen = refl

sprint153KeepsBiotSavartNonlocalClosureFalse :
  BiotSavartNonlocalClosureAtScaleDelta ≡ false
sprint153KeepsBiotSavartNonlocalClosureFalse = refl

sprint153KeepsSimultaneousConstantsCompatibilityFalse :
  SimultaneousConstantsCompatibility ≡ false
sprint153KeepsSimultaneousConstantsCompatibilityFalse = refl

sprint153KeepsModelValidityForWidthODEFalse :
  ModelValidityForWidthODE ≡ false
sprint153KeepsModelValidityForWidthODEFalse = refl

sprint153KeepsSymmetricHouLuoBKMFiniteFalse :
  SymmetricHouLuoBKMFinite ≡ false
sprint153KeepsSymmetricHouLuoBKMFiniteFalse = refl

sprint153KeepsFullClayNSSolvedFalse :
  fullClayNSSolved ≡ false
sprint153KeepsFullClayNSSolvedFalse = refl

sprint153KeepsClayPromotionFalse :
  clayNavierStokesPromoted ≡ false
sprint153KeepsClayPromotionFalse = refl

data Sprint153Support : Set where
  anchorSprint151LocalizedEnstrophyIdentityReceipt :
    Sprint153Support

  recordSprint151LocalizedEnstrophyStillFalseOpen :
    Sprint153Support

  recordSprint151VortexStretchingSourceTermStillOpen :
    Sprint153Support

  recordSprint152AnnularLeakageDominationSupportConditional :
    Sprint153Support

  recordSprint152AnnularLeakageDominationNotTheorem :
    Sprint153Support

  recordLocalizedVortexStretchingSourceBoundAsLiveTarget :
    Sprint153Support

  recordNoClayPromotionFromSourceTargetReceipt :
    Sprint153Support

canonicalSprint153Supports : List Sprint153Support
canonicalSprint153Supports =
  anchorSprint151LocalizedEnstrophyIdentityReceipt
  ∷ recordSprint151LocalizedEnstrophyStillFalseOpen
  ∷ recordSprint151VortexStretchingSourceTermStillOpen
  ∷ recordSprint152AnnularLeakageDominationSupportConditional
  ∷ recordSprint152AnnularLeakageDominationNotTheorem
  ∷ recordLocalizedVortexStretchingSourceBoundAsLiveTarget
  ∷ recordNoClayPromotionFromSourceTargetReceipt
  ∷ []

sprint153SupportCount : Nat
sprint153SupportCount = 7

data LocalizedVortexStretchingSourceObligation : Set where
  localVorticityAlignmentEstimate :
    LocalizedVortexStretchingSourceObligation

  cutoffWeightedStretchingIntegralEstimate :
    LocalizedVortexStretchingSourceObligation

  annularLeakageInsertionEstimate :
    LocalizedVortexStretchingSourceObligation

  axisBoundaryImageContributionEstimate :
    LocalizedVortexStretchingSourceObligation

  nonlocalBiotSavartTailEstimate :
    LocalizedVortexStretchingSourceObligation

  widthScaleDeltaNormalizationEstimate :
    LocalizedVortexStretchingSourceObligation

  simultaneousConstantsFitEstimate :
    LocalizedVortexStretchingSourceObligation

  sourceToLocalizedEnstrophyFeedthroughEstimate :
    LocalizedVortexStretchingSourceObligation

canonicalLocalizedVortexStretchingSourceObligations :
  List LocalizedVortexStretchingSourceObligation
canonicalLocalizedVortexStretchingSourceObligations =
  localVorticityAlignmentEstimate
  ∷ cutoffWeightedStretchingIntegralEstimate
  ∷ annularLeakageInsertionEstimate
  ∷ axisBoundaryImageContributionEstimate
  ∷ nonlocalBiotSavartTailEstimate
  ∷ widthScaleDeltaNormalizationEstimate
  ∷ simultaneousConstantsFitEstimate
  ∷ sourceToLocalizedEnstrophyFeedthroughEstimate
  ∷ []

localizedVortexStretchingSourceObligationCount : Nat
localizedVortexStretchingSourceObligationCount = 8

data Sprint153Obstruction : Set where
  localizedVortexStretchingSourceBoundNotProved :
    Sprint153Obstruction

  sprint152AnnularLeakageDominationOnlyConditional :
    Sprint153Obstruction

  biotSavartNonlocalClosureAtScaleDeltaNotProved :
    Sprint153Obstruction

  simultaneousConstantsCompatibilityNotProved :
    Sprint153Obstruction

  modelValidityForWidthODENotProved :
    Sprint153Obstruction

  localizedEnstrophyIdentityAtScaleDeltaStillFalse :
    Sprint153Obstruction

  symmetricHouLuoBKMFinitenessNotProved :
    Sprint153Obstruction

  fullClayNSNotSolved :
    Sprint153Obstruction

canonicalSprint153Obstructions : List Sprint153Obstruction
canonicalSprint153Obstructions =
  localizedVortexStretchingSourceBoundNotProved
  ∷ sprint152AnnularLeakageDominationOnlyConditional
  ∷ biotSavartNonlocalClosureAtScaleDeltaNotProved
  ∷ simultaneousConstantsCompatibilityNotProved
  ∷ modelValidityForWidthODENotProved
  ∷ localizedEnstrophyIdentityAtScaleDeltaStillFalse
  ∷ symmetricHouLuoBKMFinitenessNotProved
  ∷ fullClayNSNotSolved
  ∷ []

sprint153ObstructionCount : Nat
sprint153ObstructionCount = 8

data Sprint153FalsePromotionGuard : Set where
  keepLocalizedVortexStretchingSourceBoundFalseUntilSourceEstimate :
    Sprint153FalsePromotionGuard

  keepBiotSavartNonlocalClosureFalseUntilScaleDeltaTailEstimate :
    Sprint153FalsePromotionGuard

  keepSimultaneousConstantsCompatibilityFalseUntilJointConstantsFit :
    Sprint153FalsePromotionGuard

  keepModelValidityForWidthODEFalseUntilModelJustification :
    Sprint153FalsePromotionGuard

  keepSymmetricHouLuoBKMFiniteFalseUntilBKMIntegralBound :
    Sprint153FalsePromotionGuard

  keepFullClayNSSolvedFalseUntilAllNSGatesClose :
    Sprint153FalsePromotionGuard

  keepClayNavierStokesPromotedFalseUntilExternalPromotionBoundary :
    Sprint153FalsePromotionGuard

canonicalSprint153FalsePromotionGuards :
  List Sprint153FalsePromotionGuard
canonicalSprint153FalsePromotionGuards =
  keepLocalizedVortexStretchingSourceBoundFalseUntilSourceEstimate
  ∷ keepBiotSavartNonlocalClosureFalseUntilScaleDeltaTailEstimate
  ∷ keepSimultaneousConstantsCompatibilityFalseUntilJointConstantsFit
  ∷ keepModelValidityForWidthODEFalseUntilModelJustification
  ∷ keepSymmetricHouLuoBKMFiniteFalseUntilBKMIntegralBound
  ∷ keepFullClayNSSolvedFalseUntilAllNSGatesClose
  ∷ keepClayNavierStokesPromotedFalseUntilExternalPromotionBoundary
  ∷ []

sprint153FalsePromotionGuardCount : Nat
sprint153FalsePromotionGuardCount = 7

organizationString : String
organizationString =
  "O: Sprint153 is a checked localized vortex-stretching source receipt anchored to the Sprint151 localized-enstrophy identity receipt."

requirementString : String
requirementString =
  "R: The live target is LocalizedVortexStretchingSourceBound; Sprint152 annular leakage domination is only conditional support and cannot promote source, annular, nonlocal, constants, BKM, or Clay gates."

codeArtifactString : String
codeArtifactString =
  "C: The Agda artifact exports finite support, source-obligation, obstruction, false-promotion guard, ORCSLPGF, canonical surface, and theorem tuple packages with no stubs."

stateString : String
stateString =
  "S: localizedVortexStretchingSourceBound=false/open; BiotSavartNonlocalClosureAtScaleDelta=false/open; SimultaneousConstantsCompatibility=false/open; ModelValidityForWidthODE=false/open; SymmetricHouLuoBKMFinite=false/open; fullClayNSSolved=false; clayNavierStokesPromoted=false."

latticeString : String
latticeString =
  "L: Sprint152 conditional annular support sits below Sprint153 source localization; source localization and Biot-Savart closure sit below Sprint151 localized enstrophy; constants and width-model validity must close before BKM or Clay promotion."

proposalString : String
proposalString =
  "P: Prove the cutoff-weighted vortex-stretching source estimate with annular insertion, nonlocal tail control, width normalization, and simultaneous constants compatibility."

governanceString : String
governanceString =
  "G: Exact guard flags keep localizedVortexStretchingSourceBound, BiotSavartNonlocalClosureAtScaleDelta, SimultaneousConstantsCompatibility, ModelValidityForWidthODE, SymmetricHouLuoBKMFinite, fullClayNSSolved, and clayNavierStokesPromoted false."

gapString : String
gapString =
  "F: The missing proof is the non-circular localized source bound plus Biot-Savart tail and constants compatibility; Sprint152 annular leakage remains support/conditional only."

record Sprint153ORCSLPGF : Set where
  constructor sprint153ORCSLPGF
  field
    O : String
    OIsCanonical : O ≡ organizationString
    R : String
    RIsCanonical : R ≡ requirementString
    C : String
    CIsCanonical : C ≡ codeArtifactString
    S : String
    SIsCanonical : S ≡ stateString
    L : String
    LIsCanonical : L ≡ latticeString
    P : String
    PIsCanonical : P ≡ proposalString
    G : String
    GIsCanonical : G ≡ governanceString
    F : String
    FIsCanonical : F ≡ gapString

open Sprint153ORCSLPGF public

canonicalSprint153ORCSLPGF : Sprint153ORCSLPGF
canonicalSprint153ORCSLPGF =
  sprint153ORCSLPGF
    organizationString
    refl
    requirementString
    refl
    codeArtifactString
    refl
    stateString
    refl
    latticeString
    refl
    proposalString
    refl
    governanceString
    refl
    gapString
    refl

summaryString : String
summaryString =
  "Sprint153 anchors to Sprint151 localized enstrophy, records Sprint152 annular leakage domination as support/conditional only, declares LocalizedVortexStretchingSourceBound as the live target, and keeps localizedVortexStretchingSourceBound=false/open, BiotSavartNonlocalClosureAtScaleDelta=false/open, SimultaneousConstantsCompatibility=false/open, ModelValidityForWidthODE=false/open, SymmetricHouLuoBKMFinite=false/open, fullClayNSSolved=false, and clayNavierStokesPromoted=false."

record Sprint153LocalizedVortexStretchingSourceSurface : Set where
  constructor sprint153LocalizedVortexStretchingSourceSurface
  field
    gateName :
      String
    gateNameIsCanonical :
      gateName ≡ "LocalizedVortexStretchingSourceBound"
    anchorReceipt :
      S151.NSSprint151LocalizedEnstrophyIdentityReceipt
    anchorReceiptIsCanonical :
      anchorReceipt ≡ S151.canonicalNSSprint151LocalizedEnstrophyIdentityReceipt
    orcslpgf :
      Sprint153ORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalSprint153ORCSLPGF
    sprint151LocalizedEnstrophyFalseField :
      sprint151LocalizedEnstrophyStillFalse ≡ false
    sprint151LocalizedEnstrophyOpenField :
      sprint151LocalizedEnstrophyStillOpen ≡ true
    sprint152AnnularLeakageSupportField :
      Sprint152AnnularLeakageDominationSupport ≡ true
    sprint152AnnularLeakageConditionalField :
      Sprint152AnnularLeakageDominationConditional ≡ true
    sprint152AnnularLeakageTheoremFalseField :
      Sprint152AnnularLeakageDominationTheorem ≡ false
    localizedVortexStretchingSourceBoundFalseField :
      localizedVortexStretchingSourceBound ≡ false
    localizedVortexStretchingSourceBoundOpenField :
      localizedVortexStretchingSourceBoundOpen ≡ true
    localizedVortexStretchingSourceBoundLiveField :
      LocalizedVortexStretchingSourceBoundIsLiveTarget ≡ true
    biotSavartNonlocalClosureFalseField :
      BiotSavartNonlocalClosureAtScaleDelta ≡ false
    biotSavartNonlocalClosureOpenField :
      BiotSavartNonlocalClosureAtScaleDeltaOpen ≡ true
    simultaneousConstantsCompatibilityFalseField :
      SimultaneousConstantsCompatibility ≡ false
    simultaneousConstantsCompatibilityOpenField :
      SimultaneousConstantsCompatibilityOpen ≡ true
    modelValidityForWidthODEFalseField :
      ModelValidityForWidthODE ≡ false
    modelValidityForWidthODEOpenField :
      ModelValidityForWidthODEOpen ≡ true
    symmetricHouLuoBKMFiniteFalseField :
      SymmetricHouLuoBKMFinite ≡ false
    symmetricHouLuoBKMFiniteOpenField :
      SymmetricHouLuoBKMFiniteOpen ≡ true
    fullClayNSSolvedFalseField :
      fullClayNSSolved ≡ false
    clayPromotionFalseField :
      clayNavierStokesPromoted ≡ false

open Sprint153LocalizedVortexStretchingSourceSurface public

canonicalSprint153LocalizedVortexStretchingSourceSurface :
  Sprint153LocalizedVortexStretchingSourceSurface
canonicalSprint153LocalizedVortexStretchingSourceSurface =
  sprint153LocalizedVortexStretchingSourceSurface
    "LocalizedVortexStretchingSourceBound"
    refl
    S151.canonicalNSSprint151LocalizedEnstrophyIdentityReceipt
    refl
    canonicalSprint153ORCSLPGF
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

data Sprint153Promotion : Set where

sprint153PromotionImpossibleHere :
  Sprint153Promotion →
  ⊥
sprint153PromotionImpossibleHere ()

record NSSprint153LocalizedVortexStretchingSourceReceipt : Set where
  constructor nsSprint153LocalizedVortexStretchingSourceReceipt
  field
    surface :
      Sprint153LocalizedVortexStretchingSourceSurface
    surfaceIsCanonical :
      surface ≡ canonicalSprint153LocalizedVortexStretchingSourceSurface
    supports :
      List Sprint153Support
    supportsAreCanonical :
      supports ≡ canonicalSprint153Supports
    sourceObligations :
      List LocalizedVortexStretchingSourceObligation
    sourceObligationsAreCanonical :
      sourceObligations ≡ canonicalLocalizedVortexStretchingSourceObligations
    obstructions :
      List Sprint153Obstruction
    obstructionsAreCanonical :
      obstructions ≡ canonicalSprint153Obstructions
    falsePromotionGuards :
      List Sprint153FalsePromotionGuard
    falsePromotionGuardsAreCanonical :
      falsePromotionGuards ≡ canonicalSprint153FalsePromotionGuards
    summary :
      String
    summaryIsCanonical :
      summary ≡ summaryString

open NSSprint153LocalizedVortexStretchingSourceReceipt public

canonicalNSSprint153LocalizedVortexStretchingSourceReceipt :
  NSSprint153LocalizedVortexStretchingSourceReceipt
canonicalNSSprint153LocalizedVortexStretchingSourceReceipt =
  nsSprint153LocalizedVortexStretchingSourceReceipt
    canonicalSprint153LocalizedVortexStretchingSourceSurface
    refl
    canonicalSprint153Supports
    refl
    canonicalLocalizedVortexStretchingSourceObligations
    refl
    canonicalSprint153Obstructions
    refl
    canonicalSprint153FalsePromotionGuards
    refl
    summaryString
    refl

sprint153CountPackage :
  (sprint153SupportCount ≡ 7)
  × (localizedVortexStretchingSourceObligationCount ≡ 8)
  × (sprint153ObstructionCount ≡ 8)
  × (sprint153FalsePromotionGuardCount ≡ 7)
sprint153CountPackage =
  refl , refl , refl , refl

sprint153ExactGuardTuple :
  (localizedVortexStretchingSourceBound ≡ false)
  × (localizedVortexStretchingSourceBoundOpen ≡ true)
  × (BiotSavartNonlocalClosureAtScaleDelta ≡ false)
  × (BiotSavartNonlocalClosureAtScaleDeltaOpen ≡ true)
  × (SimultaneousConstantsCompatibility ≡ false)
  × (SimultaneousConstantsCompatibilityOpen ≡ true)
  × (ModelValidityForWidthODE ≡ false)
  × (ModelValidityForWidthODEOpen ≡ true)
  × (SymmetricHouLuoBKMFinite ≡ false)
  × (SymmetricHouLuoBKMFiniteOpen ≡ true)
  × (fullClayNSSolved ≡ false)
  × (full_clay_ns_solved ≡ false)
  × (fullNavierStokesSolutionConstructed ≡ false)
  × (clayNavierStokesPromoted ≡ false)
sprint153ExactGuardTuple =
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl

sprint153ConditionalSupportTuple :
  (sprint153LocalizedVortexStretchingLedgerClosed ≡ true)
  × (sprint151LocalizedEnstrophyAnchored ≡ true)
  × (sprint151LocalizedEnstrophyStillFalse ≡ false)
  × (sprint151LocalizedEnstrophyStillOpen ≡ true)
  × (sprint151VortexStretchingSourceTermStillOpen ≡ true)
  × (sprint151AnnularBoundaryTermStillOpen ≡ true)
  × (Sprint152AnnularLeakageDominationSupport ≡ true)
  × (Sprint152AnnularLeakageDominationConditional ≡ true)
  × (Sprint152AnnularLeakageDominationTheorem ≡ false)
  × (annularLeakageDominationMaySupportSourceLocalization ≡ true)
  × (annularLeakageDominationPromotesAnnularBoundaryTerm ≡ false)
  × (LocalizedVortexStretchingSourceBound ≡ false)
  × (LocalizedVortexStretchingSourceBoundOpen ≡ true)
  × (LocalizedVortexStretchingSourceBoundIsLiveTarget ≡ true)
sprint153ConditionalSupportTuple =
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl

sprint153ReceiptPackage :
  Sprint153LocalizedVortexStretchingSourceSurface
  × NSSprint153LocalizedVortexStretchingSourceReceipt
  × Sprint153ORCSLPGF
sprint153ReceiptPackage =
  canonicalSprint153LocalizedVortexStretchingSourceSurface ,
  canonicalNSSprint153LocalizedVortexStretchingSourceReceipt ,
  canonicalSprint153ORCSLPGF
