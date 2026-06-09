module DASHI.Promotion.ClayProofTranslationReducer where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Promotion.Gate3StandardModelClayEvidenceReducer as Reducer
import DASHI.Promotion.Gate3ClayObligations as Gate3Clay
import DASHI.Promotion.StandardModelTerminalObligations as SMT

------------------------------------------------------------------------
-- Clay proof/translation reducer.
--
-- This is a sharper non-promoting reducer over the Gate3/SM/NS/YM/terminal
-- surface.  It extracts the proof-translation rows that matter for Clay
-- submission readiness and computes the first blocker by strict priority:
-- proof obligations first, then authority obligations, then translation
-- obligations.  It intentionally does not promote any Clay, Standard Model,
-- terminal, or full-unification guard.

data TranslationTarget : Set where
  gate3ToContinuumOperatorTarget :
    TranslationTarget

  gate3MoscoRecoveryTarget :
    TranslationTarget

  gate3NoSpectralPollutionTarget :
    TranslationTarget

  gate3MassShellTarget :
    TranslationTarget

  navierStokesStandardPDETarget :
    TranslationTarget

  navierStokesPressureNonlinearPassageTarget :
    TranslationTarget

  navierStokesMaximumLocationMigrationLemmaTarget :
    TranslationTarget

  yangMillsWightmanOSSpectrumTarget :
    TranslationTarget

  yangMillsAllCompactSimpleGCoverageTarget :
    TranslationTarget

  standardModelKnownPhysicsTranslationTarget :
    TranslationTarget

  terminalClaimAuditTarget :
    TranslationTarget

data TranslationLane : Set where
  gate3ContinuumLane :
    TranslationLane

  navierStokesTranslationLane :
    TranslationLane

  yangMillsTranslationLane :
    TranslationLane

  standardModelPhysicsLane :
    TranslationLane

  terminalAuditLane :
    TranslationLane

data BlockerSource : Set where
  gate3ObligationSource :
    BlockerSource

  smTerminalObligationSource :
    BlockerSource

  evidenceReducerSource :
    BlockerSource

data Maybe (A : Set) : Set where
  nothing :
    Maybe A

  just :
    A →
    Maybe A

record TranslationBlockerRow : Set where
  field
    lane :
      TranslationLane

    target :
      TranslationTarget

    classification :
      Reducer.EvidenceClass

    source :
      BlockerSource

    upstreamRow :
      String

    requiredDischarge :
      String

    guardName :
      String

    claySubmissionRelevance :
      String

    promotesClaim :
      Bool

    promotesClaimIsFalse :
      promotesClaim ≡ false

open TranslationBlockerRow public

mkBlocker :
  TranslationLane →
  TranslationTarget →
  Reducer.EvidenceClass →
  BlockerSource →
  String →
  String →
  String →
  String →
  TranslationBlockerRow
mkBlocker lane target classification source upstreamRow requiredDischarge
  guardName relevance =
  record
    { lane = lane
    ; target = target
    ; classification = classification
    ; source = source
    ; upstreamRow = upstreamRow
    ; requiredDischarge = requiredDischarge
    ; guardName = guardName
    ; claySubmissionRelevance = relevance
    ; promotesClaim = false
    ; promotesClaimIsFalse = refl
    }

rowCount : List TranslationBlockerRow → Nat
rowCount [] =
  zero
rowCount (_ ∷ rows) =
  suc (rowCount rows)

classCount :
  Reducer.EvidenceClass →
  List TranslationBlockerRow →
  Nat
classCount wanted [] =
  zero
classCount Reducer.presentInternalCandidate (row ∷ rows)
  with classification row
... | Reducer.presentInternalCandidate =
  suc (classCount Reducer.presentInternalCandidate rows)
... | Reducer.proofMissing =
  classCount Reducer.presentInternalCandidate rows
... | Reducer.authorityMissing =
  classCount Reducer.presentInternalCandidate rows
... | Reducer.translationMissing =
  classCount Reducer.presentInternalCandidate rows
classCount Reducer.proofMissing (row ∷ rows)
  with classification row
... | Reducer.presentInternalCandidate =
  classCount Reducer.proofMissing rows
... | Reducer.proofMissing =
  suc (classCount Reducer.proofMissing rows)
... | Reducer.authorityMissing =
  classCount Reducer.proofMissing rows
... | Reducer.translationMissing =
  classCount Reducer.proofMissing rows
classCount Reducer.authorityMissing (row ∷ rows)
  with classification row
... | Reducer.presentInternalCandidate =
  classCount Reducer.authorityMissing rows
... | Reducer.proofMissing =
  classCount Reducer.authorityMissing rows
... | Reducer.authorityMissing =
  suc (classCount Reducer.authorityMissing rows)
... | Reducer.translationMissing =
  classCount Reducer.authorityMissing rows
classCount Reducer.translationMissing (row ∷ rows)
  with classification row
... | Reducer.presentInternalCandidate =
  classCount Reducer.translationMissing rows
... | Reducer.proofMissing =
  classCount Reducer.translationMissing rows
... | Reducer.authorityMissing =
  classCount Reducer.translationMissing rows
... | Reducer.translationMissing =
  suc (classCount Reducer.translationMissing rows)

firstWithClass :
  Reducer.EvidenceClass →
  List TranslationBlockerRow →
  Maybe TranslationBlockerRow
firstWithClass wanted [] =
  nothing
firstWithClass Reducer.presentInternalCandidate (row ∷ rows)
  with classification row
... | Reducer.presentInternalCandidate =
  just row
... | Reducer.proofMissing =
  firstWithClass Reducer.presentInternalCandidate rows
... | Reducer.authorityMissing =
  firstWithClass Reducer.presentInternalCandidate rows
... | Reducer.translationMissing =
  firstWithClass Reducer.presentInternalCandidate rows
firstWithClass Reducer.proofMissing (row ∷ rows)
  with classification row
... | Reducer.presentInternalCandidate =
  firstWithClass Reducer.proofMissing rows
... | Reducer.proofMissing =
  just row
... | Reducer.authorityMissing =
  firstWithClass Reducer.proofMissing rows
... | Reducer.translationMissing =
  firstWithClass Reducer.proofMissing rows
firstWithClass Reducer.authorityMissing (row ∷ rows)
  with classification row
... | Reducer.presentInternalCandidate =
  firstWithClass Reducer.authorityMissing rows
... | Reducer.proofMissing =
  firstWithClass Reducer.authorityMissing rows
... | Reducer.authorityMissing =
  just row
... | Reducer.translationMissing =
  firstWithClass Reducer.authorityMissing rows
firstWithClass Reducer.translationMissing (row ∷ rows)
  with classification row
... | Reducer.presentInternalCandidate =
  firstWithClass Reducer.translationMissing rows
... | Reducer.proofMissing =
  firstWithClass Reducer.translationMissing rows
... | Reducer.authorityMissing =
  firstWithClass Reducer.translationMissing rows
... | Reducer.translationMissing =
  just row

firstCriticalBlocker :
  List TranslationBlockerRow →
  Maybe TranslationBlockerRow
firstCriticalBlocker rows
  with firstWithClass Reducer.proofMissing rows
... | just row =
  just row
... | nothing
  with firstWithClass Reducer.authorityMissing rows
... | just row =
  just row
... | nothing
  with firstWithClass Reducer.translationMissing rows
... | just row =
  just row
... | nothing =
  nothing

canonicalGate3TranslationRows : List TranslationBlockerRow
canonicalGate3TranslationRows =
  mkBlocker
    gate3ContinuumLane
    gate3ToContinuumOperatorTarget
    Reducer.proofMissing
    gate3ObligationSource
    "Gate3Clay.continuumTransferPromotedGuard"
    "spectral transfer proof from finite/pruned route to the continuum operator"
    "continuumTransferPromoted"
    "needed before finite Gate 3 evidence can be submitted as a continuum operator result"
  ∷ mkBlocker
    gate3ContinuumLane
    gate3MoscoRecoveryTarget
    Reducer.proofMissing
    gate3ObligationSource
    "Gate3Clay.moscoRecoveryPromotedGuard"
    "constructive Mosco recovery sequence in the common ambient space"
    "moscoRecoveryPromoted"
    "needed to complete the limsup side of the Gate 3 variational limit"
  ∷ mkBlocker
    gate3ContinuumLane
    gate3NoSpectralPollutionTarget
    Reducer.proofMissing
    gate3ObligationSource
    "Gate3Clay.noSpectralPollutionPromotedGuard"
    "no-spectral-pollution theorem for the continuum transfer"
    "noSpectralPollutionPromoted"
    "needed to prevent finite spectra from being over-read as continuum spectrum"
  ∷ mkBlocker
    gate3ContinuumLane
    gate3MassShellTarget
    Reducer.translationMissing
    gate3ObligationSource
    "Gate3Clay.massShellBridgePromotedGuard"
    "translation from carrier energy spectrum to standard mass-shell language"
    "massShellBridgePromoted"
    "needed before the bridge can be compared to known relativistic physics"
  ∷ []

canonicalNavierStokesTranslationRows : List TranslationBlockerRow
canonicalNavierStokesTranslationRows =
  mkBlocker
    navierStokesTranslationLane
    navierStokesMaximumLocationMigrationLemmaTarget
    Reducer.proofMissing
    evidenceReducerSource
    "Reducer.nsMaximumLocationMigrationLemmaToken"
    "MaximumLocationMigrationLemma for the Hou-Luo axisymmetric maximum-location route"
    "navierStokesClayPromoted"
    "next active Hou-Luo gate after the Sprint145 comparison-envelope route failed closed"
  ∷ mkBlocker
    navierStokesTranslationLane
    navierStokesStandardPDETarget
    Reducer.translationMissing
    gate3ObligationSource
    "Gate3Clay.navierStokesWeakSolutionClass"
    "standard incompressible 3D Navier-Stokes PDE statement with solution class and boundary regime"
    "navierStokesClayPromoted"
    "needed before any internal route can be judged against the Clay statement"
  ∷ mkBlocker
    navierStokesTranslationLane
    navierStokesPressureNonlinearPassageTarget
    Reducer.proofMissing
    gate3ObligationSource
    "Gate3Clay.navierStokesPressureReconstruction/nonlinearTermPassage"
    "pressure reconstruction plus nonlinear term passage in the target weak/strong topology"
    "navierStokesClayPromoted"
    "needed before compactness evidence can support regularity or global smoothness"
  ∷ []

canonicalYangMillsTranslationRows : List TranslationBlockerRow
canonicalYangMillsTranslationRows =
  mkBlocker
    yangMillsTranslationLane
    yangMillsWightmanOSSpectrumTarget
    Reducer.proofMissing
    gate3ObligationSource
    "Gate3Clay.yangMillsOSPositivity/WightmanReconstruction/PositiveMassGap"
    "OS positivity, Wightman reconstruction, covariance, locality, spectrum condition, and positive gap"
    "yangMillsClayPromoted"
    "needed for the Clay Yang-Mills existence and mass-gap formulation"
  ∷ mkBlocker
    yangMillsTranslationLane
    yangMillsAllCompactSimpleGCoverageTarget
    Reducer.translationMissing
    gate3ObligationSource
    "Gate3Clay.yangMillsGaugeIdentification"
    "coverage map from current carrier evidence to every compact simple gauge group G"
    "yangMillsClayPromoted"
    "needed because the Clay problem quantifies over any compact simple gauge group"
  ∷ []

canonicalStandardModelTranslationRows : List TranslationBlockerRow
canonicalStandardModelTranslationRows =
  mkBlocker
    standardModelPhysicsLane
    standardModelKnownPhysicsTranslationTarget
    Reducer.authorityMissing
    smTerminalObligationSource
    "SMT.continuousGaugeBridgeTarget/physicalSectorMapTarget"
    "accepted known-physics translation tying SM representation, gauge normalization, sector map, and empirical authority"
    "standardModelPromoted"
    "needed before SM-facing evidence can be advertised as physical Standard Model recovery"
  ∷ []

canonicalTerminalTranslationRows : List TranslationBlockerRow
canonicalTerminalTranslationRows =
  mkBlocker
    terminalAuditLane
    terminalClaimAuditTarget
    Reducer.proofMissing
    smTerminalObligationSource
    "SMT.claimSurfaceAuditTarget"
    "claim audit proving no terminal/full-unification statement outruns source lane guards"
    "terminalPromotion"
    "needed before any terminal/full-unification submission surface can be accepted"
  ∷ []

infixr 5 _++_

_++_ :
  List TranslationBlockerRow →
  List TranslationBlockerRow →
  List TranslationBlockerRow
[] ++ ys =
  ys
(x ∷ xs) ++ ys =
  x ∷ (xs ++ ys)

canonicalClayProofTranslationRows : List TranslationBlockerRow
canonicalClayProofTranslationRows =
  canonicalNavierStokesTranslationRows
  ++ canonicalGate3TranslationRows
  ++ canonicalYangMillsTranslationRows
  ++ canonicalStandardModelTranslationRows
  ++ canonicalTerminalTranslationRows

record ClayProofTranslationReducer : Setω where
  field
    sourceEvidenceReducer :
      Reducer.Gate3StandardModelClayEvidenceReducer

    gate3ObligationReceipt :
      Gate3Clay.Gate3ClayPromotionObligationReceipt

    standardModelTerminalReceipt :
      SMT.StandardModelTerminalPromotionObligationReceipt

    translationRows :
      List TranslationBlockerRow

    translationRowCount :
      Nat

    translationRowCountIs10 :
      translationRowCount ≡ 11

    consumedReducerAllRowCount :
      Nat

    consumedReducerAllRowCountIs32 :
      consumedReducerAllRowCount ≡ 35

    consumedReducerProofMissingCount :
      Nat

    consumedReducerProofMissingCountIs16 :
      consumedReducerProofMissingCount ≡ 18

    consumedReducerAuthorityMissingCount :
      Nat

    consumedReducerAuthorityMissingCountIs4 :
      consumedReducerAuthorityMissingCount ≡ 4

    consumedReducerTranslationMissingCount :
      Nat

    consumedReducerTranslationMissingCountIs4 :
      consumedReducerTranslationMissingCount ≡ 4

    localInternalCandidateCount :
      Nat

    localInternalCandidateCountIs0 :
      localInternalCandidateCount ≡ 0

    localProofMissingCount :
      Nat

    localProofMissingCountIs6 :
      localProofMissingCount ≡ 7

    localAuthorityMissingCount :
      Nat

    localAuthorityMissingCountIs1 :
      localAuthorityMissingCount ≡ 1

    localTranslationMissingCount :
      Nat

    localTranslationMissingCountIs3 :
      localTranslationMissingCount ≡ 3

    firstBlocker :
      Maybe TranslationBlockerRow

    firstBlockerIsProofMissing :
      firstBlocker
      ≡
      just
        (mkBlocker
          navierStokesTranslationLane
          navierStokesMaximumLocationMigrationLemmaTarget
          Reducer.proofMissing
          evidenceReducerSource
          "Reducer.nsMaximumLocationMigrationLemmaToken"
          "MaximumLocationMigrationLemma for the Hou-Luo axisymmetric maximum-location route"
          "navierStokesClayPromoted"
          "next active Hou-Luo gate after the Sprint145 comparison-envelope route failed closed")

    gate3Closed :
      Bool

    gate3ClosedIsFalse :
      gate3Closed ≡ false

    standardModelPromoted :
      Bool

    standardModelPromotedIsFalse :
      standardModelPromoted ≡ false

    navierStokesClayPromoted :
      Bool

    navierStokesClayPromotedIsFalse :
      navierStokesClayPromoted ≡ false

    yangMillsClayPromoted :
      Bool

    yangMillsClayPromotedIsFalse :
      yangMillsClayPromoted ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    fullUnificationPromoted :
      Bool

    fullUnificationPromotedIsFalse :
      fullUnificationPromoted ≡ false

    reducerPromotesAnyClaim :
      Bool

    reducerPromotesAnyClaimIsFalse :
      reducerPromotesAnyClaim ≡ false

    validationCommand :
      String

open ClayProofTranslationReducer public

canonicalClayProofTranslationReducer :
  ClayProofTranslationReducer
canonicalClayProofTranslationReducer =
  record
    { sourceEvidenceReducer =
        Reducer.canonicalGate3StandardModelClayEvidenceReducer
    ; gate3ObligationReceipt =
        Gate3Clay.canonicalGate3ClayPromotionObligationReceipt
    ; standardModelTerminalReceipt =
        SMT.canonicalStandardModelTerminalPromotionObligationReceipt
    ; translationRows =
        canonicalClayProofTranslationRows
    ; translationRowCount =
        rowCount canonicalClayProofTranslationRows
    ; translationRowCountIs10 =
        refl
    ; consumedReducerAllRowCount =
        Reducer.allRowCount Reducer.canonicalGate3StandardModelClayEvidenceReducer
    ; consumedReducerAllRowCountIs32 =
        Reducer.canonicalReducerRowCountIs32
    ; consumedReducerProofMissingCount =
        Reducer.proofMissingCount
          Reducer.canonicalGate3StandardModelClayEvidenceReducer
    ; consumedReducerProofMissingCountIs16 =
        Reducer.canonicalReducerProofMissingCountIs16
    ; consumedReducerAuthorityMissingCount =
        Reducer.authorityMissingCount
          Reducer.canonicalGate3StandardModelClayEvidenceReducer
    ; consumedReducerAuthorityMissingCountIs4 =
        Reducer.canonicalReducerAuthorityMissingCountIs4
    ; consumedReducerTranslationMissingCount =
        Reducer.translationMissingCount
          Reducer.canonicalGate3StandardModelClayEvidenceReducer
    ; consumedReducerTranslationMissingCountIs4 =
        Reducer.canonicalReducerTranslationMissingCountIs4
    ; localInternalCandidateCount =
        classCount Reducer.presentInternalCandidate canonicalClayProofTranslationRows
    ; localInternalCandidateCountIs0 =
        refl
    ; localProofMissingCount =
        classCount Reducer.proofMissing canonicalClayProofTranslationRows
    ; localProofMissingCountIs6 =
        refl
    ; localAuthorityMissingCount =
        classCount Reducer.authorityMissing canonicalClayProofTranslationRows
    ; localAuthorityMissingCountIs1 =
        refl
    ; localTranslationMissingCount =
        classCount Reducer.translationMissing canonicalClayProofTranslationRows
    ; localTranslationMissingCountIs3 =
        refl
    ; firstBlocker =
        firstCriticalBlocker canonicalClayProofTranslationRows
    ; firstBlockerIsProofMissing =
        refl
    ; gate3Closed =
        Gate3Clay.gate3Closed
          Gate3Clay.canonicalGate3ClayPromotionObligationReceipt
    ; gate3ClosedIsFalse =
        Gate3Clay.gate3ClosedIsFalse
          Gate3Clay.canonicalGate3ClayPromotionObligationReceipt
    ; standardModelPromoted =
        SMT.standardModelPromoted
          SMT.canonicalStandardModelTerminalPromotionObligationReceipt
    ; standardModelPromotedIsFalse =
        SMT.standardModelPromotedIsFalse
          SMT.canonicalStandardModelTerminalPromotionObligationReceipt
    ; navierStokesClayPromoted =
        Gate3Clay.navierStokesClayPromoted
          Gate3Clay.canonicalGate3ClayPromotionObligationReceipt
    ; navierStokesClayPromotedIsFalse =
        Gate3Clay.navierStokesClayPromotedIsFalse
          Gate3Clay.canonicalGate3ClayPromotionObligationReceipt
    ; yangMillsClayPromoted =
        Gate3Clay.yangMillsClayPromoted
          Gate3Clay.canonicalGate3ClayPromotionObligationReceipt
    ; yangMillsClayPromotedIsFalse =
        Gate3Clay.yangMillsClayPromotedIsFalse
          Gate3Clay.canonicalGate3ClayPromotionObligationReceipt
    ; terminalPromotion =
        SMT.terminalPromotion
          SMT.canonicalStandardModelTerminalPromotionObligationReceipt
    ; terminalPromotionIsFalse =
        SMT.terminalPromotionIsFalse
          SMT.canonicalStandardModelTerminalPromotionObligationReceipt
    ; fullUnificationPromoted =
        SMT.fullUnificationPromoted
          SMT.canonicalStandardModelTerminalPromotionObligationReceipt
    ; fullUnificationPromotedIsFalse =
        SMT.fullUnificationPromotedIsFalse
          SMT.canonicalStandardModelTerminalPromotionObligationReceipt
    ; reducerPromotesAnyClaim =
        false
    ; reducerPromotesAnyClaimIsFalse =
        refl
    ; validationCommand =
        "agda -i . DASHI/Promotion/ClayProofTranslationReducer.agda"
    }

canonicalClayProofTranslationRowCountIs10 :
  translationRowCount canonicalClayProofTranslationReducer ≡ 11
canonicalClayProofTranslationRowCountIs10 =
  translationRowCountIs10 canonicalClayProofTranslationReducer

canonicalClayProofTranslationProofMissingCountIs6 :
  localProofMissingCount canonicalClayProofTranslationReducer ≡ 7
canonicalClayProofTranslationProofMissingCountIs6 =
  localProofMissingCountIs6 canonicalClayProofTranslationReducer

canonicalClayProofTranslationAuthorityMissingCountIs1 :
  localAuthorityMissingCount canonicalClayProofTranslationReducer ≡ 1
canonicalClayProofTranslationAuthorityMissingCountIs1 =
  localAuthorityMissingCountIs1 canonicalClayProofTranslationReducer

canonicalClayProofTranslationTranslationMissingCountIs3 :
  localTranslationMissingCount canonicalClayProofTranslationReducer ≡ 3
canonicalClayProofTranslationTranslationMissingCountIs3 =
  localTranslationMissingCountIs3 canonicalClayProofTranslationReducer

canonicalClayProofTranslationConsumesReducerRows32 :
  consumedReducerAllRowCount canonicalClayProofTranslationReducer ≡ 35
canonicalClayProofTranslationConsumesReducerRows32 =
  consumedReducerAllRowCountIs32 canonicalClayProofTranslationReducer

canonicalClayProofTranslationFirstBlocker :
  firstBlocker canonicalClayProofTranslationReducer
  ≡
  just
    (mkBlocker
      navierStokesTranslationLane
      navierStokesMaximumLocationMigrationLemmaTarget
      Reducer.proofMissing
      evidenceReducerSource
      "Reducer.nsMaximumLocationMigrationLemmaToken"
      "MaximumLocationMigrationLemma for the Hou-Luo axisymmetric maximum-location route"
      "navierStokesClayPromoted"
      "next active Hou-Luo gate after the Sprint145 comparison-envelope route failed closed")
canonicalClayProofTranslationFirstBlocker =
  firstBlockerIsProofMissing canonicalClayProofTranslationReducer

clayProofTranslationReducerKeepsGate3False :
  gate3Closed canonicalClayProofTranslationReducer ≡ false
clayProofTranslationReducerKeepsGate3False =
  gate3ClosedIsFalse canonicalClayProofTranslationReducer

clayProofTranslationReducerKeepsStandardModelFalse :
  standardModelPromoted canonicalClayProofTranslationReducer ≡ false
clayProofTranslationReducerKeepsStandardModelFalse =
  standardModelPromotedIsFalse canonicalClayProofTranslationReducer

clayProofTranslationReducerKeepsNavierStokesFalse :
  navierStokesClayPromoted canonicalClayProofTranslationReducer ≡ false
clayProofTranslationReducerKeepsNavierStokesFalse =
  navierStokesClayPromotedIsFalse canonicalClayProofTranslationReducer

clayProofTranslationReducerKeepsYangMillsFalse :
  yangMillsClayPromoted canonicalClayProofTranslationReducer ≡ false
clayProofTranslationReducerKeepsYangMillsFalse =
  yangMillsClayPromotedIsFalse canonicalClayProofTranslationReducer

clayProofTranslationReducerKeepsTerminalFalse :
  terminalPromotion canonicalClayProofTranslationReducer ≡ false
clayProofTranslationReducerKeepsTerminalFalse =
  terminalPromotionIsFalse canonicalClayProofTranslationReducer

clayProofTranslationReducerKeepsFullUnificationFalse :
  fullUnificationPromoted canonicalClayProofTranslationReducer ≡ false
clayProofTranslationReducerKeepsFullUnificationFalse =
  fullUnificationPromotedIsFalse canonicalClayProofTranslationReducer

clayProofTranslationReducerPromotesNoClaim :
  reducerPromotesAnyClaim canonicalClayProofTranslationReducer ≡ false
clayProofTranslationReducerPromotesNoClaim =
  reducerPromotesAnyClaimIsFalse canonicalClayProofTranslationReducer
