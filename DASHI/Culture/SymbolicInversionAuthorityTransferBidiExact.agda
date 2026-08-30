module DASHI.Culture.SymbolicInversionAuthorityTransferBidiExact where

------------------------------------------------------------------------
-- SYMBOLIC INVERSION / AUTHORITY TRANSFER / RECLAMATION, BIDI
--
-- A historically imposed category can later be reused, reclaimed, inverted,
-- or reconstituted without rewriting the earlier event, speaker, target, or
-- historical self-identification.  Meaning/use, authority and provenance are
-- therefore independent coordinates.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.ContextualDialecticRoleExact as Dialectic
import DASHI.Core.FeministRechartingSourceBridgeExact as Feminist
import DASHI.Culture.ReligiousSanctionFeministWiccaCrossPollinationExact as Cross

------------------------------------------------------------------------
-- 1. Keep symbol, use, valence, authority and provenance distinct.
------------------------------------------------------------------------

data SymbolToken : Set where
  witchToken hereticToken sinfulWomanToken deviantToken : SymbolToken

data SymbolicUse : Set where
  imposedCondemnation
  externallyRecordedAccusation
  defensiveRefusal
  oppositionalReclamation
  affirmativeSelfIdentification
  artisticPoliticalUse
  : SymbolicUse

data SymbolicValence : Set where
  negativeValence contestedValence positiveValence mixedValence : SymbolicValence

data AuthorityLocation : Set where
  familyAuthority
  clericalAuthority
  institutionalAuthority
  juridicalAuthority
  communityAuthority
  selfAuthority
  collectiveCounterAuthority
  unresolvedAuthority
  : AuthorityLocation

record SymbolicEpisode : Set where
  constructor symbolic-episode
  field
    token : SymbolToken
    use : SymbolicUse
    valence : SymbolicValence
    authority : AuthorityLocation
    speaker : String
    target : String
    historicalContext : String
    provenance : String

open SymbolicEpisode public

imposedWitchEpisode : SymbolicEpisode
imposedWitchEpisode = symbolic-episode
  witchToken imposedCondemnation negativeValence institutionalAuthority
  "historical accusing authority unresolved in generic specimen"
  "historical target unresolved in generic specimen"
  "historical accusation/persecution frame"
  "finite DASHI comparison specimen; not a claim that an accused person self-identified as Wiccan or witch"

reclaimedWitchEpisode : SymbolicEpisode
reclaimedWitchEpisode = symbolic-episode
  witchToken oppositionalReclamation positiveValence collectiveCounterAuthority
  "later claimant/community"
  "self/community"
  "later feminist/pagan/reclamation frame"
  "finite DASHI comparison specimen; later use does not overwrite earlier provenance"

sameTokenAcrossEpisodes : token imposedWitchEpisode ≡ token reclaimedWitchEpisode
sameTokenAcrossEpisodes = refl

------------------------------------------------------------------------
-- 2. Same lexical token cannot recover historical use or authority.
------------------------------------------------------------------------

data WitchUseState : Set where imposedWitchUse reclaimedWitchUse : WitchUseState

data SameWitchSurface : Set where witchSurface : SameWitchSurface

data UseCode : Set where imposedUseCode reclaimedUseCode : UseCode

witchSurfaceOf : WitchUseState → SameWitchSurface
witchSurfaceOf imposedWitchUse = witchSurface
witchSurfaceOf reclaimedWitchUse = witchSurface

witchUseCode : WitchUseState → UseCode
witchUseCode imposedWitchUse = imposedUseCode
witchUseCode reclaimedWitchUse = reclaimedUseCode

useCodesDiffer : witchUseCode imposedWitchUse ≡ witchUseCode reclaimedWitchUse → ⊥
useCodesDiffer ()

sameTokenCannotRecoverUse : INF.FactorsThrough witchSurfaceOf witchUseCode → ⊥
sameTokenCannotRecoverUse =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness imposedWitchUse reclaimedWitchUse refl useCodesDiffer)

------------------------------------------------------------------------
-- 3. Authority transfer is not truth transfer or historical rewriting.
------------------------------------------------------------------------

data ImposedAuthorityTransfersTruth : Set where
data ReclaimedAuthorityTransfersHistoricalIdentity : Set where
data ReclamationErasesOriginalProvenance : Set where
data PositiveValenceProvesHistoricalInjustice : Set where
data HistoricalCondemnationProvesCurrentReclamation : Set where
data SharedTokenPromotesSharedDoctrine : Set where
data SharedTokenPromotesSharedPolitics : Set where
data SharedTokenPromotesSharedFormationHistory : Set where

imposedAuthorityDoesNotTransferTruth : ImposedAuthorityTransfersTruth → ⊥
imposedAuthorityDoesNotTransferTruth ()

reclaimedAuthorityDoesNotTransferHistoricalIdentity :
  ReclaimedAuthorityTransfersHistoricalIdentity → ⊥
reclaimedAuthorityDoesNotTransferHistoricalIdentity ()

reclamationDoesNotEraseOriginalProvenance : ReclamationErasesOriginalProvenance → ⊥
reclamationDoesNotEraseOriginalProvenance ()

positiveValenceDoesNotProveHistoricalInjustice : PositiveValenceProvesHistoricalInjustice → ⊥
positiveValenceDoesNotProveHistoricalInjustice ()

historicalCondemnationDoesNotProveCurrentReclamation :
  HistoricalCondemnationProvesCurrentReclamation → ⊥
historicalCondemnationDoesNotProveCurrentReclamation ()

sharedTokenDoesNotPromoteSharedDoctrine : SharedTokenPromotesSharedDoctrine → ⊥
sharedTokenDoesNotPromoteSharedDoctrine ()

sharedTokenDoesNotPromoteSharedPolitics : SharedTokenPromotesSharedPolitics → ⊥
sharedTokenDoesNotPromoteSharedPolitics ()

sharedTokenDoesNotPromoteSharedFormationHistory :
  SharedTokenPromotesSharedFormationHistory → ⊥
sharedTokenDoesNotPromoteSharedFormationHistory ()

------------------------------------------------------------------------
-- 4. Reclamation is a positive rechart, not lexical sign-flipping alone.
------------------------------------------------------------------------

data SymbolFormation : Set where
  imposedSymbolPosition reclaimedSymbolPosition reconstitutedSymbolPosition : SymbolFormation

data CoarseSymbolChart : Set where sameWitchLabel : CoarseSymbolChart

data SymbolResidual : Set where imposedResidual reclaimedResidual reconstitutedResidual : SymbolResidual

coarseSymbolChart : SymbolFormation → CoarseSymbolChart
coarseSymbolChart imposedSymbolPosition = sameWitchLabel
coarseSymbolChart reclaimedSymbolPosition = sameWitchLabel
coarseSymbolChart reconstitutedSymbolPosition = sameWitchLabel

symbolResidual : SymbolFormation → SymbolResidual
symbolResidual imposedSymbolPosition = imposedResidual
symbolResidual reclaimedSymbolPosition = reclaimedResidual
symbolResidual reconstitutedSymbolPosition = reconstitutedResidual

imposedAndReconstitutedResidualsDiffer :
  symbolResidual imposedSymbolPosition ≡ symbolResidual reconstitutedSymbolPosition → ⊥
imposedAndReconstitutedResidualsDiffer ()

symbolicPositiveRecharting : Feminist.PositiveRecharting coarseSymbolChart
symbolicPositiveRecharting =
  Feminist.positive-recharting
    symbolResidual
    imposedSymbolPosition
    reconstitutedSymbolPosition
    refl
    imposedAndReconstitutedResidualsDiffer

------------------------------------------------------------------------
-- 5. Dialectical role follows the comparison frame.
------------------------------------------------------------------------

data SymbolicFrame : Set where
  condemnationFrame reclamationFrame genealogyFrame contemporaryUseFrame : SymbolicFrame

data SymbolicPosition : Set where
  condemningAuthority reclaimedSymbol historicalTarget contemporaryUser : SymbolicPosition

symbolicRoleSystem : Dialectic.ContextualRoleSystem SymbolicFrame SymbolicPosition
symbolicRoleSystem = record { roleIn = role }
  where
    role : SymbolicFrame → SymbolicPosition → Dialectic.DialecticRole
    role condemnationFrame condemningAuthority = Dialectic.initialRole
    role condemnationFrame reclaimedSymbol = Dialectic.counterRole
    role condemnationFrame historicalTarget = Dialectic.counterRole
    role condemnationFrame contemporaryUser = Dialectic.mediatingRole
    role reclamationFrame condemningAuthority = Dialectic.counterRole
    role reclamationFrame reclaimedSymbol = Dialectic.initialRole
    role reclamationFrame historicalTarget = Dialectic.mediatingRole
    role reclamationFrame contemporaryUser = Dialectic.mediatingRole
    role genealogyFrame condemningAuthority = Dialectic.mediatingRole
    role genealogyFrame reclaimedSymbol = Dialectic.mediatingRole
    role genealogyFrame historicalTarget = Dialectic.initialRole
    role genealogyFrame contemporaryUser = Dialectic.counterRole
    role contemporaryUseFrame condemningAuthority = Dialectic.mediatingRole
    role contemporaryUseFrame reclaimedSymbol = Dialectic.mediatingRole
    role contemporaryUseFrame historicalTarget = Dialectic.counterRole
    role contemporaryUseFrame contemporaryUser = Dialectic.initialRole

reclaimedSymbolRoleChanges : Dialectic.RoleChangeWitness symbolicRoleSystem
reclaimedSymbolRoleChanges =
  Dialectic.role-change-witness reclaimedSymbol condemnationFrame reclamationFrame (λ ())

------------------------------------------------------------------------
-- 6. Cross-pollination weld and final boundary.
------------------------------------------------------------------------

record SymbolicInversionAuthorityTransferWeld : Set where
  constructor symbolic-inversion-authority-transfer-weld
  field
    sanctionFeministWiccaBoundary : Cross.ReligiousSanctionFeministWiccaBoundary
    positiveRechart : Feminist.PositiveRecharting coarseSymbolChart
    tokenDoesNotRecoverUse : INF.FactorsThrough witchSurfaceOf witchUseCode → ⊥

canonicalSymbolicInversionAuthorityTransferWeld : SymbolicInversionAuthorityTransferWeld
canonicalSymbolicInversionAuthorityTransferWeld =
  symbolic-inversion-authority-transfer-weld
    Cross.canonicalReligiousSanctionFeministWiccaBoundary
    symbolicPositiveRecharting
    sameTokenCannotRecoverUse

record SymbolicInversionAuthorityTransferBoundary : Set where
  constructor symbolic-inversion-authority-transfer-boundary
  field
    sameWordMeansSameHistoricalUse : Bool
    imposedLabelEqualsSelfIdentification : Bool
    reclamationRewritesOriginalEvent : Bool
    reclamationErasesOriginalProvenance : Bool
    reclaimedAuthorityEstablishesHistoricalIdentity : Bool
    institutionalAuthorityEstablishesTruth : Bool
    positiveRevaluationAloneProvesHistoricalClaim : Bool
    sharedReclaimedSymbolDeterminesDoctrine : Bool
    sharedReclaimedSymbolDeterminesPolitics : Bool
    sharedReclaimedSymbolDeterminesFormationHistory : Bool
    positiveRechartRequiresResidualBeyondWord : Bool
    dialecticalRoleIsFrameRelative : Bool

canonicalSymbolicInversionAuthorityTransferBoundary :
  SymbolicInversionAuthorityTransferBoundary
canonicalSymbolicInversionAuthorityTransferBoundary =
  symbolic-inversion-authority-transfer-boundary
    false false false false false false false false false false true true
