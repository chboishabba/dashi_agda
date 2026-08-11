module DASHI.Cognition.PNF.IdentityEvidenceProduction where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.ProofRelevantIdentityFibres

------------------------------------------------------------------------
-- Parser evidence is stratified before identity admission. Candidate evidence
-- may be useful without carrying permission to establish a document identity.
------------------------------------------------------------------------

data ParserIdentityEvidence : Set where
  dependencyApposition : ParserIdentityEvidence
  personTitleApposition : ParserIdentityEvidence
  properNameExpansion : ParserIdentityEvidence
  explicitAliasCue : ParserIdentityEvidence
  paragraphCoPresence : ParserIdentityEvidence
  lexicalSimilarity : ParserIdentityEvidence

-- Strong local structural evidence may establish a document-local identity.
-- Proper-name expansion is deliberately absent: surname/name expansion needs an
-- independently admitted identity proof before it can be promoted.
data DirectIdentityEvidencePermission : ParserIdentityEvidence → Set where
  appositionMayEstablishIdentity :
    DirectIdentityEvidencePermission dependencyApposition
  titleAppositionMayEstablishIdentity :
    DirectIdentityEvidencePermission personTitleApposition
  explicitAliasMayEstablishIdentity :
    DirectIdentityEvidencePermission explicitAliasCue

properNameExpansionCannotBootstrapIdentity :
  DirectIdentityEvidencePermission properNameExpansion → ⊥
properNameExpansionCannotBootstrapIdentity ()

paragraphCoPresenceCannotBootstrapIdentity :
  DirectIdentityEvidencePermission paragraphCoPresence → ⊥
paragraphCoPresenceCannotBootstrapIdentity ()

lexicalSimilarityCannotBootstrapIdentity :
  DirectIdentityEvidencePermission lexicalSimilarity → ⊥
lexicalSimilarityCannotBootstrapIdentity ()

------------------------------------------------------------------------
-- Name expansion may become admissible only by transporting an already
-- admitted target identity. This corresponds to the runtime corroboration gate
-- rather than treating document-unique surname evidence as proof by itself.
------------------------------------------------------------------------

record CorroboratedNameExpansion : Set where
  constructor corroboratedNameExpansion
  field
    expansionCandidate : ParserIdentityEvidence
    expansionIsProperName : expansionCandidate ≡ properNameExpansion
    targetIdentity : AdmittedIdentityWitness

open CorroboratedNameExpansion public

-- Parser-token -> local-object anchoring is fail-closed. It is a bridge from
-- observation to local object, not a claim that two objects are identical.
data ParserObjectAnchorMultiplicity : Set where
  noLocalObject oneLocalObject severalLocalObjects : ParserObjectAnchorMultiplicity

data ParserObjectAnchorPermission : ParserObjectAnchorMultiplicity → Set where
  oneLocalObjectMayAnchor : ParserObjectAnchorPermission oneLocalObject

noLocalObjectCannotAnchor : ParserObjectAnchorPermission noLocalObject → ⊥
noLocalObjectCannotAnchor ()

severalLocalObjectsCannotAnchor :
  ParserObjectAnchorPermission severalLocalObjects → ⊥
severalLocalObjectsCannotAnchor ()

record IdentityEvidenceProductionBoundary : Set where
  constructor identityEvidenceProductionBoundary
  field
    appositionPermission :
      DirectIdentityEvidencePermission dependencyApposition
    titlePermission :
      DirectIdentityEvidencePermission personTitleApposition
    aliasPermission :
      DirectIdentityEvidencePermission explicitAliasCue
    nameExpansionNeedsCorroboration :
      DirectIdentityEvidencePermission properNameExpansion → ⊥
    coPresenceDenied :
      DirectIdentityEvidencePermission paragraphCoPresence → ⊥
    similarityDenied :
      DirectIdentityEvidencePermission lexicalSimilarity → ⊥

open IdentityEvidenceProductionBoundary public

canonicalIdentityEvidenceProductionBoundary : IdentityEvidenceProductionBoundary
canonicalIdentityEvidenceProductionBoundary =
  identityEvidenceProductionBoundary
    appositionMayEstablishIdentity
    titleAppositionMayEstablishIdentity
    explicitAliasMayEstablishIdentity
    properNameExpansionCannotBootstrapIdentity
    paragraphCoPresenceCannotBootstrapIdentity
    lexicalSimilarityCannotBootstrapIdentity
