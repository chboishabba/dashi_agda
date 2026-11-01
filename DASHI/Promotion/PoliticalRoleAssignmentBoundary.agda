module DASHI.Promotion.PoliticalRoleAssignmentBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Political role-assignment boundary.
--
-- This module is a receipt surface, not an adjudicator.  It blocks assigning
-- live political actors, communities, movements, conflicts, or protected
-- identities to formal roles such as "Amalek operator", "Intifada/Event",
-- "aggressor", or "protected identity" unless an external source corpus,
-- taxonomy, role-binding rule, validation lane, and governance decision are
-- all supplied outside this module.
--
-- The only positive surface here is structural characterization of evidence
-- graphs.  It may describe graph shape, custody, and unresolved requirements;
-- it never classifies real-world actors, authorizes violence or erasure,
-- supplies legal/policy authority, or grants dehumanizing classifier authority.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Blocked role vocabulary.

data PoliticalRoleAssignmentTarget : Set where
  amalekOperatorRole :
    PoliticalRoleAssignmentTarget

  intifadaEventRole :
    PoliticalRoleAssignmentTarget

  aggressorRole :
    PoliticalRoleAssignmentTarget

  protectedIdentityRole :
    PoliticalRoleAssignmentTarget

  enemyCombatantRole :
    PoliticalRoleAssignmentTarget

  terroristRole :
    PoliticalRoleAssignmentTarget

  civilianProtectedPersonRole :
    PoliticalRoleAssignmentTarget

  legitimateMilitaryTargetRole :
    PoliticalRoleAssignmentTarget

  genocideOrErasureTargetRole :
    PoliticalRoleAssignmentTarget

  legalResponsibilityRole :
    PoliticalRoleAssignmentTarget

roleLabel :
  PoliticalRoleAssignmentTarget →
  String
roleLabel amalekOperatorRole =
  "Amalek operator"
roleLabel intifadaEventRole =
  "Intifada/Event"
roleLabel aggressorRole =
  "aggressor"
roleLabel protectedIdentityRole =
  "protected identity"
roleLabel enemyCombatantRole =
  "enemy combatant"
roleLabel terroristRole =
  "terrorist"
roleLabel civilianProtectedPersonRole =
  "civilian protected person"
roleLabel legitimateMilitaryTargetRole =
  "legitimate military target"
roleLabel genocideOrErasureTargetRole =
  "genocide/erasure target"
roleLabel legalResponsibilityRole =
  "legal responsibility role"

canonicalBlockedRoleTargets :
  List PoliticalRoleAssignmentTarget
canonicalBlockedRoleTargets =
  amalekOperatorRole
  ∷ intifadaEventRole
  ∷ aggressorRole
  ∷ protectedIdentityRole
  ∷ enemyCombatantRole
  ∷ terroristRole
  ∷ civilianProtectedPersonRole
  ∷ legitimateMilitaryTargetRole
  ∷ genocideOrErasureTargetRole
  ∷ legalResponsibilityRole
  ∷ []

canonicalBlockedRoleTargetCount :
  Nat
canonicalBlockedRoleTargetCount =
  listCount canonicalBlockedRoleTargets

canonicalBlockedRoleTargetCountIsTen :
  canonicalBlockedRoleTargetCount ≡ suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
canonicalBlockedRoleTargetCountIsTen =
  refl

------------------------------------------------------------------------
-- Required gates.

data PoliticalRoleAssignmentGate : Set where
  sourceCorpusGate :
    PoliticalRoleAssignmentGate

  taxonomyGate :
    PoliticalRoleAssignmentGate

  roleBindingGate :
    PoliticalRoleAssignmentGate

  validationGate :
    PoliticalRoleAssignmentGate

  externalGovernanceGate :
    PoliticalRoleAssignmentGate

gateLabel :
  PoliticalRoleAssignmentGate →
  String
gateLabel sourceCorpusGate =
  "versioned source corpus"
gateLabel taxonomyGate =
  "accepted taxonomy"
gateLabel roleBindingGate =
  "role-binding rule"
gateLabel validationGate =
  "independent validation"
gateLabel externalGovernanceGate =
  "external governance"

canonicalPoliticalRoleAssignmentGates :
  List PoliticalRoleAssignmentGate
canonicalPoliticalRoleAssignmentGates =
  sourceCorpusGate
  ∷ taxonomyGate
  ∷ roleBindingGate
  ∷ validationGate
  ∷ externalGovernanceGate
  ∷ []

canonicalPoliticalRoleAssignmentGateCount :
  Nat
canonicalPoliticalRoleAssignmentGateCount =
  listCount canonicalPoliticalRoleAssignmentGates

canonicalPoliticalRoleAssignmentGateCountIsFive :
  canonicalPoliticalRoleAssignmentGateCount ≡ suc (suc (suc (suc (suc zero))))
canonicalPoliticalRoleAssignmentGateCountIsFive =
  refl

record PoliticalRoleGateStatus : Set where
  field
    sourceCorpusSupplied :
      Bool

    sourceCorpusSuppliedIsFalseByDefault :
      sourceCorpusSupplied ≡ false

    taxonomyAccepted :
      Bool

    taxonomyAcceptedIsFalseByDefault :
      taxonomyAccepted ≡ false

    roleBindingAccepted :
      Bool

    roleBindingAcceptedIsFalseByDefault :
      roleBindingAccepted ≡ false

    validationAccepted :
      Bool

    validationAcceptedIsFalseByDefault :
      validationAccepted ≡ false

    externalGovernanceAccepted :
      Bool

    externalGovernanceAcceptedIsFalseByDefault :
      externalGovernanceAccepted ≡ false

open PoliticalRoleGateStatus public

canonicalPoliticalRoleGateStatus :
  PoliticalRoleGateStatus
canonicalPoliticalRoleGateStatus =
  record
    { sourceCorpusSupplied =
        false
    ; sourceCorpusSuppliedIsFalseByDefault =
        refl
    ; taxonomyAccepted =
        false
    ; taxonomyAcceptedIsFalseByDefault =
        refl
    ; roleBindingAccepted =
        false
    ; roleBindingAcceptedIsFalseByDefault =
        refl
    ; validationAccepted =
        false
    ; validationAcceptedIsFalseByDefault =
        refl
    ; externalGovernanceAccepted =
        false
    ; externalGovernanceAcceptedIsFalseByDefault =
        refl
    }

------------------------------------------------------------------------
-- Structural evidence-graph lane.

data EvidenceGraphStructuralPattern : Set where
  citationDAGPattern :
    EvidenceGraphStructuralPattern

  provenanceChainPattern :
    EvidenceGraphStructuralPattern

  claimCounterclaimBraidPattern :
    EvidenceGraphStructuralPattern

  chronologyWindowPattern :
    EvidenceGraphStructuralPattern

  sourceDisagreementClusterPattern :
    EvidenceGraphStructuralPattern

  unresolvedRoleBindingGapPattern :
    EvidenceGraphStructuralPattern

record StructuralEvidenceGraphCharacterization : Set where
  field
    graphId :
      String

    observedPatterns :
      List EvidenceGraphStructuralPattern

    sourceCorpusDigest :
      String

    custodyDigest :
      String

    actorLabelsOpaque :
      Bool

    actorLabelsOpaqueIsTrue :
      actorLabelsOpaque ≡ true

    structuralPatternOnly :
      Bool

    structuralPatternOnlyIsTrue :
      structuralPatternOnly ≡ true

    realWorldRoleAdjudicated :
      Bool

    realWorldRoleAdjudicatedIsFalse :
      realWorldRoleAdjudicated ≡ false

open StructuralEvidenceGraphCharacterization public

canonicalStructuralEvidenceGraphCharacterization :
  StructuralEvidenceGraphCharacterization
canonicalStructuralEvidenceGraphCharacterization =
  record
    { graphId =
        "unbound-evidence-graph"
    ; observedPatterns =
        citationDAGPattern
        ∷ provenanceChainPattern
        ∷ claimCounterclaimBraidPattern
        ∷ chronologyWindowPattern
        ∷ sourceDisagreementClusterPattern
        ∷ unresolvedRoleBindingGapPattern
        ∷ []
    ; sourceCorpusDigest =
        "not-supplied"
    ; custodyDigest =
        "not-supplied"
    ; actorLabelsOpaque =
        true
    ; actorLabelsOpaqueIsTrue =
        refl
    ; structuralPatternOnly =
        true
    ; structuralPatternOnlyIsTrue =
        refl
    ; realWorldRoleAdjudicated =
        false
    ; realWorldRoleAdjudicatedIsFalse =
        refl
    }

------------------------------------------------------------------------
-- Block receipt and false authority lemmas.

record PoliticalRoleAssignmentBoundaryReceipt : Set where
  field
    blockedTargets :
      List PoliticalRoleAssignmentTarget

    blockedTargetsAreCanonical :
      blockedTargets ≡ canonicalBlockedRoleTargets

    requiredGates :
      List PoliticalRoleAssignmentGate

    requiredGatesAreCanonical :
      requiredGates ≡ canonicalPoliticalRoleAssignmentGates

    gateStatus :
      PoliticalRoleGateStatus

    gateStatusIsCanonical :
      gateStatus ≡ canonicalPoliticalRoleGateStatus

    structuralCharacterization :
      StructuralEvidenceGraphCharacterization

    structuralCharacterizationIsCanonical :
      structuralCharacterization ≡ canonicalStructuralEvidenceGraphCharacterization

    livePoliticalActorRoleAssignmentAuthorized :
      Bool

    livePoliticalActorRoleAssignmentAuthorizedIsFalse :
      livePoliticalActorRoleAssignmentAuthorized ≡ false

    politicalConflictRoleAssignmentAuthorized :
      Bool

    politicalConflictRoleAssignmentAuthorizedIsFalse :
      politicalConflictRoleAssignmentAuthorized ≡ false

    protectedIdentityRoleAssignmentAuthorized :
      Bool

    protectedIdentityRoleAssignmentAuthorizedIsFalse :
      protectedIdentityRoleAssignmentAuthorized ≡ false

    politicalAdjudicationAuthority :
      Bool

    noPoliticalAdjudicationAuthority :
      politicalAdjudicationAuthority ≡ false

    dehumanizingClassifierAuthority :
      Bool

    noDehumanizingClassifierAuthority :
      dehumanizingClassifierAuthority ≡ false

    violenceOrErasureAuthority :
      Bool

    noViolenceOrErasureAuthority :
      violenceOrErasureAuthority ≡ false

    legalPolicyAuthority :
      Bool

    noLegalPolicyAuthority :
      legalPolicyAuthority ≡ false

open PoliticalRoleAssignmentBoundaryReceipt public

canonicalPoliticalRoleAssignmentBoundaryReceipt :
  PoliticalRoleAssignmentBoundaryReceipt
canonicalPoliticalRoleAssignmentBoundaryReceipt =
  record
    { blockedTargets =
        canonicalBlockedRoleTargets
    ; blockedTargetsAreCanonical =
        refl
    ; requiredGates =
        canonicalPoliticalRoleAssignmentGates
    ; requiredGatesAreCanonical =
        refl
    ; gateStatus =
        canonicalPoliticalRoleGateStatus
    ; gateStatusIsCanonical =
        refl
    ; structuralCharacterization =
        canonicalStructuralEvidenceGraphCharacterization
    ; structuralCharacterizationIsCanonical =
        refl
    ; livePoliticalActorRoleAssignmentAuthorized =
        false
    ; livePoliticalActorRoleAssignmentAuthorizedIsFalse =
        refl
    ; politicalConflictRoleAssignmentAuthorized =
        false
    ; politicalConflictRoleAssignmentAuthorizedIsFalse =
        refl
    ; protectedIdentityRoleAssignmentAuthorized =
        false
    ; protectedIdentityRoleAssignmentAuthorizedIsFalse =
        refl
    ; politicalAdjudicationAuthority =
        false
    ; noPoliticalAdjudicationAuthority =
        refl
    ; dehumanizingClassifierAuthority =
        false
    ; noDehumanizingClassifierAuthority =
        refl
    ; violenceOrErasureAuthority =
        false
    ; noViolenceOrErasureAuthority =
        refl
    ; legalPolicyAuthority =
        false
    ; noLegalPolicyAuthority =
        refl
    }

canonicalNoPoliticalAdjudication :
  politicalAdjudicationAuthority canonicalPoliticalRoleAssignmentBoundaryReceipt ≡ false
canonicalNoPoliticalAdjudication =
  refl

canonicalNoDehumanizingClassifierAuthority :
  dehumanizingClassifierAuthority canonicalPoliticalRoleAssignmentBoundaryReceipt ≡ false
canonicalNoDehumanizingClassifierAuthority =
  refl

canonicalNoViolenceOrErasureAuthority :
  violenceOrErasureAuthority canonicalPoliticalRoleAssignmentBoundaryReceipt ≡ false
canonicalNoViolenceOrErasureAuthority =
  refl

canonicalNoLegalPolicyAuthority :
  legalPolicyAuthority canonicalPoliticalRoleAssignmentBoundaryReceipt ≡ false
canonicalNoLegalPolicyAuthority =
  refl

canonicalStructuralLaneDoesNotAdjudicate :
  realWorldRoleAdjudicated canonicalStructuralEvidenceGraphCharacterization ≡ false
canonicalStructuralLaneDoesNotAdjudicate =
  refl
