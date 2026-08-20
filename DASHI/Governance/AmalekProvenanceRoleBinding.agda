module DASHI.Governance.AmalekProvenanceRoleBinding where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Amalek provenance / role-binding boundary.
--
-- Scriptural sources retained by this formal carrier include Genesis 36 and
-- Deuteronomy 25:17-19.  The DASHI construction deliberately distinguishes
-- the source referent/narrative from a modern analogy and from transport of an
-- ancient command into a contemporary policy.
--
-- Reuven Firestone, "Who Is the Enemy?", chapter 6 in
-- Holy War in Judaism: The Fall and Rise of a Controversial Idea,
-- Oxford University Press, 2012, pp. 99-107.
-- DOI: 10.1093/acprof:oso/9780199860302.003.0007
--
-- Firestone's historical analysis motivates retaining reception history and
-- distinguishing the ancient referent from later paradigmatic/metaphorical
-- uses.  It is not proof authority for any contemporary empirical analogy.
------------------------------------------------------------------------

record ScripturalReceipt : Set where
  constructor scripturalReceipt
  field
    sourceLabel : String
    sourceTextScope : String

open ScripturalReceipt public

record InterpretationReceipt : Set where
  constructor interpretationReceipt
  field
    interpreterOrSource : String
    interpretationScope : String

open InterpretationReceipt public

record AmalekProvenance : Set where
  constructor amalekProvenance
  field
    genealogicalSource : ScripturalReceipt
    attackNarrative : ScripturalReceipt
    remembranceCommand : ScripturalReceipt
    erasureCommand : ScripturalReceipt
    receptionHistory : List InterpretationReceipt

open AmalekProvenance public

data AmalekNarrativeRole : Set where
  scripturalReferent : AmalekNarrativeRole
  rearAttackOnWearyAndVulnerable : AmalekNarrativeRole
  remembranceObligation : AmalekNarrativeRole
  blottingOutCommand : AmalekNarrativeRole

------------------------------------------------------------------------
-- Contemporary role binding is an analogy edge, not identity assignment.
------------------------------------------------------------------------

record AmalekRoleBinding (Actor : Set) : Set₁ where
  constructor amalekRoleBinding
  field
    subject : Actor
    provenance : AmalekProvenance
    AnalogyEvidence : Set
    proposedAnalogy : AnalogyEvidence

open AmalekRoleBinding public

record CommandTransport
    {Actor : Set}
    (binding : AmalekRoleBinding Actor) : Set₁ where
  constructor commandTransport
  field
    ModernAction : Set
    CommandImportEvidence : Set
    commandImportEvidence : CommandImportEvidence
    proposedAction : ModernAction

open CommandTransport public

------------------------------------------------------------------------
-- Three distinct promotion failures must not be fused.
------------------------------------------------------------------------

data AmalekPromotionFailureKind : Set where
  analogyFailure : AmalekPromotionFailureKind
  collectiveRolePropagation : AmalekPromotionFailureKind
  ancientCommandImport : AmalekPromotionFailureKind

data ForbiddenAmalekPromotion : AmalekPromotionFailureKind → Set where

forbiddenAnalogyPromotionImpossible :
  ForbiddenAmalekPromotion analogyFailure → ⊥
forbiddenAnalogyPromotionImpossible ()

forbiddenCollectiveRolePromotionImpossible :
  ForbiddenAmalekPromotion collectiveRolePropagation → ⊥
forbiddenCollectiveRolePromotionImpossible ()

forbiddenCommandImportImpossible :
  ForbiddenAmalekPromotion ancientCommandImport → ⊥
forbiddenCommandImportImpossible ()

------------------------------------------------------------------------
-- No inherited collective guilt / exterminatory import constructor.
------------------------------------------------------------------------

data InheritedCollectiveGuiltImport : Set where

data ExterminatoryCommandImport : Set where

inheritedCollectiveGuiltImportImpossible :
  InheritedCollectiveGuiltImport → ⊥
inheritedCollectiveGuiltImportImpossible ()

exterminatoryCommandImportImpossible :
  ExterminatoryCommandImport → ⊥
exterminatoryCommandImportImpossible ()

------------------------------------------------------------------------
-- The dangerous contemporary composition is represented as four separately
-- witnessed stages.  Possessing an ancient source receipt does not construct
-- any later stage.  In particular there is no function
--
-- AmalekProvenance -> ContemporaryAction.
------------------------------------------------------------------------

record AmalekPromotionChain (Actor : Set) : Set₁ where
  field
    binding : AmalekRoleBinding Actor
    command : CommandTransport binding
    Group : Set
    groupOf : Actor → Group
    CollectivePropagationEvidence : Set
    collectivePropagationEvidence : CollectivePropagationEvidence
    TerminalisationEvidence : Set
    terminalisationEvidence : TerminalisationEvidence

open AmalekPromotionChain public

data ProvenanceAutomaticallyBuildsPromotionChain
    {Actor : Set}
    (p : AmalekProvenance) : Set where

provenanceDoesNotAutomaticallyBuildPromotionChain :
  ∀ {Actor} {p : AmalekProvenance} →
  ProvenanceAutomaticallyBuildsPromotionChain {Actor} p → ⊥
provenanceDoesNotAutomaticallyBuildPromotionChain ()

------------------------------------------------------------------------
-- Canonical source receipts.  These record provenance labels only; this
-- module does not attempt a theological adjudication or modern identification.
------------------------------------------------------------------------

genesis36Receipt : ScripturalReceipt
genesis36Receipt =
  scripturalReceipt
    "Genesis 36"
    "genealogical Amalek referent"

deuteronomy25AttackReceipt : ScripturalReceipt
deuteronomy25AttackReceipt =
  scripturalReceipt
    "Deuteronomy 25:17-18"
    "attack on Israel while weary, including those at the rear"

deuteronomy25RememberReceipt : ScripturalReceipt
deuteronomy25RememberReceipt =
  scripturalReceipt
    "Deuteronomy 25:17"
    "remember what Amalek did"

deuteronomy25EraseReceipt : ScripturalReceipt
deuteronomy25EraseReceipt =
  scripturalReceipt
    "Deuteronomy 25:19"
    "blot out remembrance while retaining do-not-forget command context"

firestoneReceptionReceipt : InterpretationReceipt
firestoneReceptionReceipt =
  interpretationReceipt
    "Reuven Firestone, 2012"
    "rabbinic schematisation and later paradigmatic/metaphorical Amalek"

canonicalAmalekProvenance : AmalekProvenance
canonicalAmalekProvenance =
  amalekProvenance
    genesis36Receipt
    deuteronomy25AttackReceipt
    deuteronomy25RememberReceipt
    deuteronomy25EraseReceipt
    (firestoneReceptionReceipt ∷ [])

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AmalekBoundary : Set where
  constructor amalekBoundary
  field
    amalekEqualsTerminalisation : Bool
    amalekEqualsTerminalisationIsFalse :
      amalekEqualsTerminalisation ≡ false
    roleBindingEqualsIdentity : Bool
    roleBindingEqualsIdentityIsFalse :
      roleBindingEqualsIdentity ≡ false
    commandTransportRequiresSeparateEvidence : Bool
    commandTransportRequiresSeparateEvidenceIsTrue :
      commandTransportRequiresSeparateEvidence ≡ true

canonicalAmalekBoundary : AmalekBoundary
canonicalAmalekBoundary =
  amalekBoundary false refl false refl true refl
