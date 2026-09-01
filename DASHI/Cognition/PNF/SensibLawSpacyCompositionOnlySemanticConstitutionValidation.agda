module DASHI.Cognition.PNF.SensibLawSpacyCompositionOnlySemanticConstitutionValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawSpacyCompositionOnlySemanticConstitutionExact as Constitution

regexSemanticShortcutIsEmpty : Constitution.RegexDerivedSemanticEvidence → ⊥
regexSemanticShortcutIsEmpty = Constitution.regexCannotBeSemanticEvidence

positionalActorShortcutIsEmpty : Constitution.PositionalActorShortcut → ⊥
positionalActorShortcutIsEmpty = Constitution.positionBeforeModalCannotDefineActor

firstPostModalActionShortcutIsEmpty : Constitution.FirstPostModalActionShortcut → ⊥
firstPostModalActionShortcutIsEmpty = Constitution.firstPostModalTokenCannotDefineAction

prepositionCutoffObjectShortcutIsEmpty : Constitution.PrepositionCutoffObjectShortcut → ⊥
prepositionCutoffObjectShortcutIsEmpty = Constitution.prepositionCutoffCannotDefineObject

phraseDictionaryScopeShortcutIsEmpty : Constitution.PhraseDictionaryScopeShortcut → ⊥
phraseDictionaryScopeShortcutIsEmpty = Constitution.phraseDictionaryCannotDefineScope

dependencyLabelAloneCannotChooseLegalRole :
  Constitution.DependencyLabelAloneChoosesLegalRole → ⊥
dependencyLabelAloneCannotChooseLegalRole =
  Constitution.dependencyLabelCannotAloneChooseLegalRole

regexBoundaryIsFalse :
  Constitution.regexMayProduceSemanticEvidence Constitution.canonicalCompositionOnlyBoundary ≡ false
regexBoundaryIsFalse = refl

syntacticNarrowingIsAllowed :
  Constitution.dependencyLabelMayNarrowSyntacticRole Constitution.canonicalCompositionOnlyBoundary ≡ true
syntacticNarrowingIsAllowed = refl

legalRoleShortcutIsFalse :
  Constitution.dependencyLabelAloneChoosesLegalRole Constitution.canonicalCompositionOnlyBoundary ≡ false
legalRoleShortcutIsFalse = refl

contextReceiptIsRequired :
  Constitution.semanticResolutionRequiresContextReceipt Constitution.canonicalCompositionOnlyBoundary ≡ true
contextReceiptIsRequired = refl

admissionShortcutIsFalse :
  Constitution.semanticResolutionAutomaticallyAuthorizesAdmission Constitution.canonicalCompositionOnlyBoundary ≡ false
admissionShortcutIsFalse = refl
