module DASHI.Governance.HansonStuntLacanIrigarayGrammarValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Core.TernaryRoleCarrierExact as Ternary
import DASHI.Core.LacanIrigarayTernaryGrammarBridgeExact as Bridge
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.HansonStuntLacanIrigarayGrammarExact as H

allRelabellingsFail :
  (permutation : Ternary.TernaryPermutation) →
  Bridge.GrammarPreserving permutation → ⊥
allRelabellingsFail =
  H.noRelabellingTurnsStuntMasterGraphIntoReciprocalGraph

visibilityStillDoesNotRecoverAuthority :
  INF.FactorsThrough H.burqaVisibility H.burqaSubjectAuthority → ⊥
visibilityStillDoesNotRecoverAuthority =
  H.visibilityDoesNotRecoverOriginatingAuthority

repairIsNotSignFlip :
  H.feministRepairIsSignFlip H.canonicalHansonLacanIrigarayBoundary ≡ false
repairIsNotSignFlip =
  H.feministRepairIsSignFlipIsFalse H.canonicalHansonLacanIrigarayBoundary

grammarRelabellingDoesNotEquate :
  H.relabellingEquatesGrammars H.canonicalHansonLacanIrigarayBoundary ≡ false
grammarRelabellingDoesNotEquate =
  H.relabellingEquatesGrammarsIsFalse H.canonicalHansonLacanIrigarayBoundary

reciprocalRepairHasNoMasterCenter :
  H.reciprocalGrammarHasMasterCenter H.canonicalHansonLacanIrigarayBoundary ≡ false
reciprocalRepairHasNoMasterCenter =
  H.reciprocalGrammarHasMasterCenterIsFalse H.canonicalHansonLacanIrigarayBoundary

representationStillNotAuthority :
  H.representationEqualsSubjectAuthority H.canonicalHansonLacanIrigarayBoundary ≡ false
representationStillNotAuthority =
  H.representationEqualsSubjectAuthorityIsFalse H.canonicalHansonLacanIrigarayBoundary

antiLacanianDoesNotEraseLacanianLens :
  H.antiLacanianConstructionErasesLacanianLens H.canonicalHansonLacanIrigarayBoundary ≡ false
antiLacanianDoesNotEraseLacanianLens =
  H.antiLacanianConstructionErasesLacanianLensIsFalse H.canonicalHansonLacanIrigarayBoundary

oneTheoryNotMadeSovereign :
  H.oneTheoryMadeSovereign H.canonicalHansonLacanIrigarayBoundary ≡ false
oneTheoryNotMadeSovereign =
  H.oneTheoryMadeSovereignIsFalse H.canonicalHansonLacanIrigarayBoundary

renameOnlyCannotRepair :
  H.RenameOnlyBecomesReciprocalGrammar → ⊥
renameOnlyCannotRepair =
  H.renameOnlyCannotConstructReciprocalGrammar

newMasterNotInstalled :
  H.FeministRepairMeansWomanOccupiesMasterCenter → ⊥
newMasterNotInstalled =
  H.feministRepairDoesNotInstallNewMaster
