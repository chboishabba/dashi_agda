module DASHI.Papers.NavierStokes.TheoremInterfaceRound222Exact where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNClayFrontierRound222Exact as Frontier

activeRoutineCompletionSeamCount : Nat
activeRoutineCompletionSeamCount = Frontier.round222ActiveRoutineCompletionSeamCount

novelMathematicalLeafCount : Nat
novelMathematicalLeafCount = Frontier.round222NovelMathematicalLeafCount

finalResearchTargetTyped : Bool
finalResearchTargetTyped = Frontier.round222FinalResearchTargetTyped

requiresGramNegativity : Bool
requiresGramNegativity = Frontier.round222RequiresGramNegativity

requiresPointwiseCutoffUniformSmallness : Bool
requiresPointwiseCutoffUniformSmallness =
  Frontier.round222RequiresPointwiseCutoffUniformSmallness

physicalCoherentGramResidualBudgetClosed : Bool
physicalCoherentGramResidualBudgetClosed =
  Frontier.round222PhysicalCoherentGramResidualBudgetClosed

packageAClosed : Bool
packageAClosed = Frontier.round222PackageAClosed

clayPromotion : Bool
clayPromotion = Frontier.round222ClayPromotion
