module DASHI.Analysis.RiemannAnalyticModulationBidiAssemblyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannFormulaAnalyticCompatibility as Compat
import DASHI.Analysis.RiemannAnalyticComplexCharacterExtensionExact as Character
import DASHI.Analysis.RiemannAnalyticTestModulationShiftExact as Action
import DASHI.Analysis.RiemannAnalyticModulationExtensionExact as Mod

------------------------------------------------------------------------
-- BIDI ASSEMBLY: H_X + H_A -> H_M
--
-- This owner prevents the aggregate modulation extension from being inhabited
-- by independently chosen character and test-action conventions.
------------------------------------------------------------------------

record RiemannAnalyticModulationAssembly
    (analytic : Analytic.AnalyticSubstrate)
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (compat : Compat.RiemannFormulaAnalyticCompatibility analytic space formula)
    (H_X : Character.RiemannComplexCharacterExtension analytic)
    (H_A : Action.RiemannTestModulationShift analytic space formula compat H_X) : Set₁ where
  constructor riemann-analytic-modulation-assembly
  field
    H_M : Mod.RiemannAnalyticModulationExtension analytic space formula compat

    sameHXCharacterUsedByHM : Set
    sameHATestActionUsedByHM : Set
    sameCanonicalAnalyticCarrier : Set
    sameCanonicalWeilCarrier : Set
    sameConcreteExplicitFormula : Set

    targetDifferenceAgreesWithHX : Set
    targetCharacterAgreesWithHX : Set
    modulationOperationAgreesWithHA : Set
    admissibilityProofAgreesWithHA : Set
    spectralShiftProofAgreesWithHA : Set

    assemblyReference : String

open RiemannAnalyticModulationAssembly public

record ModulationAssemblyBoundary : Set where
  constructor modulation-assembly-boundary
  field
    H_XAloneClosesHM : Bool
    H_XAloneClosesHMIsFalse : H_XAloneClosesHM ≡ false

    H_AWithoutHXClosesHM : Bool
    H_AWithoutHXClosesHMIsFalse : H_AWithoutHXClosesHM ≡ false

    sameCharacterAndActionConventionsRequired : Bool
    sameCharacterAndActionConventionsRequiredIsTrue :
      sameCharacterAndActionConventionsRequired ≡ true

    sameExplicitFormulaRequired : Bool
    sameExplicitFormulaRequiredIsTrue : sameExplicitFormulaRequired ≡ true

    H_MClosed : Bool
    H_MClosedIsFalse : H_MClosed ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

canonicalModulationAssemblyBoundary : ModulationAssemblyBoundary
canonicalModulationAssemblyBoundary =
  modulation-assembly-boundary
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
