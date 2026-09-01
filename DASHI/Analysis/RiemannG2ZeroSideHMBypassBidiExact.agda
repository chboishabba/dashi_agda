module DASHI.Analysis.RiemannG2ZeroSideHMBypassBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticComplexCharacterExtensionExact as HX
import DASHI.Analysis.RiemannAristotlePoleNearTargetModulationExact as Target
import DASHI.Analysis.RiemannAristotlePoleNearExplicitFormulaBridgeExact as Window
import DASHI.Analysis.RiemannAristotlePoleNearWindowRestrictionResidualExact as HW
import DASHI.Analysis.RiemannG2CanonicalHXToHTCompilerExact as HXToHT
import DASHI.Analysis.RiemannG2PoleNearTargetWindowSpectralIdentificationCompilerExact as Spectral
import DASHI.Analysis.RiemannG2TargetModulationToHWCompilerExact as ToHW

------------------------------------------------------------------------
-- SHORTEST ZERO-SIDE PATH: H_X + LITERAL TARGET WINDOW -> H_T + H_W
--
-- The historical modulation-extension H_M is useful as an aggregate legacy
-- interface, but it is not needed on the shortest route to the finite pole-near
-- consumer.  H_X already compiles to H_T.  Separately, the exact target-window
-- spectral decomposition compiles to ModulationSpectralIdentification and then
-- to H_W.  Therefore the pointwise H_M response factorisation is not a gating
-- prerequisite for the H_W / finite-near branch.
------------------------------------------------------------------------

canonicalHXAndTargetWindowToHW :
  ∀ {analytic space formula} →
  (H_X : HX.RiemannComplexCharacterExtension analytic) →
  (m : Target.PoleNearTargetModulation space) →
  (w : Window.PoleNearTargetWindow space formula) →
  Spectral.SameLiteralPoleNearWindowAttachment m w →
  HW.PoleNearWindowRestriction (HXToHT.canonicalHXToHT H_X)
canonicalHXAndTargetWindowToHW H_X m w attachment =
  ToHW.fixedSpectralIdentificationToHW
    (HXToHT.canonicalHXToHT H_X)
    m
    (Spectral.windowToModulationSpectralIdentification m w attachment)

------------------------------------------------------------------------
-- Dependency audit.
------------------------------------------------------------------------

data ZeroSideNode : Set where
  canonicalHX
  historicalHM
  canonicalHT
  literalTargetModulation
  literalPoleNearTargetWindow
  modulationSpectralIdentification
  historicalHW
  signedFiniteNearEvaluation
  : ZeroSideNode

data EdgeKind : Set where
  compilerEdge
  liveSameObjectEdge
  liveAnalyticEdge
  optionalLegacyEdge
  : EdgeKind

record ZeroSideDependencyEdge : Set where
  constructor zero-side-dependency-edge
  field
    source target : ZeroSideNode
    kind : EdgeKind
    edgeReference : String

open ZeroSideDependencyEdge public

hxToHTEdge : ZeroSideDependencyEdge
hxToHTEdge =
  zero-side-dependency-edge
    canonicalHX canonicalHT compilerEdge
    "RiemannG2CanonicalHXToHTCompilerExact.canonicalHXToHT"

windowToIdentificationEdge : ZeroSideDependencyEdge
windowToIdentificationEdge =
  zero-side-dependency-edge
    literalPoleNearTargetWindow modulationSpectralIdentification
    liveSameObjectEdge
    "Recover the literal PoleNearTargetWindow and identify its selected test with the PoleNearTargetModulation.modulatedPoleTest; the spectral equality itself is already owned by the window object."

identificationToHWEdge : ZeroSideDependencyEdge
identificationToHWEdge =
  zero-side-dependency-edge
    modulationSpectralIdentification historicalHW compilerEdge
    "RiemannG2TargetModulationToHWCompilerExact.fixedSpectralIdentificationToHW"

hmLegacyEdge : ZeroSideDependencyEdge
hmLegacyEdge =
  zero-side-dependency-edge
    historicalHM canonicalHT optionalLegacyEdge
    "Historical H_M may feed older adapters, but canonical H_T is already compiler output directly from H_X."

------------------------------------------------------------------------
-- Search consequences.
------------------------------------------------------------------------

data ZeroSideSearchAction : Set where
  recoverCanonicalHXAction
  recoverLiteralPoleNearTargetWindow
  proveSameSelectedWindowAttachment
  reproveHTAfterHX
  closeHMPointwiseFactorizationBeforeHW
  reproveHWFamilyInterface
  evaluateFiniteSignedNearResponse
  : ZeroSideSearchAction

data SearchStatus : Set where
  live pruned downstream parallel : SearchStatus

searchStatus : ZeroSideSearchAction → SearchStatus
searchStatus recoverCanonicalHXAction = parallel
searchStatus recoverLiteralPoleNearTargetWindow = live
searchStatus proveSameSelectedWindowAttachment = live
searchStatus reproveHTAfterHX = pruned
searchStatus closeHMPointwiseFactorizationBeforeHW = pruned
searchStatus reproveHWFamilyInterface = pruned
searchStatus evaluateFiniteSignedNearResponse = downstream

hmBeforeHWPruned :
  searchStatus closeHMPointwiseFactorizationBeforeHW ≡ pruned
hmBeforeHWPruned = refl

htReproofPruned :
  searchStatus reproveHTAfterHX ≡ pruned
htReproofPruned = refl

hwInterfaceReproofPruned :
  searchStatus reproveHWFamilyInterface ≡ pruned
hwInterfaceReproofPruned = refl

record ZeroSideHMBypassBoundary : Set where
  constructor zero-side-hm-bypass-boundary
  field
    historicalHMIsNecessaryPrerequisiteForHT : Bool
    historicalHMIsNecessaryPrerequisiteForHTIsFalse :
      historicalHMIsNecessaryPrerequisiteForHT ≡ false

    historicalHMIsNecessaryPrerequisiteForHW : Bool
    historicalHMIsNecessaryPrerequisiteForHWIsFalse :
      historicalHMIsNecessaryPrerequisiteForHW ≡ false

    canonicalHXDirectlyCompilesHT : Bool
    canonicalHXDirectlyCompilesHTIsTrue : canonicalHXDirectlyCompilesHT ≡ true

    literalWindowPlusSameObjectAttachmentCompilesHW : Bool
    literalWindowPlusSameObjectAttachmentCompilesHWIsTrue :
      literalWindowPlusSameObjectAttachmentCompilesHW ≡ true

    hmPointwiseFactorizationStillUsefulForLegacyAggregate : Bool
    hmPointwiseFactorizationStillUsefulForLegacyAggregateIsTrue :
      hmPointwiseFactorizationStillUsefulForLegacyAggregate ≡ true

    hmPointwiseFactorizationBlocksFiniteNearEvaluation : Bool
    hmPointwiseFactorizationBlocksFiniteNearEvaluationIsFalse :
      hmPointwiseFactorizationBlocksFiniteNearEvaluation ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalZeroSideHMBypassBoundary : ZeroSideHMBypassBoundary
canonicalZeroSideHMBypassBoundary =
  zero-side-hm-bypass-boundary
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "The shortest zero-side route does not serialize H_X -> H_A -> H_M -> H_T -> H_W. Canonical H_X already generates H_T directly. Independently, a literal PoleNearTargetWindow already owns the cluster + finite-near + far spectral equality; after proving it is the same selected target/window object, that receipt compiles to H_W. The historical H_M pointwise response factorisation remains a useful legacy aggregate theorem but is not a gate on H_W or the finite signed near evaluation. Search priority should therefore move to the literal target-window attachment and then the signed finite-near analytic evaluation. RH is not derived."
