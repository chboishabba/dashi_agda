module DASHI.Core.PortableInteractiveViewExact where

open import DASHI.Core.Prelude
open import Data.Maybe using (Maybe; just; nothing)
import DASHI.Core.PortableSemanticInterpretationExact as Portable

------------------------------------------------------------------------
-- FRAMEWORK-NEUTRAL INTERACTIVE VIEW ALGEBRA
--
-- The semantic surface is deliberately about domain-command emission, not
-- exact pixels, layout metrics, retained/immediate implementation strategy,
-- or GPU execution details.
------------------------------------------------------------------------

data UiNode (Command : Set) : Set where
  text : String → UiNode Command
  box : UiNode Command → Maybe Command → UiNode Command
  row : List (UiNode Command) → UiNode Command
  column : List (UiNode Command) → UiNode Command
  button : String → Command → UiNode Command
  canvas : String → UiNode Command

------------------------------------------------------------------------
-- Root activation is the smallest exact interaction semantics needed for the
-- portable contract.  Child traversal/layout hit-testing is intentionally an
-- implementation/refinement concern for later concrete frontends.
------------------------------------------------------------------------

activate :
  ∀ {Command} →
  UiNode Command →
  List Command
activate (text _) = []
activate (box _ nothing) = []
activate (box _ (just command)) = command ∷ []
activate (row _) = []
activate (column _) = []
activate (button _ command) = command ∷ []
activate (canvas _) = []

record InteractiveApplication : Set₁ where
  constructor interactiveApplication
  field
    State : Set
    Command : Set
    view : State → UiNode Command
    reduce : Command → State → State

open InteractiveApplication public

interact :
  ∀ {Command} →
  UiNode Command →
  List Command
interact = activate

------------------------------------------------------------------------
-- Canonical "draw a box with this content; activation emits x" specimen.
------------------------------------------------------------------------

data DemoCommand : Set where
  selectProofNode : DemoCommand

demoNode : UiNode DemoCommand
demoNode = box (text "Proof node") (just selectProofNode)

ActivationContract : Set
ActivationContract =
  activate demoNode ≡ selectProofNode ∷ []

canonicalActivationContract : ActivationContract
canonicalActivationContract = refl

------------------------------------------------------------------------
-- Two frontend implementation roles can carry different rendering metadata
-- while refining the same interaction meaning.
------------------------------------------------------------------------

data FrontendBackend : Set where
  eguiStyle : FrontendBackend
  retainedStyle : FrontendBackend

data RenderingMode : Set where
  immediateMode : RenderingMode
  retainedMode : RenderingMode

record FrontendArtifact : Set where
  constructor frontendArtifact
  field
    tree : UiNode DemoCommand
    renderingMode : RenderingMode

open FrontendArtifact public

FrontendImplementation : FrontendBackend → Set
FrontendImplementation _ = FrontendArtifact

frontendInterpret :
  (backend : FrontendBackend) →
  UiNode DemoCommand →
  FrontendImplementation backend
frontendInterpret eguiStyle uiTree =
  frontendArtifact uiTree immediateMode
frontendInterpret retainedStyle uiTree =
  frontendArtifact uiTree retainedMode

frontendProblem : Portable.SemanticInterpretationProblem
frontendProblem =
  Portable.semanticInterpretationProblem
    (UiNode DemoCommand)
    (List DemoCommand)
    FrontendBackend
    FrontendImplementation
    ⊤
    (λ _ → List DemoCommand)
    activate
    (λ _ meaning → meaning)
    frontendInterpret
    (λ _ _ implementation → activate (tree implementation))

eguiRefinesActivation :
  Portable.SemanticRefinement
    frontendProblem eguiStyle demoNode tt
eguiRefinesActivation = Portable.semanticRefinement refl

retainedRefinesActivation :
  Portable.SemanticRefinement
    frontendProblem retainedStyle demoNode tt
retainedRefinesActivation = Portable.semanticRefinement refl

CanonicalFrontendEquivalence : Set
CanonicalFrontendEquivalence =
  Portable.BackendEquivalentFor
    frontendProblem demoNode tt eguiStyle retainedStyle

canonicalFrontendEquivalence : CanonicalFrontendEquivalence
canonicalFrontendEquivalence =
  Portable.twoRefinementsGiveConsumerEquivalence
    eguiRefinesActivation
    retainedRefinesActivation

record PortableInteractiveViewBoundary : Set where
  constructor portableInteractiveViewBoundary
  field
    frameworkEventIsDomainCommand : Bool
    frameworkEventIsDomainCommandIsFalse :
      frameworkEventIsDomainCommand ≡ false
    interactionSemanticsRequiresPixelEquality : Bool
    interactionSemanticsRequiresPixelEqualityIsFalse :
      interactionSemanticsRequiresPixelEquality ≡ false
    renderingModeDifferencePreventsCommandEquivalence : Bool
    renderingModeDifferencePreventsCommandEquivalenceIsFalse :
      renderingModeDifferencePreventsCommandEquivalence ≡ false

canonicalPortableInteractiveViewBoundary : PortableInteractiveViewBoundary
canonicalPortableInteractiveViewBoundary =
  portableInteractiveViewBoundary
    false refl
    false refl
    false refl
