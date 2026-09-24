module DASHI.Interop.PortableInteractiveGpuProjectionExact where

open import DASHI.Core.Prelude
import DASHI.Core.PortableSemanticInterpretationExact as Portable

------------------------------------------------------------------------
-- PORTABLE INTERACTIVE SHELL / GPU PROJECTION OWNER
--
-- Native shell events and GPU picks are proposal mechanisms.  They acquire
-- semantic force only by decoding to the same admitted domain-command
-- language and entering the same reducer.
------------------------------------------------------------------------

record PortableInteractiveGpuProjection : Set₁ where
  constructor portableInteractiveGpuProjection
  field
    SemanticState : Set
    DomainCommand : Set

    ShellProjection : Set
    VisualProjection : Set
    ShellInput : Set
    GpuInput : Set

    projectShell : SemanticState → ShellProjection
    projectVisual : SemanticState → VisualProjection

    decodeShell : ShellInput → DomainCommand
    decodeGpu : GpuInput → DomainCommand

    step : DomainCommand → SemanticState → SemanticState

open PortableInteractiveGpuProjection public

sameDecodedCommandSameTransition :
  ∀ {owner}
    {state : SemanticState owner}
    {shellInput : ShellInput owner}
    {gpuInput : GpuInput owner} →
  decodeShell owner shellInput ≡ decodeGpu owner gpuInput →
  step owner (decodeShell owner shellInput) state
    ≡
  step owner (decodeGpu owner gpuInput) state
sameDecodedCommandSameTransition refl = refl

------------------------------------------------------------------------
-- Consumer-indexed renderer parity is inherited from the existing portable
-- semantic interpretation parent.  This bridge deliberately says nothing
-- about pixel, geometry, execution-order, or performance equality.
------------------------------------------------------------------------

record PortableInteractiveGpuProjectionBoundary : Set where
  constructor portableInteractiveGpuProjectionBoundary
  field
    visualProjectionRequiresShellFactorisation : Bool
    visualProjectionRequiresShellFactorisationIsFalse :
      visualProjectionRequiresShellFactorisation ≡ false

    gpuPickCreatesSemanticAuthority : Bool
    gpuPickCreatesSemanticAuthorityIsFalse :
      gpuPickCreatesSemanticAuthority ≡ false

    shellEventCreatesSemanticAuthority : Bool
    shellEventCreatesSemanticAuthorityIsFalse :
      shellEventCreatesSemanticAuthority ≡ false

    hiddenFromVisualMeansAbsentFromWorld : Bool
    hiddenFromVisualMeansAbsentFromWorldIsFalse :
      hiddenFromVisualMeansAbsentFromWorld ≡ false

    rendererParityRequiresPixelParity : Bool
    rendererParityRequiresPixelParityIsFalse :
      rendererParityRequiresPixelParity ≡ false

    performanceWitnessCreatesSemanticIdentity : Bool
    performanceWitnessCreatesSemanticIdentityIsFalse :
      performanceWitnessCreatesSemanticIdentity ≡ false

    jsonSemanticCommandTransport : Bool
    jsonSemanticCommandTransportIsFalse :
      jsonSemanticCommandTransport ≡ false

    regexSemanticCommandParser : Bool
    regexSemanticCommandParserIsFalse :
      regexSemanticCommandParser ≡ false

canonicalPortableInteractiveGpuProjectionBoundary :
  PortableInteractiveGpuProjectionBoundary
canonicalPortableInteractiveGpuProjectionBoundary =
  portableInteractiveGpuProjectionBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Explicit parent anchor: interaction parity is a child of portable semantic
-- interpretation, not a replacement semantics.
------------------------------------------------------------------------

ParentSemanticBoundary : Set
ParentSemanticBoundary = Portable.PortableSemanticInterpretationBoundary

parentSemanticBoundaryPaid : ParentSemanticBoundary
parentSemanticBoundaryPaid =
  Portable.canonicalPortableSemanticInterpretationBoundary
