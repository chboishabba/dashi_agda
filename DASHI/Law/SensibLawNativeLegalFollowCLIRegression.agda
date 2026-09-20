module DASHI.Law.SensibLawNativeLegalFollowCLIRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawNativeLegalFollowCLIExact as CLI

boundaryExists : Set
boundaryExists = CLI.NativeLegalFollowCliBoundary

boundaryPaid : boundaryExists
boundaryPaid = CLI.canonicalNativeLegalFollowCliBoundary

nativeRustRemainsCanonicalOwner :
  CLI.canonicalOrchestrationOwner ≡ CLI.nativeRustCli
nativeRustRemainsCanonicalOwner = refl

pythonCannotBecomeCanonicalOwner :
  CLI.canonicalOrchestrationOwner ≡ CLI.pythonCompatibilityShim → ⊥
pythonCannotBecomeCanonicalOwner =
  CLI.pythonCompatibilityOwnerIsNotCanonical

jsonStillCannotBecomeSemanticCommandAbi :
  CLI.JsonArtifactIsSemanticCommandAbi → ⊥
jsonStillCannotBecomeSemanticCommandAbi =
  CLI.jsonIsNotSemanticCommandAbi


cullenOrchestrationRemainsNative :
  CLI.cullenLegalOrchestrationIsNativeRust
    CLI.canonicalNativeLegalFollowCliBoundary
    ≡ true
cullenOrchestrationRemainsNative =
  CLI.cullenLegalOrchestrationIsNativeRustIsTrue
    CLI.canonicalNativeLegalFollowCliBoundary

spacyRemainsParserProducerOnly :
  CLI.spacyIsParserProducerOnly
    CLI.canonicalNativeLegalFollowCliBoundary
    ≡ true
spacyRemainsParserProducerOnly =
  CLI.spacyIsParserProducerOnlyIsTrue
    CLI.canonicalNativeLegalFollowCliBoundary

jsonSemanticCommandTransportRemainsFalse :
  CLI.jsonIsSemanticCommandTransport
    CLI.canonicalNativeLegalFollowCliBoundary
    ≡ false
jsonSemanticCommandTransportRemainsFalse =
  CLI.jsonIsSemanticCommandTransportIsFalse
    CLI.canonicalNativeLegalFollowCliBoundary
