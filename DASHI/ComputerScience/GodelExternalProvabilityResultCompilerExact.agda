module DASHI.ComputerScience.GodelExternalProvabilityResultCompilerExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.GodelDiagonalProvabilityContractExact as Godel
import DASHI.ComputerScience.GodelExternalArithmeticABIMinimalCompilerExact as External

------------------------------------------------------------------------
-- EXTERNAL SOURCE PROVABILITY RESULTS -> DASHI RESULT CONTRACTS
--
-- This compiler assumes the arithmetic/source adapter is already paid.  It
-- does not identify theorem names; it transports theorem inhabitants over the
-- SAME restricted sentence and derivation carriers produced by that adapter.
------------------------------------------------------------------------

record ExternalProvabilityPayment
    (S : External.ExternalArithmeticSource) : Set₁ where
  field
    boxRaw : External.RawFormula S → External.RawFormula S
    boxClosed :
      (φ : External.RawFormula S) → External.Closed S φ →
      External.Closed S (boxRaw φ)

    lobRaw :
      (A : External.RawFormula S) →
      External.Closed S A →
      External.RawDeriv S
        (External.ImplicationRaw S (boxRaw A) A) →
      External.RawDeriv S A

    godelIIRaw :
      External.RawDeriv S (External.consistencyRaw S) → ⊥

open ExternalProvabilityPayment public

compileExternalProvabilityStructure :
  (S : External.ExternalArithmeticSource) →
  ExternalProvabilityPayment S →
  Godel.ProvabilityStructure (External.compileExternalArithmeticSystem S)
compileExternalProvabilityStructure S P =
  record
    { box = λ A →
        External.restrictedSentence
          (boxRaw P (External.rawSentence A))
          (boxClosed P
            (External.rawSentence A)
            (External.closedOK A))
    }

compileExternalLob :
  (S : External.ExternalArithmeticSource) →
  (P : ExternalProvabilityPayment S) →
  Godel.LobTheoremResult
    (External.compileExternalArithmeticSystem S)
    (compileExternalProvabilityStructure S P)
compileExternalLob S P =
  record
    { lob = λ A hypothesis →
        lobRaw P
          (External.rawSentence A)
          (External.closedOK A)
          hypothesis
    }

compileExternalGodelII :
  (S : External.ExternalArithmeticSource) →
  ExternalProvabilityPayment S →
  Godel.GodelSecondIncompletenessResult
    (External.compileExternalArithmeticSystem S)
compileExternalGodelII S P =
  record
    { systemCannotProveItsConsistency = godelIIRaw P }

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ExternalLobNameImpliesLocalLob : Set where
data ExternalGodelIINameImpliesLocalGodelII : Set where
data DifferentArithmeticCarrierTheoremTransport : Set where

lobNameDoesNotImportProof : ExternalLobNameImpliesLocalLob → ⊥
lobNameDoesNotImportProof ()

godelIINameDoesNotImportProof : ExternalGodelIINameImpliesLocalGodelII → ⊥
godelIINameDoesNotImportProof ()

differentCarrierDoesNotTransport : DifferentArithmeticCarrierTheoremTransport → ⊥
differentCarrierDoesNotTransport ()

record ExternalProvabilityCompilerBoundary : Set where
  constructor externalProvabilityCompilerBoundary
  field
    sameCarrierBoxCompilerOwned : Bool
    sameCarrierLobCompilerOwned : Bool
    sameCarrierGodelIICompilerOwned : Bool
    theoremNamesAcceptedAsProofs : Bool
    differentArithmeticCarriersSilentlyIdentified : Bool

canonicalExternalProvabilityCompilerBoundary : ExternalProvabilityCompilerBoundary
canonicalExternalProvabilityCompilerBoundary =
  externalProvabilityCompilerBoundary true true true false false
