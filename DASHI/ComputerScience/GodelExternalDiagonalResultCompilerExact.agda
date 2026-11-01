module DASHI.ComputerScience.GodelExternalDiagonalResultCompilerExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.GodelDiagonalProvabilityContractExact as Godel
import DASHI.ComputerScience.GodelExternalArithmeticABIMinimalCompilerExact as External

------------------------------------------------------------------------
-- EXTERNAL MACHINE-CHECKED FIXED POINT -> DASHI DIAGONAL-LEMMA RESULT
--
-- If an external arithmetic source already proves its diagonal/fixed-point
-- theorem, DASHI need not reconstruct that proof through a particular local
-- representability architecture.  The only requirement is SAME-CARRIER
-- transport over the restricted unary/sentence/code/derivation fibres.
------------------------------------------------------------------------

record ExternalDiagonalPayment
    (S : External.ExternalArithmeticSource) : Set₁ where
  field
    fixedPointRaw :
      (φ : External.RawFormula S) →
      External.UnaryAdmissible S φ →
      External.RawFormula S

    fixedPointClosed :
      (φ : External.RawFormula S) →
      (u : External.UnaryAdmissible S φ) →
      External.Closed S (fixedPointRaw φ u)

    fixedPointLawRaw :
      (φ : External.RawFormula S) →
      (u : External.UnaryAdmissible S φ) →
      External.RawDeriv S
        (External.BiconditionalRaw S
          (fixedPointRaw φ u)
          (External.instantiateUnaryRaw S φ
            (External.numeral S
              (External.codeFormula S (fixedPointRaw φ u)))))

open ExternalDiagonalPayment public

compileExternalDiagonalLemma :
  (S : External.ExternalArithmeticSource) →
  ExternalDiagonalPayment S →
  Godel.DiagonalLemmaAuthority (External.compileExternalArithmeticSystem S)
compileExternalDiagonalLemma S D =
  record
    { fixedPoint = λ φ →
        External.restrictedSentence
          (fixedPointRaw D (External.rawUnary φ) (External.unaryOK φ))
          (fixedPointClosed D (External.rawUnary φ) (External.unaryOK φ))
    ; fixedPointLaw = λ φ →
        fixedPointLawRaw D (External.rawUnary φ) (External.unaryOK φ)
    }

------------------------------------------------------------------------
-- This is intentionally independent of the local PR-representability
-- compiler.  Both are legitimate producers of the same diagonal consumer.
------------------------------------------------------------------------

data ExternalDiagonalNameImportsResult : Set where
data RepresentabilityRouteIsMandatoryWhenFinishedExternalProofExists : Set where
data DifferentCodeCarrierFixedPointCanTransportWithoutAdapter : Set where

nameDoesNotImportResult : ExternalDiagonalNameImportsResult → ⊥
nameDoesNotImportResult ()

representabilityRouteIsNotMandatory :
  RepresentabilityRouteIsMandatoryWhenFinishedExternalProofExists → ⊥
representabilityRouteIsNotMandatory ()

differentCodeNeedsAdapter : DifferentCodeCarrierFixedPointCanTransportWithoutAdapter → ⊥
differentCodeNeedsAdapter ()

record ExternalDiagonalResultCompilerBoundary : Set where
  constructor externalDiagonalResultCompilerBoundary
  field
    sameCarrierFixedPointCompilerOwned : Bool
    representabilityCompilerStillAvailable : Bool
    representabilityCompilerMandatoryForExternalFinishedProof : Bool
    theoremNameAcceptedAsProof : Bool

canonicalExternalDiagonalResultCompilerBoundary :
  ExternalDiagonalResultCompilerBoundary
canonicalExternalDiagonalResultCompilerBoundary =
  externalDiagonalResultCompilerBoundary true true false false
