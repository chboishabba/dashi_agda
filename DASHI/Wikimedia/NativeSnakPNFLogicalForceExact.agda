module DASHI.Wikimedia.NativeSnakPNFLogicalForceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Wikimedia.NativeStatementExact as WD
import DASHI.Wikimedia.AristotleNativeModelSourceExact as Aristotle

------------------------------------------------------------------------
-- NATIVE SNAK LOGICAL FORCE -> PNF INTERPRETATION BOUNDARY
--
-- Aristotle RequestProject.Snaks explicitly gives:
--   value(v)    : positive value assertion;
--   someValue   : existential claim that some value exists;
--   noValue     : negative claim that the property has no value.
-- It further proves satisfiable_iff_clashFree for clashes involving noValue.
--
-- PNF does not currently make negation a QuantifierForce constructor, so this
-- bridge keeps quantifier disposition and polarity separate rather than forcing
-- noValue into an unrelated PNF constructor.
------------------------------------------------------------------------

data SnakLogicalForce : Set where
  concreteValueForce : SnakLogicalForce
  existentialUnknownValueForce : SnakLogicalForce
  explicitNoValueForce : SnakLogicalForce

logicalForce : WD.Snak → SnakLogicalForce
logicalForce (WD.valueSnak value) = concreteValueForce
logicalForce WD.someValue = existentialUnknownValueForce
logicalForce WD.noValue = explicitNoValueForce

data PNFQuantifierDisposition : Set where
  noAutomaticQuantifier : PNFQuantifierDisposition
  existentialQuantifierCandidate : PNFQuantifierDisposition

quantifierDisposition : WD.Snak → PNFQuantifierDisposition
quantifierDisposition (WD.valueSnak value) = noAutomaticQuantifier
quantifierDisposition WD.someValue = existentialQuantifierCandidate
quantifierDisposition WD.noValue = noAutomaticQuantifier

data SnakPolarity : Set where
  positiveValuePolarity : SnakPolarity
  existentialPositivePolarity : SnakPolarity
  explicitNegativePolarity : SnakPolarity

snakPolarity : WD.Snak → SnakPolarity
snakPolarity (WD.valueSnak value) = positiveValuePolarity
snakPolarity WD.someValue = existentialPositivePolarity
snakPolarity WD.noValue = explicitNegativePolarity

someValuePNFQuantifierCandidate :
  quantifierDisposition WD.someValue ≡ existentialQuantifierCandidate
someValuePNFQuantifierCandidate = refl

someValueCanUseExistentialQ : PNF.QuantifierForce
someValueCanUseExistentialQ = PNF.existentialQ

noValueIsExplicitNegative : snakPolarity WD.noValue ≡ explicitNegativePolarity
noValueIsExplicitNegative = refl

snakSourceContract : Aristotle.AristotleDeclarationContract
snakSourceContract = Aristotle.snakSatisfiabilityContract

-- Source-level entailment/satisfiability theorems remain Lean authority until
-- independently reconstructed/proved in Agda.  This module only imports their
-- logical distinctions into the native interpretation boundary.
data SomeValueIsUnknownOrAbsent : Set where
data NoValueIsStatementAbsent : Set where
data NoValueIsUnresolvedEpistemicState : Set where
data LeanSnakSatisfiabilityProofTransportedToAgda : Set where

someValueDoesNotMeanAbsent : SomeValueIsUnknownOrAbsent → ⊥
someValueDoesNotMeanAbsent ()

noValueDoesNotMeanStatementAbsent : NoValueIsStatementAbsent → ⊥
noValueDoesNotMeanStatementAbsent ()

noValueDoesNotDefinitionallyMeanUnresolved : NoValueIsUnresolvedEpistemicState → ⊥
noValueDoesNotDefinitionallyMeanUnresolved ()

leanSnakProofNotSilentlyTransported : LeanSnakSatisfiabilityProofTransportedToAgda → ⊥
leanSnakProofNotSilentlyTransported ()

record NativeSnakPNFBoundary : Set where
  constructor native-snak-pnf-boundary
  field
    someValueHasExistentialShape : Bool
    noValueHasExplicitNegativeShape : Bool
    noValueEqualsStatementAbsence : Bool
    snakDeterminesWholePNFAssertion : Bool
    leanSatisfiabilityProofTransported : Bool

canonicalNativeSnakPNFBoundary : NativeSnakPNFBoundary
canonicalNativeSnakPNFBoundary =
  native-snak-pnf-boundary true true false false false
