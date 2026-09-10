module DASHI.ComputerScience.GodelBase12SelfSubstitutionPRFrontierExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.GodelArithmeticRawSyntaxExact as Syntax
import DASHI.ComputerScience.GodelArithmeticDeBruijnInstantiationExact as Inst
import DASHI.ComputerScience.GodelArithmeticBase12NatRetractionExact as NatCodec
import DASHI.ComputerScience.GodelPrimitiveRecursiveRepresentabilityBridgeExact as PR

------------------------------------------------------------------------
-- SAME-CODE PRIMITIVE-RECURSIVE FRONTIER FOR THE CONCRETE BASE-12 CODE
--
-- Computability of the already-owned encoder/decoder is not promoted to a
-- primitive-recursive certificate.  This module identifies the exact local
-- closure payments required for the concrete substitution/self-substitution
-- producer.
------------------------------------------------------------------------

record Base12PrimitiveRecursivePayments : Set₁ where
  constructor base12PrimitiveRecursivePayments
  field
    fixedBase12RemainderPR : PR.PrimitiveRecursiveUnary (λ n → n % 12)
    fixedBase12QuotientPR  : PR.PrimitiveRecursiveUnary (λ n → n / 12)

    formulaDecoderCodePR :
      PR.PrimitiveRecursiveUnary
        (λ n → NatCodec.encodeFormulaNat (NatCodec.decodeFormulaNat n))

    numeralEncodingPR :
      PR.PrimitiveRecursiveUnary
        (λ n → NatCodec.encodeFormulaNat
          (Syntax.equalFormula (Inst.numeralTerm n) (Inst.numeralTerm n)))

open Base12PrimitiveRecursivePayments public

------------------------------------------------------------------------
-- The exact concrete meta-level code substitution function.
--
-- We keep this separate from the abstract formal-system substituteCode until
-- a same-code weld identifies the raw arithmetic carrier with that system.
------------------------------------------------------------------------

concreteSubstituteX0Code : Nat → Nat → Nat
concreteSubstituteX0Code formulaCode numeral =
  NatCodec.encodeFormulaNat
    (Inst.instantiateX0
      (NatCodec.decodeFormulaNat formulaCode)
      (Inst.numeralTerm numeral))

concreteSelfSubstituteCode : Nat → Nat
concreteSelfSubstituteCode code = concreteSubstituteX0Code code code

------------------------------------------------------------------------
-- Exact PR closure authority needed for this repo-specific composition.
-- This is deliberately smaller than a whole primitive-recursion library.
------------------------------------------------------------------------

record ConcreteSubstitutionPrimitiveRecursiveAuthority : Set₁ where
  constructor concreteSubstitutionPrimitiveRecursiveAuthority
  field
    substituteX0CodePR :
      Set
    substituteX0CodePRWitness : substituteX0CodePR

    selfSubstitutionPR :
      PR.PrimitiveRecursiveUnary concreteSelfSubstituteCode

open ConcreteSubstitutionPrimitiveRecursiveAuthority public

------------------------------------------------------------------------
-- Same-code transport into the generic diagonal producer.
------------------------------------------------------------------------

record SameCodeSelfSubstitutionWeld
    (F : Set₁)
    (AbstractSelfSubstitute : Nat → Nat) : Set₁ where
  constructor sameCodeSelfSubstitutionWeld
  field
    concreteEqualsAbstract :
      (n : Nat) → concreteSelfSubstituteCode n ≡ AbstractSelfSubstitute n

open SameCodeSelfSubstitutionWeld public

transportPrimitiveRecursiveAlongSameCode :
  (abstractSelf : Nat → Nat) →
  ConcreteSubstitutionPrimitiveRecursiveAuthority →
  ((n : Nat) → concreteSelfSubstituteCode n ≡ abstractSelf n) →
  PR.PrimitiveRecursiveUnary abstractSelf
transportPrimitiveRecursiveAlongSameCode abstractSelf authority sameCode =
  PR.primitiveRecursiveUnary
    ((PR.Certificate (selfSubstitutionPR authority)) ×
      ((n : Nat) → concreteSelfSubstituteCode n ≡ abstractSelf n))
    ((PR.certificate (selfSubstitutionPR authority)) , sameCode)

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data TotalDecoderImpliesPrimitiveRecursiveDecoder : Set where
data StructuralSubstitutionImpliesPRSubstitution : Set where
data DifferentGodelCodeTransfersPRCertificate : Set where

totalityDoesNotProvePrimitiveRecursiveness :
  TotalDecoderImpliesPrimitiveRecursiveDecoder → ⊥
totalityDoesNotProvePrimitiveRecursiveness ()

structuralDefinitionDoesNotSelfCertifyPR :
  StructuralSubstitutionImpliesPRSubstitution → ⊥
structuralDefinitionDoesNotSelfCertifyPR ()

differentCodeDoesNotTransportWithoutWeld :
  DifferentGodelCodeTransfersPRCertificate → ⊥
differentCodeDoesNotTransportWithoutWeld ()

record GodelBase12SelfSubstitutionPRBoundary : Set where
  constructor godelBase12SelfSubstitutionPRBoundary
  field
    concreteSelfSubstitutionFunctionOwned : Bool
    fixedBaseArithmeticPRPaymentsOwned : Bool
    concreteSubstitutionPRAuthorityOwned : Bool
    sameCodeTransportCompilerOwned : Bool
    totalityPromotedToPrimitiveRecursiveness : Bool
    localSelfSubstitutionPRLeafClosed : Bool

canonicalGodelBase12SelfSubstitutionPRBoundary :
  GodelBase12SelfSubstitutionPRBoundary
canonicalGodelBase12SelfSubstitutionPRBoundary =
  godelBase12SelfSubstitutionPRBoundary
    true false false true false false
