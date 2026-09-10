module DASHI.ComputerScience.GodelBase12SelfSubstitutionPRFrontierExact where

open import DASHI.Core.Prelude
open import Data.Nat.DivMod using (_/_; _%_)

import DASHI.ComputerScience.GodelArithmeticRawSyntaxExact as Syntax
import DASHI.ComputerScience.GodelArithmeticDeBruijnInstantiationExact as Inst
import DASHI.ComputerScience.GodelArithmeticBase12NatRetractionExact as NatCodec
import DASHI.ComputerScience.GodelPrimitiveRecursiveRepresentabilityBridgeExact as PR

------------------------------------------------------------------------
-- SAME-CODE PRIMITIVE-RECURSIVE FRONTIER FOR THE CONCRETE BASE-12 CODE
------------------------------------------------------------------------

record Base12PrimitiveRecursivePayments
    (PRT : PR.PrimitiveRecursiveTheory) : Set₁ where
  constructor base12PrimitiveRecursivePayments
  field
    fixedBase12RemainderPR :
      PR.PrimitiveRecursiveUnary PRT (λ n → n % 12)
    fixedBase12QuotientPR :
      PR.PrimitiveRecursiveUnary PRT (λ n → n / 12)

    formulaDecoderCodePR :
      PR.PrimitiveRecursiveUnary PRT
        (λ n → NatCodec.encodeFormulaNat (NatCodec.decodeFormulaNat n))

    numeralEncodingPR :
      PR.PrimitiveRecursiveUnary PRT
        (λ n → NatCodec.encodeFormulaNat
          (Syntax.equalFormula (Inst.numeralTerm n) (Inst.numeralTerm n)))

open Base12PrimitiveRecursivePayments public

------------------------------------------------------------------------
-- Exact concrete meta-level code substitution.
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
-- Repo-specific PR payment under one explicit PR authority.
------------------------------------------------------------------------

record ConcreteSubstitutionPrimitiveRecursivePayment
    (PRT : PR.PrimitiveRecursiveTheory) : Set₁ where
  constructor concreteSubstitutionPrimitiveRecursivePayment
  field
    prerequisitePayments : Base12PrimitiveRecursivePayments PRT
    selfSubstitutionPR :
      PR.PrimitiveRecursiveUnary PRT concreteSelfSubstituteCode

open ConcreteSubstitutionPrimitiveRecursivePayment public

------------------------------------------------------------------------
-- Same-code transport.  Pointwise equality alone is not used as an implicit
-- coercion; the SAME PR theory must provide its extensionality authority.
------------------------------------------------------------------------

transportPrimitiveRecursiveAlongSameCode :
  (PRT : PR.PrimitiveRecursiveTheory) →
  PR.PrimitiveRecursiveExtensionalityAuthority PRT →
  (abstractSelf : Nat → Nat) →
  ConcreteSubstitutionPrimitiveRecursivePayment PRT →
  ((n : Nat) → concreteSelfSubstituteCode n ≡ abstractSelf n) →
  PR.PrimitiveRecursiveUnary PRT abstractSelf
transportPrimitiveRecursiveAlongSameCode
  PRT extensionality abstractSelf payment sameCode =
  PR.transportAlongPointwiseEquality extensionality
    concreteSelfSubstituteCode
    abstractSelf
    sameCode
    (selfSubstitutionPR payment)

------------------------------------------------------------------------
-- Compiler into the generic self-substitution PR producer.
------------------------------------------------------------------------

record SameCodeFormalSubstitutionWeld
    (F : Set₁)
    (abstractSelf : Nat → Nat) : Set₁ where
  constructor sameCodeFormalSubstitutionWeld
  field
    sameCode : (n : Nat) → concreteSelfSubstituteCode n ≡ abstractSelf n

open SameCodeFormalSubstitutionWeld public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data TotalDecoderImpliesPrimitiveRecursiveDecoder : Set where
data StructuralSubstitutionImpliesPRSubstitution : Set where
data DifferentGodelCodeTransfersPRCertificate : Set where
data PointwiseEqualitySilentlyTransfersPRAuthority : Set where

totalityDoesNotProvePrimitiveRecursiveness :
  TotalDecoderImpliesPrimitiveRecursiveDecoder → ⊥
totalityDoesNotProvePrimitiveRecursiveness ()

structuralDefinitionDoesNotSelfCertifyPR :
  StructuralSubstitutionImpliesPRSubstitution → ⊥
structuralDefinitionDoesNotSelfCertifyPR ()

differentCodeDoesNotTransportWithoutWeld :
  DifferentGodelCodeTransfersPRCertificate → ⊥
differentCodeDoesNotTransportWithoutWeld ()

pointwiseEqualityNeedsPRAuthority :
  PointwiseEqualitySilentlyTransfersPRAuthority → ⊥
pointwiseEqualityNeedsPRAuthority ()

record GodelBase12SelfSubstitutionPRBoundary : Set where
  constructor godelBase12SelfSubstitutionPRBoundary
  field
    concreteSelfSubstitutionFunctionOwned : Bool
    authorityIndexedPrerequisiteShapeOwned : Bool
    concreteSelfSubstitutionPRPaymentOwned : Bool
    sameCodeTransportCompilerOwned : Bool
    totalityPromotedToPrimitiveRecursiveness : Bool
    localSelfSubstitutionPRLeafClosed : Bool

canonicalGodelBase12SelfSubstitutionPRBoundary :
  GodelBase12SelfSubstitutionPRBoundary
canonicalGodelBase12SelfSubstitutionPRBoundary =
  godelBase12SelfSubstitutionPRBoundary
    true true false true false false
