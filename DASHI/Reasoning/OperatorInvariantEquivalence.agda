module DASHI.Reasoning.OperatorInvariantEquivalence where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Cross-domain operator/topology equivalence with explicit invariants.
--
-- This module records the thread delta:
--
--   cross-domain situations may instantiate the same abstract operator /
--   topology class only under an explicit invariant family.
--
-- The surface is intentionally theorem-thin.  It is a typed vocabulary and
-- non-promotion boundary, not a global ontology, not substance identity, not
-- untyped exact equivalence, and not universal reducibility.

data SituationDomain : Set where
  debateDomain :
    SituationDomain

  redoxDomain :
    SituationDomain

  marketDomain :
    SituationDomain

  immuneDomain :
    SituationDomain

  warDomain :
    SituationDomain

  predatorPreyDomain :
    SituationDomain

  signalAmplificationDomain :
    SituationDomain

  rendererTransportDomain :
    SituationDomain

data InvariantFamilyKind : Set where
  transferInvariant :
    InvariantFamilyKind

  gradientInvariant :
    InvariantFamilyKind

  stabilizationInvariant :
    InvariantFamilyKind

  escalationInvariant :
    InvariantFamilyKind

  equilibriumInvariant :
    InvariantFamilyKind

  catalyticAmplificationInvariant :
    InvariantFamilyKind

  repairSynthesisInvariant :
    InvariantFamilyKind

data EquivalenceStrength : Set where
  exactEquivalence :
    EquivalenceStrength

  partialEquivalence :
    EquivalenceStrength

  misleadingEquivalence :
    EquivalenceStrength

  blockedEquivalence :
    EquivalenceStrength

data OperatorInvariantGuard : Set where
  noGlobalOntology :
    OperatorInvariantGuard

  noSubstanceIdentity :
    OperatorInvariantGuard

  noUntypedExactEquivalence :
    OperatorInvariantGuard

  noUniversalReducibility :
    OperatorInvariantGuard

canonicalOperatorInvariantGuards :
  List OperatorInvariantGuard
canonicalOperatorInvariantGuards =
  noGlobalOntology
  ∷ noSubstanceIdentity
  ∷ noUntypedExactEquivalence
  ∷ noUniversalReducibility
  ∷ []

canonicalSituationDomains :
  List SituationDomain
canonicalSituationDomains =
  debateDomain
  ∷ redoxDomain
  ∷ marketDomain
  ∷ immuneDomain
  ∷ warDomain
  ∷ predatorPreyDomain
  ∷ signalAmplificationDomain
  ∷ rendererTransportDomain
  ∷ []

canonicalInvariantFamilies :
  List InvariantFamilyKind
canonicalInvariantFamilies =
  transferInvariant
  ∷ gradientInvariant
  ∷ stabilizationInvariant
  ∷ escalationInvariant
  ∷ equilibriumInvariant
  ∷ catalyticAmplificationInvariant
  ∷ repairSynthesisInvariant
  ∷ []

record AbstractOperatorTopologyClass : Set₁ where
  field
    Situation :
      Set

    Operator :
      Set

    Topology :
      Set

    domain :
      SituationDomain

    operatorOf :
      Situation →
      Operator

    topologyOf :
      Situation →
      Topology

    operatorClassName :
      String

    topologyClassName :
      String

    classBoundary :
      String

open AbstractOperatorTopologyClass public

record ExplicitInvariantFamily
    (C : AbstractOperatorTopologyClass) : Set₁ where
  field
    Invariant :
      Set

    invariantFamilies :
      List InvariantFamilyKind

    invariantHolds :
      Situation C →
      Invariant →
      Set

    invariantReading :
      Invariant →
      String

    explicitFamilyBoundary :
      String

open ExplicitInvariantFamily public

record CrossDomainInvariantInstantiation : Set₁ where
  field
    leftClass :
      AbstractOperatorTopologyClass

    rightClass :
      AbstractOperatorTopologyClass

    leftInvariantFamily :
      ExplicitInvariantFamily leftClass

    rightInvariantFamily :
      ExplicitInvariantFamily rightClass

    selectedFamilies :
      List InvariantFamilyKind

    leftSituation :
      Situation leftClass

    rightSituation :
      Situation rightClass

    sameAbstractClassUnderSelectedInvariants :
      Set

    strength :
      EquivalenceStrength

    strengthReading :
      String

    invariantBoundary :
      String

open CrossDomainInvariantInstantiation public

record ReceiptGatedExactness
    (instantiation : CrossDomainInvariantInstantiation) : Set₁ where
  field
    ExactReceipt :
      Set

    receiptStrength :
      ExactReceipt →
      EquivalenceStrength

    receiptStrengthIsExact :
      (receipt : ExactReceipt) →
      receiptStrength receipt ≡ exactEquivalence

    exactOnlyUnderSelectedInvariants :
      ExactReceipt →
      sameAbstractClassUnderSelectedInvariants instantiation

    receiptBoundary :
      String

open ReceiptGatedExactness public

record OperatorInvariantNonPromotionBoundary : Set where
  field
    guards :
      List OperatorInvariantGuard

    guardsAreCanonical :
      guards ≡ canonicalOperatorInvariantGuards

    globalOntologyClaim :
      Bool

    globalOntologyClaimIsFalse :
      globalOntologyClaim ≡ false

    substanceIdentityClaim :
      Bool

    substanceIdentityClaimIsFalse :
      substanceIdentityClaim ≡ false

    untypedExactEquivalenceClaim :
      Bool

    untypedExactEquivalenceClaimIsFalse :
      untypedExactEquivalenceClaim ≡ false

    universalReducibilityClaim :
      Bool

    universalReducibilityClaimIsFalse :
      universalReducibilityClaim ≡ false

    boundaryReading :
      String

open OperatorInvariantNonPromotionBoundary public

canonicalOperatorInvariantNonPromotionBoundary :
  OperatorInvariantNonPromotionBoundary
canonicalOperatorInvariantNonPromotionBoundary =
  record
    { guards =
        canonicalOperatorInvariantGuards
    ; guardsAreCanonical =
        refl
    ; globalOntologyClaim =
        false
    ; globalOntologyClaimIsFalse =
        refl
    ; substanceIdentityClaim =
        false
    ; substanceIdentityClaimIsFalse =
        refl
    ; untypedExactEquivalenceClaim =
        false
    ; untypedExactEquivalenceClaimIsFalse =
        refl
    ; universalReducibilityClaim =
        false
    ; universalReducibilityClaimIsFalse =
        refl
    ; boundaryReading =
        "Cross-domain equivalence is invariant-family scoped and non-promoting."
    }

------------------------------------------------------------------------
-- Canonical toy inhabitants: debate / redox.

data ToyDebateRedoxSituation : Set where
  toyDebateSituation :
    ToyDebateRedoxSituation

  toyRedoxSituation :
    ToyDebateRedoxSituation

data ToyOperator : Set where
  toyTransferOperator :
    ToyOperator

  toyGradientOperator :
    ToyOperator

  toyStabilizationOperator :
    ToyOperator

data ToyTopology : Set where
  toyCoupledTopology :
    ToyTopology

  toyEscalatingTopology :
    ToyTopology

data ToyInvariant : Set where
  toyTransferInvariant :
    ToyInvariant

  toyGradientInvariant :
    ToyInvariant

  toyStabilizationInvariant :
    ToyInvariant

data ToyExactReceipt : Set where
  debateRedoxSelectedInvariantReceipt :
    ToyExactReceipt

toyOperatorOf :
  ToyDebateRedoxSituation →
  ToyOperator
toyOperatorOf toyDebateSituation =
  toyTransferOperator
toyOperatorOf toyRedoxSituation =
  toyTransferOperator

toyTopologyOf :
  ToyDebateRedoxSituation →
  ToyTopology
toyTopologyOf toyDebateSituation =
  toyCoupledTopology
toyTopologyOf toyRedoxSituation =
  toyCoupledTopology

toyDebateClass :
  AbstractOperatorTopologyClass
toyDebateClass =
  record
    { Situation =
        ToyDebateRedoxSituation
    ; Operator =
        ToyOperator
    ; Topology =
        ToyTopology
    ; domain =
        debateDomain
    ; operatorOf =
        toyOperatorOf
    ; topologyOf =
        toyTopologyOf
    ; operatorClassName =
        "transfer-gradient-stabilization"
    ; topologyClassName =
        "coupled response topology"
    ; classBoundary =
        "debate is represented only by a selected operator/topology class"
    }

toyRedoxClass :
  AbstractOperatorTopologyClass
toyRedoxClass =
  record
    { Situation =
        ToyDebateRedoxSituation
    ; Operator =
        ToyOperator
    ; Topology =
        ToyTopology
    ; domain =
        redoxDomain
    ; operatorOf =
        toyOperatorOf
    ; topologyOf =
        toyTopologyOf
    ; operatorClassName =
        "transfer-gradient-stabilization"
    ; topologyClassName =
        "coupled response topology"
    ; classBoundary =
        "redox is represented only by a selected operator/topology class"
    }

toyInvariantFamily :
  (C : AbstractOperatorTopologyClass) →
  ExplicitInvariantFamily C
toyInvariantFamily C =
  record
    { Invariant =
        ToyInvariant
    ; invariantFamilies =
        transferInvariant
        ∷ gradientInvariant
        ∷ stabilizationInvariant
        ∷ []
    ; invariantHolds =
        λ _ _ → ⊤
    ; invariantReading =
        toyInvariantReading
    ; explicitFamilyBoundary =
        "only transfer, gradient, and stabilization are selected in this toy family"
    }
  where
    toyInvariantReading :
      ToyInvariant →
      String
    toyInvariantReading toyTransferInvariant =
      "selected transfer invariant"
    toyInvariantReading toyGradientInvariant =
      "selected gradient invariant"
    toyInvariantReading toyStabilizationInvariant =
      "selected stabilization invariant"

toyDebateRedoxPartialInstantiation :
  CrossDomainInvariantInstantiation
toyDebateRedoxPartialInstantiation =
  record
    { leftClass =
        toyDebateClass
    ; rightClass =
        toyRedoxClass
    ; leftInvariantFamily =
        toyInvariantFamily toyDebateClass
    ; rightInvariantFamily =
        toyInvariantFamily toyRedoxClass
    ; selectedFamilies =
        transferInvariant
        ∷ gradientInvariant
        ∷ stabilizationInvariant
        ∷ []
    ; leftSituation =
        toyDebateSituation
    ; rightSituation =
        toyRedoxSituation
    ; sameAbstractClassUnderSelectedInvariants =
        ⊤
    ; strength =
        partialEquivalence
    ; strengthReading =
        "debate/redox share a selected abstract transfer-gradient-stabilization class only partially"
    ; invariantBoundary =
        "partial means selected invariants line up, not substances or all dynamics"
    }

toyDebateRedoxExactUnderReceiptInstantiation :
  CrossDomainInvariantInstantiation
toyDebateRedoxExactUnderReceiptInstantiation =
  record
    { leftClass =
        toyDebateClass
    ; rightClass =
        toyRedoxClass
    ; leftInvariantFamily =
        toyInvariantFamily toyDebateClass
    ; rightInvariantFamily =
        toyInvariantFamily toyRedoxClass
    ; selectedFamilies =
        transferInvariant
        ∷ gradientInvariant
        ∷ stabilizationInvariant
        ∷ []
    ; leftSituation =
        toyDebateSituation
    ; rightSituation =
        toyRedoxSituation
    ; sameAbstractClassUnderSelectedInvariants =
        ⊤
    ; strength =
        exactEquivalence
    ; strengthReading =
        "exact only after the selected invariant family receipt is supplied"
    ; invariantBoundary =
        "exactness is receipt-gated and scoped to the selected invariant family"
    }

toyDebateRedoxReceiptGatedExactness :
  ReceiptGatedExactness toyDebateRedoxExactUnderReceiptInstantiation
toyDebateRedoxReceiptGatedExactness =
  record
    { ExactReceipt =
        ToyExactReceipt
    ; receiptStrength =
        λ _ → exactEquivalence
    ; receiptStrengthIsExact =
        λ _ → refl
    ; exactOnlyUnderSelectedInvariants =
        λ _ → tt
    ; receiptBoundary =
        "the receipt gates exactness; without it the canonical toy reading remains partial"
    }
