module DASHI.Empirical.GRQuantumKnownLimitRecovery where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Algebra.Quantum.FiniteTreeWeyl as Tree
import DASHI.Algebra.Quantum.FiniteQutritBornAdditivity as Born
import DASHI.Physics.Closure.PropositionEinsteinBridge as Einstein

------------------------------------------------------------------------
-- Named accepted-limit targets.  A finite consistency model is not identified
-- with a physical low-energy or continuum limit.

data AcceptedLimit : Set where
  flatSpecialRelativity : AcceptedLimit
  newtonianWeakFieldGravity : AcceptedLimit
  vacuumEinsteinEquation : AcceptedLimit
  bornProbabilityRule : AcceptedLimit
  freeFieldHeisenbergCCR : AcceptedLimit
  qftOnCurvedSpacetime : AcceptedLimit

record LimitRecoveryCase (kind : AcceptedLimit) : Set₁ where
  field
    FormalRegime : Set
    DASHIState : Set
    ReferenceState : Set
    Observable : Set

    enterRegime : DASHIState → FormalRegime
    dashiObservable : DASHIState → Observable
    referenceObservable : ReferenceState → Observable

    ComparisonInput : Set
    dashiCase : ComparisonInput → DASHIState
    referenceCase : ComparisonInput → ReferenceState

    agreesInDeclaredLimit :
      (input : ComparisonInput) →
      dashiObservable (dashiCase input)
      ≡ referenceObservable (referenceCase input)

    assumptions : List String
    referenceTheory : String
    referenceVersion : String
    convergenceOrAsymptoticAuthority : Set
    convergenceOrAsymptoticAuthorityProof :
      convergenceOrAsymptoticAuthority
open LimitRecoveryCase public

record AcceptedGRQFTLimitSuite : Set₁ where
  field
    specialRelativity : LimitRecoveryCase flatSpecialRelativity
    newtonianGravity : LimitRecoveryCase newtonianWeakFieldGravity
    vacuumEinstein : LimitRecoveryCase vacuumEinsteinEquation
    bornRule : LimitRecoveryCase bornProbabilityRule
    heisenbergCCR : LimitRecoveryCase freeFieldHeisenbergCCR
    curvedSpacetimeQFT : LimitRecoveryCase qftOnCurvedSpacetime

    oneParameterSetAcrossLimits : Set
    oneParameterSetAcrossLimitsProof : oneParameterSetAcrossLimits
    noLimitFittedOnItsEvaluationData : Set
    noLimitFittedOnItsEvaluationDataProof : noLimitFittedOnItsEvaluationData
    uncertaintyAndDiscretisationErrorsPropagated : Set
    uncertaintyAndDiscretisationErrorsPropagatedProof :
      uncertaintyAndDiscretisationErrorsPropagated
open AcceptedGRQFTLimitSuite public

------------------------------------------------------------------------
-- Exact finite/model evidence already in the repository.
--
-- These fields are useful regression adapters.  They do not inhabit the accepted
-- physical suite because they contain no continuum/scaling or measured authority.

record ExistingFiniteLimitAdapters : Set where
  constructor existing-finite-limit-adapters
  field
    flatEinsteinProducer : Einstein.ExactFlatEinsteinProducer
    finiteBornReceipt : Tree.FiniteBornReceipt
    finiteBornAdditivity : Born.FiniteQutritBornAdditivityReceipt
    scope : String
open ExistingFiniteLimitAdapters public

canonicalExistingFiniteLimitAdapters : ExistingFiniteLimitAdapters
canonicalExistingFiniteLimitAdapters =
  existing-finite-limit-adapters
    Einstein.canonicalExactFlatEinsteinProducer
    Tree.canonicalFiniteBornReceipt
    Born.canonicalFiniteQutritBornAdditivityReceipt
    "exact flat and finite qutrit adapters only; no accepted continuum GR/QFT limit is inferred"

record KnownLimitBoundary : Set where
  constructor known-limit-boundary
  field
    acceptedLimitInterfaceImplemented : Bool
    acceptedLimitInterfaceImplementedIsTrue :
      acceptedLimitInterfaceImplemented ≡ true
    finiteReferenceAdaptersImplemented : Bool
    finiteReferenceAdaptersImplementedIsTrue :
      finiteReferenceAdaptersImplemented ≡ true
    acceptedPhysicalLimitSuiteCompleted : Bool
    acceptedPhysicalLimitSuiteCompletedIsFalse :
      acceptedPhysicalLimitSuiteCompleted ≡ false
    finiteCCRIdentifiedWithHeisenbergRepresentation : Bool
    finiteCCRIdentifiedWithHeisenbergRepresentationIsFalse :
      finiteCCRIdentifiedWithHeisenbergRepresentation ≡ false
open KnownLimitBoundary public

canonicalKnownLimitBoundary : KnownLimitBoundary
canonicalKnownLimitBoundary =
  known-limit-boundary true refl true refl false refl false refl
