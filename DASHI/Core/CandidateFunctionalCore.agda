module DASHI.Core.CandidateFunctionalCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Core.GenericReceipt as Generic

------------------------------------------------------------------------
-- Candidate functional vocabulary.
--
-- This core generalizes Hamiltonian-shaped candidate surfaces to the
-- wider family of scalar/function-shaped readings used by receipts.  It
-- records term grammar and authority boundaries only; it does not define
-- numeric evaluation, optimization, minimization, spectrum, clinical
-- safety, physical law, or metaphysical authority.

data FunctionalKind : Set where
  HamiltonianLike :
    FunctionalKind

  EnergyLike :
    FunctionalKind

  CostLike :
    FunctionalKind

  RiskLike :
    FunctionalKind

  ScoreLike :
    FunctionalKind

  LossLike :
    FunctionalKind

  UtilityLike :
    FunctionalKind

  StrainLike :
    FunctionalKind

  PressureLike :
    FunctionalKind

  HarmLike :
    FunctionalKind

  RenewalLike :
    FunctionalKind

  NamedFunctionalKind :
    String →
    FunctionalKind

data TermPolarity : Set where
  positiveStrainPolarity :
    TermPolarity

  negativeSupportPolarity :
    TermPolarity

  negativeCreditPolarity :
    TermPolarity

  neutralPolarity :
    TermPolarity

data TermSign : Set where
  positiveSign :
    TermSign

  negativeSign :
    TermSign

  neutralSign :
    TermSign

  symbolicSign :
    TermSign

data SymbolicWeight : Set where
  unitSymbolicWeight :
    SymbolicWeight

  strainSymbolicWeight :
    SymbolicWeight

  supportSymbolicWeight :
    SymbolicWeight

  creditSymbolicWeight :
    SymbolicWeight

  neutralSymbolicWeight :
    SymbolicWeight

  namedSymbolicWeight :
    String →
    SymbolicWeight

data CandidateAggregation : Set where
  candidateSymbolicSum :
    CandidateAggregation

  candidateWeightedSymbolicSum :
    CandidateAggregation

  candidateSignedBalance :
    CandidateAggregation

  candidateTermCatalogue :
    CandidateAggregation

  namedCandidateAggregation :
    String →
    CandidateAggregation

record FunctionalTerm : Set where
  constructor functionalTerm
  field
    termLabel :
      String

    termPolarity :
      TermPolarity

    termSign :
      TermSign

    termWeight :
      SymbolicWeight

open FunctionalTerm public

positiveStrainTerm :
  String →
  SymbolicWeight →
  FunctionalTerm
positiveStrainTerm label weight =
  functionalTerm label positiveStrainPolarity positiveSign weight

negativeSupportTerm :
  String →
  SymbolicWeight →
  FunctionalTerm
negativeSupportTerm label weight =
  functionalTerm label negativeSupportPolarity negativeSign weight

negativeCreditTerm :
  String →
  SymbolicWeight →
  FunctionalTerm
negativeCreditTerm label weight =
  functionalTerm label negativeCreditPolarity negativeSign weight

neutralFunctionalTerm :
  String →
  SymbolicWeight →
  FunctionalTerm
neutralFunctionalTerm label weight =
  functionalTerm label neutralPolarity neutralSign weight

------------------------------------------------------------------------
-- Candidate functional surface.

record CandidateFunctionalSurface : Set where
  constructor candidateFunctionalSurface
  field
    carrierLabel :
      String

    stateLabel :
      String

    functionalKind :
      FunctionalKind

    canonicalTerms :
      List FunctionalTerm

    canonicalAggregation :
      CandidateAggregation

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    numericAuthority :
      Bool

    numericAuthorityIsFalse :
      numericAuthority ≡ false

    optimizationAuthority :
      Bool

    optimizationAuthorityIsFalse :
      optimizationAuthority ≡ false

    minimizationAuthority :
      Bool

    minimizationAuthorityIsFalse :
      minimizationAuthority ≡ false

    spectralAuthority :
      Bool

    spectralAuthorityIsFalse :
      spectralAuthority ≡ false

    clinicalAuthority :
      Bool

    clinicalAuthorityIsFalse :
      clinicalAuthority ≡ false

    physicalAuthority :
      Bool

    physicalAuthorityIsFalse :
      physicalAuthority ≡ false

    metaphysicalAuthority :
      Bool

    metaphysicalAuthorityIsFalse :
      metaphysicalAuthority ≡ false

open CandidateFunctionalSurface public

------------------------------------------------------------------------
-- Canonical meditation-like candidate surface.

agitationStrainFunctionalTerm :
  FunctionalTerm
agitationStrainFunctionalTerm =
  positiveStrainTerm "agitation strain" strainSymbolicWeight

dullnessStrainFunctionalTerm :
  FunctionalTerm
dullnessStrainFunctionalTerm =
  positiveStrainTerm "dullness strain" strainSymbolicWeight

ruminationStrainFunctionalTerm :
  FunctionalTerm
ruminationStrainFunctionalTerm =
  positiveStrainTerm "rumination strain" strainSymbolicWeight

avoidanceStrainFunctionalTerm :
  FunctionalTerm
avoidanceStrainFunctionalTerm =
  positiveStrainTerm "avoidance strain" strainSymbolicWeight

clarityCreditFunctionalTerm :
  FunctionalTerm
clarityCreditFunctionalTerm =
  negativeCreditTerm "clarity credit" creditSymbolicWeight

embodimentCreditFunctionalTerm :
  FunctionalTerm
embodimentCreditFunctionalTerm =
  negativeCreditTerm "embodiment credit" creditSymbolicWeight

equanimitySupportFunctionalTerm :
  FunctionalTerm
equanimitySupportFunctionalTerm =
  negativeSupportTerm "equanimity support" supportSymbolicWeight

compassionSupportFunctionalTerm :
  FunctionalTerm
compassionSupportFunctionalTerm =
  negativeSupportTerm "compassion support" supportSymbolicWeight

openAwarenessNeutralFunctionalTerm :
  FunctionalTerm
openAwarenessNeutralFunctionalTerm =
  neutralFunctionalTerm "open awareness neutral term" neutralSymbolicWeight

renewalCreditFunctionalTerm :
  FunctionalTerm
renewalCreditFunctionalTerm =
  negativeCreditTerm "renewal credit" creditSymbolicWeight

canonicalMeditationLikeFunctionalTerms :
  List FunctionalTerm
canonicalMeditationLikeFunctionalTerms =
  agitationStrainFunctionalTerm
  ∷ dullnessStrainFunctionalTerm
  ∷ ruminationStrainFunctionalTerm
  ∷ avoidanceStrainFunctionalTerm
  ∷ clarityCreditFunctionalTerm
  ∷ embodimentCreditFunctionalTerm
  ∷ equanimitySupportFunctionalTerm
  ∷ compassionSupportFunctionalTerm
  ∷ openAwarenessNeutralFunctionalTerm
  ∷ renewalCreditFunctionalTerm
  ∷ []

canonicalMeditationLikeFunctionalSurface :
  CandidateFunctionalSurface
canonicalMeditationLikeFunctionalSurface =
  candidateFunctionalSurface
    "mind carrier"
    "meditation state"
    RenewalLike
    canonicalMeditationLikeFunctionalTerms
    candidateWeightedSymbolicSum
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl

canonicalMeditationLikeFunctionalSurfaceCandidateOnly :
  candidateOnly canonicalMeditationLikeFunctionalSurface ≡ true
canonicalMeditationLikeFunctionalSurfaceCandidateOnly =
  refl

canonicalMeditationLikeFunctionalSurfaceNumericAuthorityFalse :
  numericAuthority canonicalMeditationLikeFunctionalSurface ≡ false
canonicalMeditationLikeFunctionalSurfaceNumericAuthorityFalse =
  refl

canonicalMeditationLikeFunctionalSurfaceOptimizationAuthorityFalse :
  optimizationAuthority canonicalMeditationLikeFunctionalSurface ≡ false
canonicalMeditationLikeFunctionalSurfaceOptimizationAuthorityFalse =
  refl

canonicalMeditationLikeFunctionalSurfaceMinimizationAuthorityFalse :
  minimizationAuthority canonicalMeditationLikeFunctionalSurface ≡ false
canonicalMeditationLikeFunctionalSurfaceMinimizationAuthorityFalse =
  refl

canonicalMeditationLikeFunctionalSurfaceSpectralAuthorityFalse :
  spectralAuthority canonicalMeditationLikeFunctionalSurface ≡ false
canonicalMeditationLikeFunctionalSurfaceSpectralAuthorityFalse =
  refl

canonicalMeditationLikeFunctionalSurfaceClinicalAuthorityFalse :
  clinicalAuthority canonicalMeditationLikeFunctionalSurface ≡ false
canonicalMeditationLikeFunctionalSurfaceClinicalAuthorityFalse =
  refl

canonicalMeditationLikeFunctionalSurfacePhysicalAuthorityFalse :
  physicalAuthority canonicalMeditationLikeFunctionalSurface ≡ false
canonicalMeditationLikeFunctionalSurfacePhysicalAuthorityFalse =
  refl

canonicalMeditationLikeFunctionalSurfaceMetaphysicalAuthorityFalse :
  metaphysicalAuthority canonicalMeditationLikeFunctionalSurface ≡ false
canonicalMeditationLikeFunctionalSurfaceMetaphysicalAuthorityFalse =
  refl

------------------------------------------------------------------------
-- Generic receipt adapter.

candidateFunctionalSurfaceGenericReceipt :
  CandidateFunctionalSurface →
  Generic.GenericReceipt
candidateFunctionalSurfaceGenericReceipt surface =
  Generic.mkNonPromotingReceipt
    "candidate functional surface"
    "DASHI.Core.CandidateFunctionalCore"
    "CandidateFunctionalSurface"
    "candidate scalar/function-shaped surface records kind, terms, aggregation, and fail-closed authority bits"
    "numeric evaluation, optimization, minimization, spectral, clinical, physical, and metaphysical authority remain outside this core"
    "agda -i . DASHI/Core/CandidateFunctionalCore.agda"

canonicalMeditationLikeFunctionalSurfaceGenericReceipt :
  Generic.GenericReceipt
canonicalMeditationLikeFunctionalSurfaceGenericReceipt =
  candidateFunctionalSurfaceGenericReceipt
    canonicalMeditationLikeFunctionalSurface

canonicalMeditationLikeFunctionalSurfaceGenericReceiptNonPromoting :
  Generic.promotesClaim
    canonicalMeditationLikeFunctionalSurfaceGenericReceipt
  ≡
  false
canonicalMeditationLikeFunctionalSurfaceGenericReceiptNonPromoting =
  refl
