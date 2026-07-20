module DASHI.Geometry.AdmissibilityJetSpec where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Typed admissibility specification for a kernel depth.
--
-- This module records the dictionary:
--   redundancy / pseudogroup
--   field carrier
--   finite jet order
--   invariant-generator discipline
--   MDL preference for the smallest admissible local basis
--
-- It is a structural carrier.  It does not claim that selecting a row proves
-- Einstein, Yang--Mills, Dirac, or any other physical theory.


data RedundancyKind : Set where
  noRedundancy : RedundancyKind
  diffeomorphismRedundancy : RedundancyKind
  abelianGaugeRedundancy : RedundancyKind
  nonAbelianGaugeRedundancy : RedundancyKind
  spinLiftRedundancy : RedundancyKind

redundancyName : RedundancyKind → String
redundancyName noRedundancy = "no-redundancy"
redundancyName diffeomorphismRedundancy = "diffeomorphism-redundancy"
redundancyName abelianGaugeRedundancy = "abelian-gauge-redundancy"
redundancyName nonAbelianGaugeRedundancy = "non-abelian-gauge-redundancy"
redundancyName spinLiftRedundancy = "spin-lift-redundancy"


data FieldCarrierKind : Set where
  scalarCarrier : FieldCarrierKind
  metricCarrier : FieldCarrierKind
  oneFormCarrier : FieldCarrierKind
  principalConnectionCarrier : FieldCarrierKind
  tensorCarrier : FieldCarrierKind
  bitensorCarrier : FieldCarrierKind
  spinorCarrier : FieldCarrierKind

fieldCarrierName : FieldCarrierKind → String
fieldCarrierName scalarCarrier = "scalar-carrier"
fieldCarrierName metricCarrier = "metric-carrier"
fieldCarrierName oneFormCarrier = "one-form-carrier"
fieldCarrierName principalConnectionCarrier = "principal-connection-carrier"
fieldCarrierName tensorCarrier = "tensor-carrier"
fieldCarrierName bitensorCarrier = "bitensor-carrier"
fieldCarrierName spinorCarrier = "spinor-carrier"


data InvariantGeneratorKind : Set where
  scalarInvariantGenerator : InvariantGeneratorKind
  curvatureInvariantGenerator : InvariantGeneratorKind
  fieldStrengthInvariantGenerator : InvariantGeneratorKind
  covariantDerivativeInvariantGenerator : InvariantGeneratorKind
  twoPointInvariantGenerator : InvariantGeneratorKind
  CartanInvariantGenerator : InvariantGeneratorKind
  DiracInvariantGenerator : InvariantGeneratorKind

invariantGeneratorName : InvariantGeneratorKind → String
invariantGeneratorName scalarInvariantGenerator = "scalar-invariant-generator"
invariantGeneratorName curvatureInvariantGenerator = "curvature-invariant-generator"
invariantGeneratorName fieldStrengthInvariantGenerator = "field-strength-invariant-generator"
invariantGeneratorName covariantDerivativeInvariantGenerator = "covariant-derivative-invariant-generator"
invariantGeneratorName twoPointInvariantGenerator = "two-point-invariant-generator"
invariantGeneratorName CartanInvariantGenerator = "cartan-invariant-generator"
invariantGeneratorName DiracInvariantGenerator = "dirac-invariant-generator"

record DepthAdmissibilitySpec : Set where
  constructor mkDepthAdmissibilitySpec
  field
    depthLabel : String
    redundancy : RedundancyKind
    fieldCarrier : FieldCarrierKind
    jetOrder : Nat
    invariantGenerators : List InvariantGeneratorKind
    localityRequired : Bool
    finiteJetRequired : Bool
    quotientFirst : Bool
    mdlPrefersLowerJetOrder : Bool
    physicalDerivationClaimed : Bool
    scopeStatement : String

open DepthAdmissibilitySpec public

metricDiffeomorphismTwoJetSpec : DepthAdmissibilitySpec
metricDiffeomorphismTwoJetSpec =
  mkDepthAdmissibilitySpec
    "metric-diffeomorphism-two-jet"
    diffeomorphismRedundancy
    metricCarrier
    (suc (suc zero))
    (curvatureInvariantGenerator
     ∷ covariantDerivativeInvariantGenerator
     ∷ CartanInvariantGenerator
     ∷ [])
    true
    true
    true
    true
    false
    "candidate admissibility row for local diffeomorphism-invariant metric actions through two jets"

abelianConnectionOneJetSpec : DepthAdmissibilitySpec
abelianConnectionOneJetSpec =
  mkDepthAdmissibilitySpec
    "abelian-connection-one-jet"
    abelianGaugeRedundancy
    oneFormCarrier
    (suc zero)
    (fieldStrengthInvariantGenerator
     ∷ covariantDerivativeInvariantGenerator
     ∷ [])
    true
    true
    true
    true
    false
    "candidate admissibility row for a local abelian connection and its field strength"

nonAbelianConnectionOneJetSpec : DepthAdmissibilitySpec
nonAbelianConnectionOneJetSpec =
  mkDepthAdmissibilitySpec
    "non-abelian-connection-one-jet"
    nonAbelianGaugeRedundancy
    principalConnectionCarrier
    (suc zero)
    (fieldStrengthInvariantGenerator
     ∷ covariantDerivativeInvariantGenerator
     ∷ CartanInvariantGenerator
     ∷ [])
    true
    true
    true
    true
    false
    "candidate admissibility row for a local principal connection; no Yang--Mills uniqueness theorem is promoted"

spinorOneJetSpec : DepthAdmissibilitySpec
spinorOneJetSpec =
  mkDepthAdmissibilitySpec
    "spinor-one-jet"
    spinLiftRedundancy
    spinorCarrier
    (suc zero)
    (DiracInvariantGenerator
     ∷ covariantDerivativeInvariantGenerator
     ∷ [])
    true
    true
    true
    true
    false
    "candidate spin-lift row; existence of a spin structure remains an explicit prerequisite"

bitensorTwoPointSpec : DepthAdmissibilitySpec
bitensorTwoPointSpec =
  mkDepthAdmissibilitySpec
    "bitensor-two-point"
    diffeomorphismRedundancy
    bitensorCarrier
    zero
    (twoPointInvariantGenerator
     ∷ CartanInvariantGenerator
     ∷ [])
    false
    true
    true
    true
    false
    "two-point relational carrier for propagators, correlators, or transport; locality is not asserted"

canonicalAdmissibilitySpecs : List DepthAdmissibilitySpec
canonicalAdmissibilitySpecs =
  metricDiffeomorphismTwoJetSpec
  ∷ abelianConnectionOneJetSpec
  ∷ nonAbelianConnectionOneJetSpec
  ∷ spinorOneJetSpec
  ∷ bitensorTwoPointSpec
  ∷ []

metricSpecIsTwoJet : jetOrder metricDiffeomorphismTwoJetSpec ≡ suc (suc zero)
metricSpecIsTwoJet = refl

spinorSpecIsOneJet : jetOrder spinorOneJetSpec ≡ suc zero
spinorSpecIsOneJet = refl

metricSpecDoesNotClaimDerivation : physicalDerivationClaimed metricDiffeomorphismTwoJetSpec ≡ false
metricSpecDoesNotClaimDerivation = refl

nonAbelianSpecDoesNotClaimDerivation : physicalDerivationClaimed nonAbelianConnectionOneJetSpec ≡ false
nonAbelianSpecDoesNotClaimDerivation = refl
