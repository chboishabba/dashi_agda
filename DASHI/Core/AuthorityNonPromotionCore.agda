module DASHI.Core.AuthorityNonPromotionCore where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Reusable authority non-promotion core.
--
-- This module is intentionally independent of promotion and physics
-- modules.  It records the closed local default for authority-bearing
-- interpretations: every authority bit below is false unless a separate
-- domain artifact supplies accepted authority elsewhere.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Authority vocabulary.

data AuthorityKind : Set where
  truthAuthority :
    AuthorityKind

  supportAuthority :
    AuthorityKind

  admissibilityAuthority :
    AuthorityKind

  clinicalAuthority :
    AuthorityKind

  scientificAuthority :
    AuthorityKind

  spiritualAuthority :
    AuthorityKind

  metaphysicalAuthority :
    AuthorityKind

  tradingAuthority :
    AuthorityKind

  theoremAuthority :
    AuthorityKind

  clayAuthority :
    AuthorityKind

  runtimeAuthority :
    AuthorityKind

  externalAuthority :
    AuthorityKind

  empiricalAuthority :
    AuthorityKind

  legalAuthority :
    AuthorityKind

  culturalAuthority :
    AuthorityKind

AuthorityDomain : Set
AuthorityDomain =
  AuthorityKind

canonicalAuthorityKinds : List AuthorityKind
canonicalAuthorityKinds =
  truthAuthority
  ∷ supportAuthority
  ∷ admissibilityAuthority
  ∷ clinicalAuthority
  ∷ scientificAuthority
  ∷ spiritualAuthority
  ∷ metaphysicalAuthority
  ∷ tradingAuthority
  ∷ theoremAuthority
  ∷ clayAuthority
  ∷ runtimeAuthority
  ∷ externalAuthority
  ∷ empiricalAuthority
  ∷ legalAuthority
  ∷ culturalAuthority
  ∷ []

canonicalAuthorityKindCount : Nat
canonicalAuthorityKindCount =
  listCount canonicalAuthorityKinds

------------------------------------------------------------------------
-- Closed authority bundle.

record AuthorityNonPromotionBundle : Set where
  constructor mkAuthorityNonPromotionBundle
  field
    bundleLabel :
      String

    truthAuthorityFlag :
      Bool

    truthAuthorityFlagIsFalse :
      truthAuthorityFlag ≡ false

    supportAuthorityFlag :
      Bool

    supportAuthorityFlagIsFalse :
      supportAuthorityFlag ≡ false

    admissibilityAuthorityFlag :
      Bool

    admissibilityAuthorityFlagIsFalse :
      admissibilityAuthorityFlag ≡ false

    clinicalAuthorityFlag :
      Bool

    clinicalAuthorityFlagIsFalse :
      clinicalAuthorityFlag ≡ false

    scientificAuthorityFlag :
      Bool

    scientificAuthorityFlagIsFalse :
      scientificAuthorityFlag ≡ false

    spiritualAuthorityFlag :
      Bool

    spiritualAuthorityFlagIsFalse :
      spiritualAuthorityFlag ≡ false

    metaphysicalAuthorityFlag :
      Bool

    metaphysicalAuthorityFlagIsFalse :
      metaphysicalAuthorityFlag ≡ false

    tradingAuthorityFlag :
      Bool

    tradingAuthorityFlagIsFalse :
      tradingAuthorityFlag ≡ false

    theoremAuthorityFlag :
      Bool

    theoremAuthorityFlagIsFalse :
      theoremAuthorityFlag ≡ false

    clayAuthorityFlag :
      Bool

    clayAuthorityFlagIsFalse :
      clayAuthorityFlag ≡ false

    runtimeAuthorityFlag :
      Bool

    runtimeAuthorityFlagIsFalse :
      runtimeAuthorityFlag ≡ false

    externalAuthorityFlag :
      Bool

    externalAuthorityFlagIsFalse :
      externalAuthorityFlag ≡ false

    empiricalAuthorityFlag :
      Bool

    empiricalAuthorityFlagIsFalse :
      empiricalAuthorityFlag ≡ false

    legalAuthorityFlag :
      Bool

    legalAuthorityFlagIsFalse :
      legalAuthorityFlag ≡ false

    culturalAuthorityFlag :
      Bool

    culturalAuthorityFlagIsFalse :
      culturalAuthorityFlag ≡ false

    promotesAnyAuthority :
      Bool

    promotesAnyAuthorityIsFalse :
      promotesAnyAuthority ≡ false

open AuthorityNonPromotionBundle public

mkClosedAuthorityNonPromotionBundle :
  String →
  AuthorityNonPromotionBundle
mkClosedAuthorityNonPromotionBundle label =
  mkAuthorityNonPromotionBundle
    label
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
    false
    refl
    false
    refl

------------------------------------------------------------------------
-- Vocabulary-indexed accessors.

authorityFlag :
  AuthorityKind →
  AuthorityNonPromotionBundle →
  Bool
authorityFlag truthAuthority bundle =
  truthAuthorityFlag bundle
authorityFlag supportAuthority bundle =
  supportAuthorityFlag bundle
authorityFlag admissibilityAuthority bundle =
  admissibilityAuthorityFlag bundle
authorityFlag clinicalAuthority bundle =
  clinicalAuthorityFlag bundle
authorityFlag scientificAuthority bundle =
  scientificAuthorityFlag bundle
authorityFlag spiritualAuthority bundle =
  spiritualAuthorityFlag bundle
authorityFlag metaphysicalAuthority bundle =
  metaphysicalAuthorityFlag bundle
authorityFlag tradingAuthority bundle =
  tradingAuthorityFlag bundle
authorityFlag theoremAuthority bundle =
  theoremAuthorityFlag bundle
authorityFlag clayAuthority bundle =
  clayAuthorityFlag bundle
authorityFlag runtimeAuthority bundle =
  runtimeAuthorityFlag bundle
authorityFlag externalAuthority bundle =
  externalAuthorityFlag bundle
authorityFlag empiricalAuthority bundle =
  empiricalAuthorityFlag bundle
authorityFlag legalAuthority bundle =
  legalAuthorityFlag bundle
authorityFlag culturalAuthority bundle =
  culturalAuthorityFlag bundle

authorityFlagIsFalse :
  (kind : AuthorityKind) →
  (bundle : AuthorityNonPromotionBundle) →
  authorityFlag kind bundle ≡ false
authorityFlagIsFalse truthAuthority bundle =
  truthAuthorityFlagIsFalse bundle
authorityFlagIsFalse supportAuthority bundle =
  supportAuthorityFlagIsFalse bundle
authorityFlagIsFalse admissibilityAuthority bundle =
  admissibilityAuthorityFlagIsFalse bundle
authorityFlagIsFalse clinicalAuthority bundle =
  clinicalAuthorityFlagIsFalse bundle
authorityFlagIsFalse scientificAuthority bundle =
  scientificAuthorityFlagIsFalse bundle
authorityFlagIsFalse spiritualAuthority bundle =
  spiritualAuthorityFlagIsFalse bundle
authorityFlagIsFalse metaphysicalAuthority bundle =
  metaphysicalAuthorityFlagIsFalse bundle
authorityFlagIsFalse tradingAuthority bundle =
  tradingAuthorityFlagIsFalse bundle
authorityFlagIsFalse theoremAuthority bundle =
  theoremAuthorityFlagIsFalse bundle
authorityFlagIsFalse clayAuthority bundle =
  clayAuthorityFlagIsFalse bundle
authorityFlagIsFalse runtimeAuthority bundle =
  runtimeAuthorityFlagIsFalse bundle
authorityFlagIsFalse externalAuthority bundle =
  externalAuthorityFlagIsFalse bundle
authorityFlagIsFalse empiricalAuthority bundle =
  empiricalAuthorityFlagIsFalse bundle
authorityFlagIsFalse legalAuthority bundle =
  legalAuthorityFlagIsFalse bundle
authorityFlagIsFalse culturalAuthority bundle =
  culturalAuthorityFlagIsFalse bundle

data AllAuthorityKindsFalse
  (bundle : AuthorityNonPromotionBundle) :
  List AuthorityKind →
  Set where
  allAuthorityKindsFalseNil :
    AllAuthorityKindsFalse bundle []

  allAuthorityKindsFalseCons :
    ∀ {kind kinds} →
    authorityFlag kind bundle ≡ false →
    AllAuthorityKindsFalse bundle kinds →
    AllAuthorityKindsFalse bundle (kind ∷ kinds)

proveAllAuthorityKindsFalse :
  (bundle : AuthorityNonPromotionBundle) →
  (kinds : List AuthorityKind) →
  AllAuthorityKindsFalse bundle kinds
proveAllAuthorityKindsFalse bundle [] =
  allAuthorityKindsFalseNil
proveAllAuthorityKindsFalse bundle (kind ∷ kinds) =
  allAuthorityKindsFalseCons
    (authorityFlagIsFalse kind bundle)
    (proveAllAuthorityKindsFalse bundle kinds)

------------------------------------------------------------------------
-- Projection lemmas.

bundleTruthAuthorityIsFalse :
  (bundle : AuthorityNonPromotionBundle) →
  truthAuthorityFlag bundle ≡ false
bundleTruthAuthorityIsFalse bundle =
  truthAuthorityFlagIsFalse bundle

bundleSupportAuthorityIsFalse :
  (bundle : AuthorityNonPromotionBundle) →
  supportAuthorityFlag bundle ≡ false
bundleSupportAuthorityIsFalse bundle =
  supportAuthorityFlagIsFalse bundle

bundleAdmissibilityAuthorityIsFalse :
  (bundle : AuthorityNonPromotionBundle) →
  admissibilityAuthorityFlag bundle ≡ false
bundleAdmissibilityAuthorityIsFalse bundle =
  admissibilityAuthorityFlagIsFalse bundle

bundleClinicalAuthorityIsFalse :
  (bundle : AuthorityNonPromotionBundle) →
  clinicalAuthorityFlag bundle ≡ false
bundleClinicalAuthorityIsFalse bundle =
  clinicalAuthorityFlagIsFalse bundle

bundleScientificAuthorityIsFalse :
  (bundle : AuthorityNonPromotionBundle) →
  scientificAuthorityFlag bundle ≡ false
bundleScientificAuthorityIsFalse bundle =
  scientificAuthorityFlagIsFalse bundle

bundleSpiritualAuthorityIsFalse :
  (bundle : AuthorityNonPromotionBundle) →
  spiritualAuthorityFlag bundle ≡ false
bundleSpiritualAuthorityIsFalse bundle =
  spiritualAuthorityFlagIsFalse bundle

bundleMetaphysicalAuthorityIsFalse :
  (bundle : AuthorityNonPromotionBundle) →
  metaphysicalAuthorityFlag bundle ≡ false
bundleMetaphysicalAuthorityIsFalse bundle =
  metaphysicalAuthorityFlagIsFalse bundle

bundleTradingAuthorityIsFalse :
  (bundle : AuthorityNonPromotionBundle) →
  tradingAuthorityFlag bundle ≡ false
bundleTradingAuthorityIsFalse bundle =
  tradingAuthorityFlagIsFalse bundle

bundleTheoremAuthorityIsFalse :
  (bundle : AuthorityNonPromotionBundle) →
  theoremAuthorityFlag bundle ≡ false
bundleTheoremAuthorityIsFalse bundle =
  theoremAuthorityFlagIsFalse bundle

bundleClayAuthorityIsFalse :
  (bundle : AuthorityNonPromotionBundle) →
  clayAuthorityFlag bundle ≡ false
bundleClayAuthorityIsFalse bundle =
  clayAuthorityFlagIsFalse bundle

bundleRuntimeAuthorityIsFalse :
  (bundle : AuthorityNonPromotionBundle) →
  runtimeAuthorityFlag bundle ≡ false
bundleRuntimeAuthorityIsFalse bundle =
  runtimeAuthorityFlagIsFalse bundle

bundleExternalAuthorityIsFalse :
  (bundle : AuthorityNonPromotionBundle) →
  externalAuthorityFlag bundle ≡ false
bundleExternalAuthorityIsFalse bundle =
  externalAuthorityFlagIsFalse bundle

bundleEmpiricalAuthorityIsFalse :
  (bundle : AuthorityNonPromotionBundle) →
  empiricalAuthorityFlag bundle ≡ false
bundleEmpiricalAuthorityIsFalse bundle =
  empiricalAuthorityFlagIsFalse bundle

bundleLegalAuthorityIsFalse :
  (bundle : AuthorityNonPromotionBundle) →
  legalAuthorityFlag bundle ≡ false
bundleLegalAuthorityIsFalse bundle =
  legalAuthorityFlagIsFalse bundle

bundleCulturalAuthorityIsFalse :
  (bundle : AuthorityNonPromotionBundle) →
  culturalAuthorityFlag bundle ≡ false
bundleCulturalAuthorityIsFalse bundle =
  culturalAuthorityFlagIsFalse bundle

bundlePromotesAnyAuthorityIsFalse :
  (bundle : AuthorityNonPromotionBundle) →
  promotesAnyAuthority bundle ≡ false
bundlePromotesAnyAuthorityIsFalse bundle =
  promotesAnyAuthorityIsFalse bundle

------------------------------------------------------------------------
-- Generic receipt adapter.

authorityNonPromotionGenericReceipt :
  AuthorityNonPromotionBundle →
  GenericReceipt.GenericReceipt
authorityNonPromotionGenericReceipt bundle =
  GenericReceipt.mkNonPromotingReceipt
    (bundleLabel bundle)
    "DASHI.Core.AuthorityNonPromotionCore"
    "canonicalAuthorityNonPromotionBundle"
    "centralized authority flags for truth, support, admissibility, clinical, scientific, spiritual, metaphysical, trading, theorem, Clay, runtime, external, empirical, legal, and cultural authority are closed"
    "accepted domain authority artifacts remain absent unless supplied by a separate external gate"
    "agda -i . DASHI/Core/AuthorityNonPromotionCore.agda"

------------------------------------------------------------------------
-- List-level bundle proofs.

data AllAuthorityBundlesNonPromoting :
  List AuthorityNonPromotionBundle →
  Set where
  allAuthorityBundlesNonPromotingNil :
    AllAuthorityBundlesNonPromoting []

  allAuthorityBundlesNonPromotingCons :
    ∀ {bundle bundles} →
    promotesAnyAuthority bundle ≡ false →
    AllAuthorityBundlesNonPromoting bundles →
    AllAuthorityBundlesNonPromoting (bundle ∷ bundles)

proveAllAuthorityBundlesNonPromoting :
  (bundles : List AuthorityNonPromotionBundle) →
  AllAuthorityBundlesNonPromoting bundles
proveAllAuthorityBundlesNonPromoting [] =
  allAuthorityBundlesNonPromotingNil
proveAllAuthorityBundlesNonPromoting (bundle ∷ bundles) =
  allAuthorityBundlesNonPromotingCons
    (promotesAnyAuthorityIsFalse bundle)
    (proveAllAuthorityBundlesNonPromoting bundles)

------------------------------------------------------------------------
-- Canonical closed bundle.

canonicalAuthorityNonPromotionBundle :
  AuthorityNonPromotionBundle
canonicalAuthorityNonPromotionBundle =
  mkClosedAuthorityNonPromotionBundle
    "canonical authority non-promotion bundle"

canonicalTruthAuthorityIsFalse :
  truthAuthorityFlag canonicalAuthorityNonPromotionBundle ≡ false
canonicalTruthAuthorityIsFalse =
  truthAuthorityFlagIsFalse canonicalAuthorityNonPromotionBundle

canonicalSupportAuthorityIsFalse :
  supportAuthorityFlag canonicalAuthorityNonPromotionBundle ≡ false
canonicalSupportAuthorityIsFalse =
  supportAuthorityFlagIsFalse canonicalAuthorityNonPromotionBundle

canonicalAdmissibilityAuthorityIsFalse :
  admissibilityAuthorityFlag canonicalAuthorityNonPromotionBundle ≡ false
canonicalAdmissibilityAuthorityIsFalse =
  admissibilityAuthorityFlagIsFalse canonicalAuthorityNonPromotionBundle

canonicalClinicalAuthorityIsFalse :
  clinicalAuthorityFlag canonicalAuthorityNonPromotionBundle ≡ false
canonicalClinicalAuthorityIsFalse =
  clinicalAuthorityFlagIsFalse canonicalAuthorityNonPromotionBundle

canonicalScientificAuthorityIsFalse :
  scientificAuthorityFlag canonicalAuthorityNonPromotionBundle ≡ false
canonicalScientificAuthorityIsFalse =
  scientificAuthorityFlagIsFalse canonicalAuthorityNonPromotionBundle

canonicalSpiritualAuthorityIsFalse :
  spiritualAuthorityFlag canonicalAuthorityNonPromotionBundle ≡ false
canonicalSpiritualAuthorityIsFalse =
  spiritualAuthorityFlagIsFalse canonicalAuthorityNonPromotionBundle

canonicalMetaphysicalAuthorityIsFalse :
  metaphysicalAuthorityFlag canonicalAuthorityNonPromotionBundle ≡ false
canonicalMetaphysicalAuthorityIsFalse =
  metaphysicalAuthorityFlagIsFalse canonicalAuthorityNonPromotionBundle

canonicalTradingAuthorityIsFalse :
  tradingAuthorityFlag canonicalAuthorityNonPromotionBundle ≡ false
canonicalTradingAuthorityIsFalse =
  tradingAuthorityFlagIsFalse canonicalAuthorityNonPromotionBundle

canonicalTheoremAuthorityIsFalse :
  theoremAuthorityFlag canonicalAuthorityNonPromotionBundle ≡ false
canonicalTheoremAuthorityIsFalse =
  theoremAuthorityFlagIsFalse canonicalAuthorityNonPromotionBundle

canonicalClayAuthorityIsFalse :
  clayAuthorityFlag canonicalAuthorityNonPromotionBundle ≡ false
canonicalClayAuthorityIsFalse =
  clayAuthorityFlagIsFalse canonicalAuthorityNonPromotionBundle

canonicalRuntimeAuthorityIsFalse :
  runtimeAuthorityFlag canonicalAuthorityNonPromotionBundle ≡ false
canonicalRuntimeAuthorityIsFalse =
  runtimeAuthorityFlagIsFalse canonicalAuthorityNonPromotionBundle

canonicalExternalAuthorityIsFalse :
  externalAuthorityFlag canonicalAuthorityNonPromotionBundle ≡ false
canonicalExternalAuthorityIsFalse =
  externalAuthorityFlagIsFalse canonicalAuthorityNonPromotionBundle

canonicalEmpiricalAuthorityIsFalse :
  empiricalAuthorityFlag canonicalAuthorityNonPromotionBundle ≡ false
canonicalEmpiricalAuthorityIsFalse =
  empiricalAuthorityFlagIsFalse canonicalAuthorityNonPromotionBundle

canonicalLegalAuthorityIsFalse :
  legalAuthorityFlag canonicalAuthorityNonPromotionBundle ≡ false
canonicalLegalAuthorityIsFalse =
  legalAuthorityFlagIsFalse canonicalAuthorityNonPromotionBundle

canonicalCulturalAuthorityIsFalse :
  culturalAuthorityFlag canonicalAuthorityNonPromotionBundle ≡ false
canonicalCulturalAuthorityIsFalse =
  culturalAuthorityFlagIsFalse canonicalAuthorityNonPromotionBundle

canonicalPromotesAnyAuthorityIsFalse :
  promotesAnyAuthority canonicalAuthorityNonPromotionBundle ≡ false
canonicalPromotesAnyAuthorityIsFalse =
  promotesAnyAuthorityIsFalse canonicalAuthorityNonPromotionBundle

canonicalAuthorityKindsFalse :
  AllAuthorityKindsFalse
    canonicalAuthorityNonPromotionBundle
    canonicalAuthorityKinds
canonicalAuthorityKindsFalse =
  proveAllAuthorityKindsFalse
    canonicalAuthorityNonPromotionBundle
    canonicalAuthorityKinds

canonicalAuthorityNonPromotionBundles :
  List AuthorityNonPromotionBundle
canonicalAuthorityNonPromotionBundles =
  canonicalAuthorityNonPromotionBundle
  ∷ []

canonicalAuthorityNonPromotionBundleCount :
  Nat
canonicalAuthorityNonPromotionBundleCount =
  listCount canonicalAuthorityNonPromotionBundles

canonicalAuthorityNonPromotionBundlesNonPromoting :
  AllAuthorityBundlesNonPromoting canonicalAuthorityNonPromotionBundles
canonicalAuthorityNonPromotionBundlesNonPromoting =
  proveAllAuthorityBundlesNonPromoting
    canonicalAuthorityNonPromotionBundles

canonicalAuthorityNonPromotionGenericReceipt :
  GenericReceipt.GenericReceipt
canonicalAuthorityNonPromotionGenericReceipt =
  authorityNonPromotionGenericReceipt
    canonicalAuthorityNonPromotionBundle

canonicalAuthorityNonPromotionGenericReceipts :
  List GenericReceipt.GenericReceipt
canonicalAuthorityNonPromotionGenericReceipts =
  canonicalAuthorityNonPromotionGenericReceipt
  ∷ []

canonicalAuthorityNonPromotionGenericReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting
    canonicalAuthorityNonPromotionGenericReceipts
canonicalAuthorityNonPromotionGenericReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting
    canonicalAuthorityNonPromotionGenericReceipts
