module DASHI.HyperfabricMonsterConjugacyActionValidation where

import DASHI.Moonshine.HyperfabricMonsterConjugacyActionAuditExact as Audit

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

literalActionCarrierIsUsed :
  Audit.HyperfabricMonsterConjugacyBoundary.literalHyperformalCarrierUsed
    Audit.canonicalHyperfabricMonsterConjugacyBoundary
  ≡ true
literalActionCarrierIsUsed = refl
  where
  open import Agda.Builtin.Bool using (true)

noncommutingActionGeneratorsAreUsed :
  Audit.HyperfabricMonsterConjugacyBoundary.literalNoncommutingGeneratorsUsed
    Audit.canonicalHyperfabricMonsterConjugacyBoundary
  ≡ true
noncommutingActionGeneratorsAreUsed = refl
  where
  open import Agda.Builtin.Bool using (true)

noFullMonsterActionClaim :
  Audit.HyperfabricMonsterConjugacyBoundary.fullMonsterActionOnHyperfabricEstablished
    Audit.canonicalHyperfabricMonsterConjugacyBoundary
  ≡ false
noFullMonsterActionClaim = refl

no194ClassComparisonClaimYet :
  Audit.HyperfabricMonsterConjugacyBoundary.all194MonsterClassesCompared
    Audit.canonicalHyperfabricMonsterConjugacyBoundary
  ≡ false
no194ClassComparisonClaimYet = refl
