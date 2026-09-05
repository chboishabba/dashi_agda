module DASHI.Analysis.NonArchimedeanSigmaRoleSeparationExact where

------------------------------------------------------------------------
-- SIGMA ROLE SEPARATION
--
-- The source repository uses the numeral 1/2 in three distinct places:
--
--   1. cyclotomic orbit amplitude: |W| = sqrt 2 = 2^(1/2);
--   2. level-to-level contraction of log r_n;
--   3. Archimedean/Prolate spectral parameter s = sigma + i t with
--      critical line sigma = 1/2.
--
-- Numerical equality is not a same-object receipt.  These coordinates remain
-- separately typed until an explicit source theorem relates them.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)


data SigmaRole : Set where
  cyclotomicAmplitudeExponent : SigmaRole
  directedLevelContraction : SigmaRole
  archimedeanCriticalLine : SigmaRole
  undirectedGapExponent : SigmaRole

record SigmaRoleEvidence : Set where
  constructor sigmaRoleEvidence
  field
    role : SigmaRole
    halfNumeralAppears : Bool
    theoremBearingSourceObjectLocated : Bool
    sameObjectWithCyclotomicAmplitude : Bool
    sameObjectWithArchimedeanCriticalLine : Bool

cyclotomicEvidence : SigmaRoleEvidence
cyclotomicEvidence =
  sigmaRoleEvidence cyclotomicAmplitudeExponent true true true false

levelContractionEvidence : SigmaRoleEvidence
levelContractionEvidence =
  sigmaRoleEvidence directedLevelContraction true true false false

archimedeanEvidence : SigmaRoleEvidence
archimedeanEvidence =
  sigmaRoleEvidence archimedeanCriticalLine true true false true

undirectedAlphaEvidence : SigmaRoleEvidence
undirectedAlphaEvidence =
  sigmaRoleEvidence undirectedGapExponent false true false false

record SigmaFirewall : Set where
  constructor sigmaFirewall
  field
    sameNumeralImpliesSameQuantity : Bool
    perLevelHalfImpliesSizePowerHalf : Bool
    cyclotomicHalfImpliesCriticalLineHalf : Bool
    criticalLineHalfImpliesCyclotomicHalf : Bool
    independentWeldRequired : Bool

canonicalSigmaFirewall : SigmaFirewall
canonicalSigmaFirewall =
  sigmaFirewall false false false false true

sameHalfNumeralDoesNotWeldRoles :
  SigmaFirewall.sameNumeralImpliesSameQuantity canonicalSigmaFirewall ≡ false
sameHalfNumeralDoesNotWeldRoles = refl

cyclotomicDoesNotPromoteCriticalLine :
  SigmaFirewall.cyclotomicHalfImpliesCriticalLineHalf canonicalSigmaFirewall ≡ false
cyclotomicDoesNotPromoteCriticalLine = refl

criticalLineDoesNotPromoteCyclotomic :
  SigmaFirewall.criticalLineHalfImpliesCyclotomicHalf canonicalSigmaFirewall ≡ false
criticalLineDoesNotPromoteCyclotomic = refl
