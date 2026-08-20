module DASHI.Physics.YangMills.BalabanOPECoefficientRGRecurrenceUniquenessExact where

------------------------------------------------------------------------
-- ROUND86: SAME UV NORMALIZATION + SAME RG MIXING RECURSION -> OPE MATCHING
--
-- PRIMARY / METHOD SOURCES
--
-- Janos Polonyi and Kornel Sailer,
-- "Renormalization of Composite Operators", Physical Review D 63 (2001),
-- 105006. DOI: 10.1103/PhysRevD.63.105006.
--
-- Stefan Hollands and Christoph Kopper,
-- "The Operator Product Expansion Converges in Perturbative Field Theory",
-- Communications in Mathematical Physics 313 (2012), 257--290.
-- DOI: 10.1007/s00220-012-1457-4.
--
-- David J. Gross and Frank Wilczek,
-- "Ultraviolet Behavior of Non-Abelian Gauge Theories",
-- Physical Review Letters 30 (1973), 1343--1346.
-- DOI: 10.1103/PhysRevLett.30.1343.
--
-- H. David Politzer,
-- "Reliable Perturbative Results for Strong Interactions?",
-- Physical Review Letters 30 (1973), 1346--1349.
-- DOI: 10.1103/PhysRevLett.30.1346.
--
-- AUTHORITY BOUNDARY
--
-- Polonyi--Sailer calibrate the scale-indexed composite-operator mixing picture;
-- Hollands--Kopper calibrate quantitative perturbative OPE control.  Neither
-- source is imported as a nonperturbative four-dimensional pure-YM OPE theorem.
--
-- MATHEMATICAL REDUCTION
--
-- The physical OPE leaf has repeatedly been phrased as an all-scale equality
-- between the coefficient produced by the literal same-family composite RG and
-- the asymptotically-free coefficient family.  Once coefficients transform by a
-- deterministic one-step mixing map, that is stronger than necessary.
--
-- Let P_n be the physical coefficient coordinate and A_n the AF/reference
-- coefficient coordinate.  If
--
--       P_0 = A_0,
--       P_{n+1} = M_n(P_n),
--       A_{n+1} = M_n(A_n),
--
-- then P_n=A_n for every n by exact induction.  Thus the genuinely physical
-- coefficient-matching theorem can target one local statement:
--
--   the literal composite coefficient descends through the SAME one-step mixing
--   map as the AF coefficient, with the SAME UV normalization.
--
-- No second all-depth coefficient comparison is needed afterward.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong; sym; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record CoefficientRGRecurrence (Coefficient : Set) : Set₁ where
  field
    oneStepMixing : Nat → Coefficient → Coefficient
    physicalCoefficient : Nat → Coefficient
    asymptoticFreedomCoefficient : Nat → Coefficient

    sameUVNormalization :
      physicalCoefficient zero ≡ asymptoticFreedomCoefficient zero

    physicalOneStep : ∀ depth →
      physicalCoefficient (suc depth)
      ≡ oneStepMixing depth (physicalCoefficient depth)

    asymptoticFreedomOneStep : ∀ depth →
      asymptoticFreedomCoefficient (suc depth)
      ≡ oneStepMixing depth (asymptoticFreedomCoefficient depth)

open CoefficientRGRecurrence public

coefficientFamiliesEqualAtEveryDepth :
  ∀ {Coefficient}
    (dataSet : CoefficientRGRecurrence Coefficient)
    depth →
  physicalCoefficient dataSet depth
  ≡ asymptoticFreedomCoefficient dataSet depth
coefficientFamiliesEqualAtEveryDepth dataSet zero = sameUVNormalization dataSet
coefficientFamiliesEqualAtEveryDepth dataSet (suc depth) =
  trans
    (physicalOneStep dataSet depth)
    (trans
      (cong (oneStepMixing dataSet depth)
        (coefficientFamiliesEqualAtEveryDepth dataSet depth))
      (sym (asymptoticFreedomOneStep dataSet depth)))

record AllDepthCoefficientMatching
    {Coefficient : Set}
    (dataSet : CoefficientRGRecurrence Coefficient) : Set₁ where
  field
    coefficientsMatch : ∀ depth →
      physicalCoefficient dataSet depth
      ≡ asymptoticFreedomCoefficient dataSet depth

open AllDepthCoefficientMatching public

allDepthCoefficientMatching :
  ∀ {Coefficient}
    (dataSet : CoefficientRGRecurrence Coefficient) →
  AllDepthCoefficientMatching dataSet
allDepthCoefficientMatching dataSet = record
  { coefficientsMatch = coefficientFamiliesEqualAtEveryDepth dataSet }

------------------------------------------------------------------------
-- A second exact compiler for a terminal coefficient obtained by applying the
-- SAME observable/projection to the matched finite-depth coordinate.
------------------------------------------------------------------------

record MatchedCoefficientProjection
    {Coefficient PhysicalCoefficient : Set}
    (recurrence : CoefficientRGRecurrence Coefficient) : Set₁ where
  field
    project : Coefficient → PhysicalCoefficient

open MatchedCoefficientProjection public

projectedCoefficientMatch :
  ∀ {Coefficient PhysicalCoefficient}
    {recurrence : CoefficientRGRecurrence Coefficient}
    (projection : MatchedCoefficientProjection
      {PhysicalCoefficient = PhysicalCoefficient} recurrence)
    depth →
  project projection (physicalCoefficient recurrence depth)
  ≡ project projection (asymptoticFreedomCoefficient recurrence depth)
projectedCoefficientMatch {recurrence = recurrence} projection depth =
  cong (project projection)
    (coefficientFamiliesEqualAtEveryDepth recurrence depth)

coefficientRGRecurrenceUniquenessLevel : ProofLevel
coefficientRGRecurrenceUniquenessLevel = machineChecked

projectedCoefficientMatchingLevel : ProofLevel
projectedCoefficientMatchingLevel = machineChecked

-- Sharpened physical OPE/AF coefficient seam:
--
--   * identify the literal same-family OPE coefficient coordinate;
--   * prove its ONE-STEP renormalization/mixing law is the AF/reference law;
--   * prove the common UV normalization.
--
-- The all-depth coefficient matching is then machine downstream.  This can be
-- attacked together with the composite marked-source theorem because both use
-- the same literal source derivative/mixing coordinate, but the physical
-- one-step identification itself is not claimed here.
physicalSameFamilyOPECoefficientOneStepAFIdentificationLevel : ProofLevel
physicalSameFamilyOPECoefficientOneStepAFIdentificationLevel = conditional
