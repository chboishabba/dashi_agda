{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5CylinderDeterminingClusterUniquenessExact where

------------------------------------------------------------------------
-- CYLINDER EXPECTATION AGREEMENT + DETERMINING CLASS -> CLUSTER UNIQUENESS
--
-- Historical compactness records store cylinder agreement, measure separation,
-- and continuum uniqueness as independent Set receipts.  The last implication
-- is generic: once a selected cylinder class separates measures, agreement of
-- all its expectations determines the measure.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5CompactUniqueFullSequenceExact as Compact

record CylinderDeterminingAuthority
    (Measure Test Scalar : Set)
    (expectation : Measure → Test → Scalar) : Set₁ where
  field
    cylinderExpectationsDetermineMeasure : ∀ left right →
      (∀ test → expectation left test ≡ expectation right test) →
      left ≡ right

open CylinderDeterminingAuthority public

record ExtractedClusterCylinderAgreement
    (Measure Test Scalar : Set)
    (expectation : Measure → Test → Scalar)
    (sequence : _)
    (clusterLimit : (subsequence : Compact.SubsequenceWitness sequence) → Measure)
    (target : Measure) : Set₁ where
  field
    everyExtractedClusterAgreesOnCylinderTests :
      (subsequence : Compact.SubsequenceWitness sequence) →
      (test : Test) →
      expectation (clusterLimit subsequence) test
      ≡ expectation target test

open ExtractedClusterCylinderAgreement public

everyExtractedClusterPointIsTarget :
  ∀ {Measure Test Scalar}
    {expectation : Measure → Test → Scalar}
    {sequence : _}
    {clusterLimit :
      (subsequence : Compact.SubsequenceWitness sequence) → Measure}
    {target : Measure} →
  CylinderDeterminingAuthority Measure Test Scalar expectation →
  ExtractedClusterCylinderAgreement
    Measure Test Scalar expectation sequence clusterLimit target →
  (subsequence : Compact.SubsequenceWitness sequence) →
  clusterLimit subsequence ≡ target
everyExtractedClusterPointIsTarget authority agreement subsequence =
  cylinderExpectationsDetermineMeasure authority
    _ _
    (everyExtractedClusterAgreesOnCylinderTests agreement subsequence)

cylinderDeterminingClusterUniquenessCompilerLevel : ProofLevel
cylinderDeterminingClusterUniquenessCompilerLevel = machineChecked

cylinderDeterminingAuthorityLevel : ProofLevel
cylinderDeterminingAuthorityLevel = standardImported

physicalExtractedClusterCylinderAgreementLevel : ProofLevel
physicalExtractedClusterCylinderAgreementLevel = conditional
