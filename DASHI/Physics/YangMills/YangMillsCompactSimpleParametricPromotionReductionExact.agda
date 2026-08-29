module DASHI.Physics.YangMills.YangMillsCompactSimpleParametricPromotionReductionExact where

------------------------------------------------------------------------
-- ROUND65: ALL-GROUP PROMOTION IS ONE PARAMETRIC ANALYTIC THEOREM
--
-- PRIMARY SOURCES
--
-- Anthony W. Knapp, "Lie Groups Beyond an Introduction".
-- DOI: 10.1007/978-1-4757-2453-0.
--
-- N. Bourbaki, "Lie Groups and Lie Algebras, Chapters 4--6".
-- ISBN: 978-3-540-69171-6; no DOI assigned to the cited edition.
--
-- Arthur Jaffe and Edward Witten, "Quantum Yang-Mills Theory", Clay
-- Mathematics Institute Millennium problem description.  No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- The repository already eliminates the compact-simple classification into a
-- QuantitativeCompactLiePackage for each classical and exceptional family.
-- Therefore P7 should not ask for independent Yang--Mills proofs for A/B/C/D
-- and G2/F4/E6/E7/E8.  The remaining analytic theorem should be parametric:
--
--   for arbitrary classified G and its quantitative Lie package,
--   the completed single-group construction transports to G.
--
-- Once that theorem is supplied, classification elimination constructs the
-- all-group family definitionally.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.CompactSimpleQuantitativeCoverage as Compact

record CompactSimpleParametricYMContinuation
    (Scalar LieElement GroupElement : Set) : Set₁ where
  field
    authority : Compact.CompactSimpleQuantitativeAuthority
      Scalar LieElement GroupElement

    PhysicalConstruction : Compact.CompactSimpleLieGroup → Set

    continueFromQuantitativePackage :
      (G : Compact.CompactSimpleLieGroup) →
      Compact.QuantitativeCompactLiePackage
        Scalar LieElement GroupElement G →
      PhysicalConstruction G

open CompactSimpleParametricYMContinuation public

allCompactSimpleConstruction :
  ∀ {Scalar LieElement GroupElement}
    (continuation : CompactSimpleParametricYMContinuation
      Scalar LieElement GroupElement) →
    (G : Compact.CompactSimpleLieGroup) →
  PhysicalConstruction continuation G
allCompactSimpleConstruction continuation G =
  continueFromQuantitativePackage continuation G
    (Compact.compactSimpleHasQuantitativePackage
      (authority continuation) G)

record AllCompactSimplePhysicalFamily
    (Scalar LieElement GroupElement : Set) : Set₁ where
  field
    continuation : CompactSimpleParametricYMContinuation
      Scalar LieElement GroupElement
    constructionForEveryCompactSimpleGroup :
      (G : Compact.CompactSimpleLieGroup) →
      PhysicalConstruction continuation G

open AllCompactSimplePhysicalFamily public

assembleAllCompactSimplePhysicalFamily :
  ∀ {Scalar LieElement GroupElement} →
  (continuation : CompactSimpleParametricYMContinuation
    Scalar LieElement GroupElement) →
  AllCompactSimplePhysicalFamily Scalar LieElement GroupElement
assembleAllCompactSimplePhysicalFamily continuation = record
  { continuation = continuation
  ; constructionForEveryCompactSimpleGroup =
      allCompactSimpleConstruction continuation
  }

compactSimpleClassificationToParametricFamilyLevel : ProofLevel
compactSimpleClassificationToParametricFamilyLevel = machineChecked

-- The physical P7 frontier is now ONE group-parametric analytic continuation
-- theorem.  The classification/family enumeration and package lookup are not
-- separate research obligations.
compactSimpleParametricYMContinuationLevel : ProofLevel
compactSimpleParametricYMContinuationLevel = conditional
