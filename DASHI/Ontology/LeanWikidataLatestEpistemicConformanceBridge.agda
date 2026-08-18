module DASHI.Ontology.LeanWikidataLatestEpistemicConformanceBridge where

open import Agda.Builtin.List using (List; []; _∷_)

open import DASHI.Ontology.LeanWikidataFullSourceManifest
open import DASHI.Ontology.LeanWikidataTheoremSurfaceBridge

------------------------------------------------------------------------
-- Source-pinned theorem-surface conformance for the later supplied JMD /
-- Aristotle development.
--
-- These contracts do NOT identify Lean proof terms with Agda proof terms.
-- They record that independently implemented theorem surfaces have the same
-- mathematical reading, so DASHI can test its local constructions against the
-- source theorem names without creating a second generic observer/quotient
-- stack.
------------------------------------------------------------------------

latestTetralemmaSource : LeanSourceModule
latestTetralemmaSource =
  leanSourceModule
    "RequestProject.Epistemic.Tetralemma"
    "d043a72b73401c8d7642bca4683f3a12939fb208a2a4b7aeade09574873ac512"
    foundations
    (epistemicAnchor ∷ derivationFibreAnchor ∷ [])

latestObserverSource : LeanSourceModule
latestObserverSource =
  leanSourceModule
    "RequestProject.Epistemic.Observer"
    "124e74d371d89f8f4140f70051ff5d40f766d8b2fcd890a8f11989253b350a0d"
    foundations
    (epistemicAnchor ∷ derivationFibreAnchor ∷ [])

latestQuotientSource : LeanSourceModule
latestQuotientSource =
  leanSourceModule
    "RequestProject.Epistemic.Quotient"
    "11989e1b382db938f536c42b2f3e8d43ce1847298dfd55d5df6a05b361f3d4cd"
    foundations
    (epistemicAnchor ∷ derivationFibreAnchor ∷ contextualClaimAnchor ∷ [])

latestClassAlgebraSource : LeanSourceModule
latestClassAlgebraSource =
  leanSourceModule
    "RequestProject.Wikidata.ClassAlgebra"
    "18c413bdd2720de4e60797a953168d28f5a8b93ad046d01326989ed3a8ca27c9"
    classHierarchy
    (epistemicAnchor ∷ repairReviewAnchor ∷ [])

latestAlignmentSource : LeanSourceModule
latestAlignmentSource =
  leanSourceModule
    "RequestProject.Wikidata.Alignment"
    "88ed929e9945ac5e524de9850795af6ccaceb5aaaacf298347f25b7bfd7cf3da"
    classHierarchy
    (contextualClaimAnchor ∷ derivationFibreAnchor ∷ candidateRoleAnchor ∷ [])

latestLensSource : LeanSourceModule
latestLensSource =
  leanSourceModule
    "RequestProject.Wikidata.Lens"
    "7a39fa8d9c4672c21d0bc7b65c1d3533d0b48e91a93d59b22b85df79810751c3"
    dataModel
    (epistemicAnchor ∷ contextualClaimAnchor ∷ [])

latestParentingFibresSource : LeanSourceModule
latestParentingFibresSource =
  leanSourceModule
    "RequestProject.Wikidata.ParentingFibres"
    "68ae2c3739594353abf828c48bc34b2fefbb7219b8ac8bc00d291b2379070ab3"
    classHierarchy
    (epistemicAnchor ∷ derivationFibreAnchor ∷ [])

latestParentingAuthoritySource : LeanSourceModule
latestParentingAuthoritySource =
  leanSourceModule
    "RequestProject.Wikidata.ParentingAuthority"
    "e276a92b709633a5dac74fcb6e423be59a9addf061451301afcb450eb95fd516"
    classHierarchy
    (epistemicAnchor ∷ authorityBoundaryAnchor ∷ [])

latestEpistemicSources : List LeanSourceModule
latestEpistemicSources =
  latestTetralemmaSource ∷ latestObserverSource ∷ latestQuotientSource ∷
  latestClassAlgebraSource ∷ latestAlignmentSource ∷ latestLensSource ∷
  latestParentingFibresSource ∷ latestParentingAuthoritySource ∷ []

------------------------------------------------------------------------
-- Load-bearing theorem contracts.
------------------------------------------------------------------------

jmdCollapseNotInjective : LeanTheoremContract
jmdCollapseNotInjective =
  leanTheoremContract latestTetralemmaSource
    "Epistemic.collapse_not_injective"
    "the trit projection cannot distinguish support-square conflict from ignorance"
    negativeConstraintTheorem

jmdMergeBeforeCollapse : LeanTheoremContract
jmdMergeBeforeCollapse =
  leanTheoremContract latestTetralemmaSource
    "Epistemic.merge_then_collapse_ne_collapse_then_merge"
    "pool source evidence on support squares before lossy trit presentation"
    semanticExactness

jmdResidualFibreConsSubset : LeanTheoremContract
jmdResidualFibreConsSubset =
  leanTheoremContract latestObserverSource
    "Epistemic.residualFibre_cons_subset"
    "adding an observer can only shrink the residual observational fibre"
    structuralTheorem

jmdHiddenTransitionMovesResidual : LeanTheoremContract
jmdHiddenTransitionMovesResidual =
  leanTheoremContract latestQuotientSource
    "Epistemic.ExactRecoverable.residual_ne_of_hiddenTransition"
    "a nontrivial hidden transition at fixed surface must move the exact reopening residual"
    structuralTheorem

jmdFactorsThroughIffFibreConstant : LeanTheoremContract
jmdFactorsThroughIffFibreConstant =
  leanTheoremContract latestQuotientSource
    "Epistemic.factorsThrough_iff_fibreConstant"
    "a fine route factors through a coarse projection exactly when it is constant on projection fibres"
    semanticExactness

jmdDisjointUnionCheckerExact : LeanTheoremContract
jmdDisjointUnionCheckerExact =
  leanTheoremContract latestClassAlgebraSource
    "Wikidata.dunOk_iff"
    "the executable finite-KB disjoint-union checker is exact for union coverage plus pairwise disjointness"
    checkerExactness

jmdAlignmentSubclassExact : LeanTheoremContract
jmdAlignmentSubclassExact =
  leanTheoremContract latestAlignmentSource
    "Wikidata.Alignment.alignOk_iff"
    "alignment checker exactly characterizes its declared mapped-subclass edge obligations"
    crossOntologyTheorem

jmdAlignmentDisjointReflect : LeanTheoremContract
jmdAlignmentDisjointReflect =
  leanTheoremContract latestAlignmentSource
    "Wikidata.Alignment.disjoint_reflect"
    "target disjointness reflects through an alignment only with the explicit instance-transport hypothesis"
    crossOntologyTheorem

jmdReifiedDeterminesDirectRdf : LeanTheoremContract
jmdReifiedDeterminesDirectRdf =
  leanTheoremContract latestLensSource
    "Wikidata.determines_reified_direct"
    "the reified RDF view determines the direct RDF view"
    semanticExactness

jmdDirectDoesNotDetermineReifiedRdf : LeanTheoremContract
jmdDirectDoesNotDetermineReifiedRdf =
  leanTheoremContract latestLensSource
    "Wikidata.not_determines_direct_reified"
    "the direct RDF view does not recover the reified RDF view"
    negativeConstraintTheorem
