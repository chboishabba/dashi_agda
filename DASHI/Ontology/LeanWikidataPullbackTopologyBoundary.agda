module DASHI.Ontology.LeanWikidataPullbackTopologyBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Ontology.LeanWikidataTheoremSurfaceBridge
open import DASHI.Ontology.LeanWikidataParentingPullbackBridge

------------------------------------------------------------------------
-- JMD's PullbackComparison source contains both sides of an important boundary:
-- a componentwise condition is sufficient for the comparison map to be a
-- homeomorphism, and a worked counterexample shows that homeomorphism is not
-- automatic for arbitrary ontology pullbacks.
------------------------------------------------------------------------

jmdPullbackHomeomorphUnderComponentwise : LeanTheoremContract
jmdPullbackHomeomorphUnderComponentwise =
  leanTheoremContract pullbackComparisonLatestSource
    "Wikidata.Ontology.isHomeomorph_pbCompare_of_componentwise"
    "topological/ontology pullback comparison is a homeomorphism under simultaneous componentwise subclass-chain compatibility"
    preservationTheorem

jmdPullbackNotAlwaysHomeomorphic : LeanTheoremContract
jmdPullbackNotAlwaysHomeomorphic =
  leanTheoremContract pullbackComparisonLatestSource
    "Wikidata.Ontology.exists_not_isHomeomorph_pbCompare"
    "there exist ontology morphisms whose categorical pullback comparison is not a homeomorphism"
    negativeConstraintTheorem

record PullbackTopologyBoundary : Set where
  constructor pullbackTopologyBoundary
  field
    categoricalPullbackAutomaticallyTopologicalEquivalence : Bool
    componentwiseCompatibilityRequiredByPositiveTheorem : Bool
    localFibreCompatibilityMayStillNeedWitness : Bool
open PullbackTopologyBoundary public

canonicalPullbackTopologyBoundary : PullbackTopologyBoundary
canonicalPullbackTopologyBoundary =
  pullbackTopologyBoundary false true true

pullbackDoesNotCollapseSemanticTopology :
  categoricalPullbackAutomaticallyTopologicalEquivalence canonicalPullbackTopologyBoundary ≡ false
pullbackDoesNotCollapseSemanticTopology = refl

componentwiseCompatibilityRemainsExplicit :
  componentwiseCompatibilityRequiredByPositiveTheorem canonicalPullbackTopologyBoundary ≡ true
componentwiseCompatibilityRemainsExplicit = refl
