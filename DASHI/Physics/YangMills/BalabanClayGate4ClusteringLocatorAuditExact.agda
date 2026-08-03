module DASHI.Physics.YangMills.BalabanClayGate4ClusteringLocatorAuditExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary source locator confirmed independently.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
-- Project Euclid stable identifier: euclid:cmp/1104161193.
--
-- Secondary source under audit, never theorem authority:
-- Lluis Eriksson,
-- "Exponential Clustering and Mass Gap for Four-Dimensional SU(N) Lattice
-- Yang--Mills Theory Via Balaban's Renormalization Group and Multiscale
-- Correlator Decoupling -- a Conditional Clustering Theorem --",
-- ai.viXra:2602.0088v3, July 2026, no DOI recorded.
------------------------------------------------------------------------

record ConditionalLocatorLoad : Set where
  constructor locatorLoad
  field
    name : String
    statement : String
    suppliedByPrimarySource : Bool
    suppliedByRepositoryTheorem : Bool
    statusNote : String

open ConditionalLocatorLoad public

hKP : ConditionalLocatorLoad
hKP = locatorLoad
  "H-KP"
  "terminal Kotecky--Preiss smallness uniform in physical volume"
  false
  false
  "v3 retags the former Theorem 5.3 as a hypothesis because its intended companion is unpublished and identifier-less"

hLOC : ConditionalLocatorLoad
hLOC = locatorLoad
  "H-LOC"
  "exponential localization of conditioned blocked observables"
  false
  false
  "v3 adds this hypothesis after observing that conditional expectation generally delocalizes support"

hRBeta : ConditionalLocatorLoad
hRBeta = locatorLoad
  "H-Rbeta"
  "uniform-in-scale analyticity radius and bound for the discrete beta function in h = g^2"
  false
  false
  "the locator uses this as the Cauchy-estimate input for coupling control; it is not verified from Balaban in the paper"

hP0Prime : ConditionalLocatorLoad
hP0Prime = locatorLoad
  "H-P0'"
  "large-field profile inequality exp(-p0(g)) <= g^4 in the selected weak-coupling regime"
  false
  false
  "this is a separate profile condition, not a consequence of the polylogarithmic p0 metadata alone"

hDECScale : ConditionalLocatorLoad
hDECScale = locatorLoad
  "per-scale decoupling"
  "cluster expansion with holes uniformly over conditioned coarse fields"
  false
  false
  "the locator explicitly tags Lemma 6.2 as a traceable import with a decoupling load"

os4Load : ConditionalLocatorLoad
os4Load = locatorLoad
  "OS4"
  "uniform exponential clustering of continuum Schwinger functions"
  false
  false
  "the locator obtains OS4 only under H-KP, H-LOC, H-Rbeta, H-P0' and per-scale decoupling"

os1Load : ConditionalLocatorLoad
os1Load = locatorLoad
  "OS1"
  "full O(4) Euclidean covariance in the continuum limit"
  false
  false
  "v3 establishes only translations and the hypercubic group and explicitly leaves full O(4) covariance open"

conditionalLoads : List ConditionalLocatorLoad
conditionalLoads =
  hKP ∷ hLOC ∷ hRBeta ∷ hP0Prime ∷ hDECScale ∷ os4Load ∷ os1Load ∷ []

record LocatorExactContent : Set where
  constructor exactContent
  field
    item : String
    exactOnlyAtClaimedScope : Bool
    note : String

open LocatorExactContent public

multiscaleTelescoping : LocatorExactContent
multiscaleTelescoping = exactContent
  "law-of-total-covariance telescoping identity"
  true
  "exact for arbitrary measures and a nested sigma-algebra chain"

scaleSummationArithmetic : LocatorExactContent
scaleSummationArithmetic = exactContent
  "summation of assumed per-scale exponential errors"
  true
  "arithmetic is exact only after the per-scale decoupling estimate is supplied"

latticeAnimalArithmetic : LocatorExactContent
latticeAnimalArithmetic = exactContent
  "finite lattice-animal counting bounds"
  true
  "combinatorial content does not supply the missing physical polymer activity bound"

couplingRecursionArithmetic : LocatorExactContent
couplingRecursionArithmetic = exactContent
  "inverse-coupling induction arithmetic"
  true
  "the recursion closes only after H-Rbeta and H-P0' supply the two remainders"

locatorExactContent : List LocatorExactContent
locatorExactContent =
  multiscaleTelescoping ∷ scaleSummationArithmetic ∷
  latticeAnimalArithmetic ∷ couplingRecursionArithmetic ∷ []

record ClusteringLocatorAudit : Set where
  field
    admissibleAsAuthority : Bool
    usableAsLocator : Bool
    usableAsRiskPrompt : Bool
    noStatementImportedUnconditionally : Bool
    conditionalLoadsRecorded : List ConditionalLocatorLoad
    exactScopeRecorded : List LocatorExactContent

open ClusteringLocatorAudit public

eriksson26020088v3Audit : ClusteringLocatorAudit
eriksson26020088v3Audit = record
  { admissibleAsAuthority = false
  ; usableAsLocator = true
  ; usableAsRiskPrompt = true
  ; noStatementImportedUnconditionally = true
  ; conditionalLoadsRecorded = conditionalLoads
  ; exactScopeRecorded = locatorExactContent
  }

clusteringLocatorQuarantineLevel : ProofLevel
clusteringLocatorQuarantineLevel = machineChecked

clusteringLocatorConditionalLoadAuditLevel : ProofLevel
clusteringLocatorConditionalLoadAuditLevel = machineChecked

projectEuclidClusterExpansionLocatorLevel : ProofLevel
projectEuclidClusterExpansionLocatorLevel = machineChecked
