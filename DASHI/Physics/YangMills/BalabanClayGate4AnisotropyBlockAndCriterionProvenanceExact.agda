module DASHI.Physics.YangMills.BalabanClayGate4AnisotropyBlockAndCriterionProvenanceExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Source-normalization update for anisotropy, block averaging and terminal
-- cluster criteria.
------------------------------------------------------------------------

record ProvenanceEntry : Set where
  constructor provenanceEntry
  field
    authors : String
    title : String
    venueYearPages : String
    identifier : String
    peerReviewed : Bool
    admissibleAsMethodAuthority : Bool
    provesPhysicalDASHITarget : Bool
    note : String

open ProvenanceEntry public

drummondAnisotropyBenchmark : ProvenanceEntry
drummondAnisotropyBenchmark = provenanceEntry
  "I. T. Drummond, A. Hart, R. R. Horgan, and L. C. Storoni"
  "One Loop Calculation of the Renormalised Anisotropy for Improved Anisotropic Gluon Actions on a Lattice"
  "Physical Review D 66 (2002), 094509"
  "DOI 10.1103/PhysRevD.66.094509; arXiv:hep-lat/0208010"
  true
  true
  false
  "correct source of the quoted SU(3), 3+1-dimensional one-loop O(3 percent) anisotropy benchmark; perturbative evidence only"

karschAnisotropyCoefficientReference : ProvenanceEntry
karschAnisotropyCoefficientReference = provenanceEntry
  "J. Engels, F. Karsch, and T. Scheideler"
  "Determination of Anisotropy Coefficients for SU(3) Gauge Actions from the Integral and Matching Methods"
  "Nuclear Physics B 564 (2000), 303--324"
  "DOI 10.1016/S0550-3213(99)00522-2; arXiv:hep-lat/9905002"
  true
  true
  false
  "nonperturbative lattice anisotropy-coefficient benchmark; distinct from hep-lat/0208010 and not an OS1 proof"

balabanFermionBlockRGReference : ProvenanceEntry
balabanFermionBlockRGReference = provenanceEntry
  "Tadeusz Bałaban, Michael O'Carroll, and Ricardo Schor"
  "Block Renormalization Group for Euclidean Fermions"
  "Communications in Mathematical Physics 122 (1989), 233--247"
  "DOI 10.1007/BF01257414"
  true
  true
  false
  "primary precedent for block averaging, uniform rescaled exponential decay and fluctuation two-point decompositions in a free fermion setting; it does not prove the gauge-field Q-star 1/8 norm"

balabanImbrieJaffePropagatorReference : ProvenanceEntry
balabanImbrieJaffePropagatorReference = provenanceEntry
  "Tadeusz Bałaban, John Imbrie, and Arthur Jaffe"
  "Renormalization of the Higgs Model: Minimizers, Propagators and the Stability of Mean Field Theory"
  "Communications in Mathematical Physics 97 (1985), 299--329"
  "DOI 10.1007/BF01206191"
  true
  true
  false
  "constructive-RG precedent for uniform propagator bounds and exponential kernels; transfer to four-dimensional pure gauge block adjoints requires a separate physical theorem"

koteckyPreissPrimaryReference : ProvenanceEntry
koteckyPreissPrimaryReference = provenanceEntry
  "Roman Kotecký and David Preiss"
  "Cluster Expansion for Abstract Polymer Models"
  "Communications in Mathematical Physics 103 (1986), 491--498"
  "DOI 10.1007/BF01211762"
  true
  true
  false
  "primary two-weight a,d criterion; physical terminal activities and incompatibility neighbourhoods must be identified explicitly"

fernandezProcacciPrimaryReference : ProvenanceEntry
fernandezProcacciPrimaryReference = provenanceEntry
  "Roberto Fernández and Aldo Procacci"
  "Cluster Expansion for Abstract Polymer Models. New Bounds from an Old Approach"
  "Communications in Mathematical Physics 274 (2007), 123--140"
  "DOI 10.1007/s00220-007-0279-2; arXiv:math-ph/0605041"
  true
  true
  false
  "published stronger convergence region; does not by itself prove the physical Yang--Mills activity majorant"

allNormalizedEntries : List ProvenanceEntry
allNormalizedEntries =
  drummondAnisotropyBenchmark ∷
  karschAnisotropyCoefficientReference ∷
  balabanFermionBlockRGReference ∷
  balabanImbrieJaffePropagatorReference ∷
  koteckyPreissPrimaryReference ∷
  fernandezProcacciPrimaryReference ∷ []

data LocatorConfidence : Set where
  singleQuarantinedLocator : LocatorConfidence
  multipleIndependentLocators : LocatorConfidence
  primaryAbstractOnly : LocatorConfidence
  primaryTextVerified : LocatorConfidence

balabanEquation175Confidence : LocatorConfidence
balabanEquation175Confidence = singleQuarantinedLocator

balabanEquation189Confidence : LocatorConfidence
balabanEquation189Confidence = multipleIndependentLocators

balabanEquation1100Confidence : LocatorConfidence
balabanEquation1100Confidence = multipleIndependentLocators

blockAdjointPhysicalTargetNote : String
blockAdjointPhysicalTargetNote =
  "uniform propagator boundedness and exponential kernel decay support the mechanism, but neither the fermion nor Higgs reference proves normSq(Qstar(k+1)) <= 1/8 normSq(Qstar(k)) for DASHI's physical gauge carrier"

harrisSearchStatusNote : String
harrisSearchStatusNote =
  "no ready-made Yang--Mills boundary-process drift/minorization construction is imported; Harris remains a separate conditional fallback"

anisotropyBenchmarkNormalizationLevel : ProofLevel
anisotropyBenchmarkNormalizationLevel = machineChecked

blockRGMethodProvenanceLevel : ProofLevel
blockRGMethodProvenanceLevel = standardImported

primaryKPTwoWeightProvenanceLevel : ProofLevel
primaryKPTwoWeightProvenanceLevel = standardImported

balabanEquation175SingleLocatorLevel : ProofLevel
balabanEquation175SingleLocatorLevel = conditional

physicalBlockAdjointContractionInputsLevel : ProofLevel
physicalBlockAdjointContractionInputsLevel = conditional
