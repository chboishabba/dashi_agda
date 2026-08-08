module DASHI.Physics.Closure.NSTriadKNLuoClaimedSolutionCorpusRound24Exact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Record claimed, conditional, comparator and exploratory Navier-Stokes papers
-- without turning venue, novelty or a claimed conclusion into theorem
-- authority.  Every source is useful in one of four ways:
--
-- * it supplies a reusable local lemma;
-- * it states a load-bearing producer that can be isolated and attempted;
-- * it exposes a precise no-go or quantifier gap;
-- * or it supplies a distinct route that must be compared with the canonical
--   highest-alpha path.
--
-- The corpus is deliberately broader than peer-reviewed literature.  The
-- authority tier and current audit disposition remain explicit and separate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)


data AuthorityTier : Set where
  peerReviewedPaper : AuthorityTier
  arxivPreprint : AuthorityTier
  repositoryPreprint : AuthorityTier
  independentPublication : AuthorityTier
  blogOrWebsite : AuthorityTier


data ClaimFamily : Set where
  shellModifiedEnergy : ClaimFamily
  finitePacketExhaustion : ClaimFamily
  temporalResponseLift : ClaimFamily
  geometricDepletion : ClaimFamily
  helicalFluxQuasiTrapping : ClaimFamily
  filteredVortexDefect : ClaimFamily
  firstThresholdPackets : ClaimFamily
  sparseSupercriticalEnergy : ClaimFamily
  highHighResidenceAbsorption : ClaimFamily
  emergentVorticityDamping : ClaimFamily
  strainProjectionCoercivity : ClaimFamily
  topologicalContinuationExhaustion : ClaimFamily
  universalFrequencyEnvelope : ClaimFamily
  finiteCascadeSpeed : ClaimFamily
  arithmeticVortonCutoff : ClaimFamily
  symmetryRestrictedThreshold : ClaimFamily


data AuditDisposition : Set where
  localLemmaReusable : AuditDisposition
  structuralComparator : AuditDisposition
  loadBearingProducerOpen : AuditDisposition
  exactNoGoFound : AuditDisposition
  conditionalOnly : AuditDisposition
  sourceAuditOpen : AuditDisposition

record ClaimedSolutionSource : Set where
  constructor claimedSolutionSource
  field
    authors : String
    title : String
    identifier : String
    authority : AuthorityTier
    family : ClaimFamily
    disposition : AuditDisposition
    claimsUnconditionalGlobalRegularity : Bool
    suppliesClayProofAuthority : Bool

open ClaimedSolutionSource public

abuGhuwaleh : ClaimedSolutionSource
abuGhuwaleh = claimedSolutionSource
  "Mohammad Abu-Ghuwaleh"
  "Global Regularity for the Three-Dimensional Periodic Incompressible Navier-Stokes Equations: A Shellwise-Microlocal Modified-Energy Proof"
  "DOI 10.5281/zenodo.19559087"
  repositoryPreprint shellModifiedEnergy exactNoGoFound true false

abuShellBridge : ClaimedSolutionSource
abuShellBridge = claimedSolutionSource
  "Mohammad Abu-Ghuwaleh"
  "Exact Shell-Bridge Closure and Finite Packet Exhaustion for the Three-Dimensional Periodic Navier-Stokes Equations"
  "DOI 10.20944/preprints202603.1889.v1; ScienceOpen 10.14293/PR2199.003375.v1"
  repositoryPreprint finitePacketExhaustion loadBearingProducerOpen true false

camlin : ClaimedSolutionSource
camlin = claimedSolutionSource
  "Jeffrey Camlin"
  "Global Regularity for Navier-Stokes on T3 via Bounded Vorticity-Response Functionals"
  "DOI 10.63968/post-bio-ai-epistemics.v1n2.012"
  independentPublication temporalResponseLift exactNoGoFound true false

pavesi : ClaimedSolutionSource
pavesi = claimedSolutionSource
  "Luca Eliseo Pavesi"
  "Global Regularity for the Three-Dimensional Incompressible Navier-Stokes Equations via Geometric Frustration and Helical Quasi-Trapping"
  "DOI 10.5281/zenodo.21194906"
  repositoryPreprint helicalFluxQuasiTrapping loadBearingProducerOpen true false

permanaLathifIbrahim : ClaimedSolutionSource
permanaLathifIbrahim = claimedSolutionSource
  "Bryan Permana; Hanif A. Lathif; Sage A. Ibrahim"
  "Quantitative Resolution of Global Regularity for 3D Incompressible Navier-Stokes Equations: Explicit Geometric Depletion and Non-Local Alignment Rates"
  "DOI 10.5281/zenodo.19632058; SSRN 10.2139/ssrn.6557718"
  repositoryPreprint geometricDepletion loadBearingProducerOpen true false

yu : ClaimedSolutionSource
yu = claimedSolutionSource
  "Runlong Yu"
  "Filtered Vortex Stretching and Subgrid Defects for the Three-Dimensional Navier-Stokes Equations"
  "arXiv 2606.27560; DOI 10.48550/arXiv.2606.27560"
  arxivPreprint filteredVortexDefect localLemmaReusable false false

shahmurovPartI : ClaimedSolutionSource
shahmurovPartI = claimedSolutionSource
  "Rishad Shahmurov"
  "Large-Data Global Regularity for Three-Dimensional Navier-Stokes I: A Direct First-Threshold Continuation Proof for the Axisymmetric Swirl Class"
  "arXiv 2605.01875"
  arxivPreprint firstThresholdPackets loadBearingProducerOpen true false

shahmurovPartII : ClaimedSolutionSource
shahmurovPartII = claimedSolutionSource
  "Rishad Shahmurov"
  "Large-Data Global Regularity for Three-Dimensional Navier-Stokes II: A Direct First-Threshold Continuation Proof for the Full System"
  "arXiv 2605.01873"
  arxivPreprint firstThresholdPackets loadBearingProducerOpen true false

ri : ClaimedSolutionSource
ri = claimedSolutionSource
  "Myong-Hwan Ri"
  "Global regularity for the Navier-Stokes equations with application to global solvability for the Euler equations"
  "arXiv 2601.15685"
  arxivPreprint sparseSupercriticalEnergy loadBearingProducerOpen true false

inagePublished : ClaimedSolutionSource
inagePublished = claimedSolutionSource
  "Shin-ichi Inage"
  "Structural Reduction Framework and Residence-Time Compression of Coherent Same-Scale Triadic Interactions in the 3D Navier-Stokes Equations"
  "DOI 10.3390/math14091410"
  peerReviewedPaper highHighResidenceAbsorption structuralComparator false false

inageConditional : ClaimedSolutionSource
inageConditional = claimedSolutionSource
  "Shin-ichi Inage"
  "Conditional Regularity of the Three-Dimensional Navier-Stokes Equations via High-High Triadic Absorption"
  "DOI 10.20944/preprints202603.1591.v1"
  repositoryPreprint highHighResidenceAbsorption conditionalOnly false false

inageNecessaryConditions : ClaimedSolutionSource
inageNecessaryConditions = claimedSolutionSource
  "Shin-ichi Inage"
  "Structural Reduction and Necessary Conditions for Coherent Triadic Accumulation in the Three-Dimensional Navier-Stokes Equations"
  "DOI 10.20944/preprints202604.2068.v1"
  repositoryPreprint highHighResidenceAbsorption structuralComparator false false

polozov : ClaimedSolutionSource
polozov = claimedSolutionSource
  "Andrei Polozov"
  "Emergent Nonlinear Vorticity Dissipation"
  "Springer Nature Communities post / repository deposit; DOI not verified"
  blogOrWebsite emergentVorticityDamping loadBearingProducerOpen true false

nemoto : ClaimedSolutionSource
nemoto = claimedSolutionSource
  "Ryusho Nemoto"
  "NEMGRO"
  "PhilArchive record NEMGRO; DOI not located"
  repositoryPreprint strainProjectionCoercivity exactNoGoFound true false

rolloDicks : ClaimedSolutionSource
rolloDicks = claimedSolutionSource
  "Rollo Dicks"
  "Global Regularity of the Three-Dimensional Incompressible Navier-Stokes Equations via Exhaustion of Continuations"
  "Zenodo record 18963533"
  repositoryPreprint topologicalContinuationExhaustion sourceAuditOpen true false

harbeck : ClaimedSolutionSource
harbeck = claimedSolutionSource
  "William Harbeck"
  "Global Regularity for the Three-Dimensional Navier-Stokes Equations via Equilibrium Depletion and Universal Frequency Envelopes"
  "DOI 10.31224/5814"
  repositoryPreprint universalFrequencyEnvelope sourceAuditOpen true false

higgins : ClaimedSolutionSource
higgins = claimedSolutionSource
  "Rod Higgins"
  "Global Regularity of 3D Navier-Stokes: An Energy Argument"
  "DOI 10.5281/zenodo.19601371"
  blogOrWebsite finiteCascadeSpeed exactNoGoFound true false

aksman : ClaimedSolutionSource
aksman = claimedSolutionSource
  "Michael Aksman"
  "Global Regularity of 3D Navier Stokes via Topological Duality"
  "DOI 10.5281/zenodo.21263877"
  repositoryPreprint arithmeticVortonCutoff sourceAuditOpen true false

cavazzini : ClaimedSolutionSource
cavazzini = claimedSolutionSource
  "Andrea Cavazzini"
  "Symmetry, Triadic Sparsity, and Global Regularity for Kida-Pelz Navier-Stokes Flows"
  "DOI 10.5281/zenodo.19180827"
  repositoryPreprint symmetryRestrictedThreshold conditionalOnly false false

claimedSolutionCorpusRound24 : List ClaimedSolutionSource
claimedSolutionCorpusRound24 =
  abuGhuwaleh ∷
  abuShellBridge ∷
  camlin ∷
  pavesi ∷
  permanaLathifIbrahim ∷
  yu ∷
  shahmurovPartI ∷
  shahmurovPartII ∷
  ri ∷
  inagePublished ∷
  inageConditional ∷
  inageNecessaryConditions ∷
  polozov ∷
  nemoto ∷
  rolloDicks ∷
  harbeck ∷
  higgins ∷
  aksman ∷
  cavazzini ∷
  []

allCorpusSourcesAreProofAuthorities : Bool
allCorpusSourcesAreProofAuthorities = false

corpusSearchIsDeclaredExhaustive : Bool
corpusSearchIsDeclaredExhaustive = false
