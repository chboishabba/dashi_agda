module DASHI.Physics.YangMills.BalabanClayGate4Attachment252MechanismAuditExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Audit of the mechanism brief supplied for the present continuation tranche.
------------------------------------------------------------------------

data MechanismAuthorityClass : Set where
  primaryMathematicalSource peerReviewedMethodology textbookNormalization
  locatorOnly alternativeStrategy systemicOverclaimRisk : MechanismAuthorityClass

record MechanismAuditEntry : Set where
  constructor mechanismAudit
  field
    authors : String
    title : String
    venueOrPublisher : String
    doiOrStableIdentifier : String
    classification : MechanismAuthorityClass
    admissibleAsAuthorityForStatedScope : Bool
    usableAsMechanismPrompt : Bool
    exactDASHIScope : String
    forbiddenInference : String

open MechanismAuditEntry public

su2HaarChartAudit : MechanismAuditEntry
su2HaarChartAudit = mechanismAudit
  "Brian C. Hall; Michael Creutz"
  "Lie Groups, Lie Algebras, and Representations; Quarks, Gluons and Lattices"
  "Springer; Cambridge University Press"
  "10.1007/978-3-319-13467-3; 10.1017/9781009290395"
  textbookNormalization
  true
  true
  "SU(2) exponential-coordinate normalization and Haar-density convention"
  "does not by itself prove the polymer-wide loss budget or physical/reference ratio"

finiteDeterminantAudit : MechanismAuditEntry
finiteDeterminantAudit = mechanismAudit
  "Barry Simon; Gerald V. Dunne"
  "Trace Ideals and Their Applications; Functional Determinants in Quantum Field Theory"
  "American Mathematical Society; Journal of Physics A"
  "10.1090/surv/120; 10.1088/1751-8113/41/30/304006"
  peerReviewedMethodology
  true
  true
  "finite trace-log and relative-determinant methodology"
  "does not supply the physical Hessian perturbation or its uniform small-field norm"

blockAdjointLocatorAudit : MechanismAuditEntry
blockAdjointLocatorAudit = mechanismAudit
  "Lluis Eriksson"
  "Uniform Poincare Inequality for Lattice Yang-Mills Theory Via Multiscale Martingale Decomposition"
  "ai.viXra"
  "ai.viXra:2602.0040; no DOI"
  locatorOnly
  false
  true
  "prompt to prove a physical squared-adjoint 2^(-3k) estimate independently"
  "RG-normalized disintegration and the physical Q* norm may not be imported"

reehSchliederAudit : MechanismAuditEntry
reehSchliederAudit = mechanismAudit
  "Helmut Reeh and Siegfried Schlieder"
  "Bemerkungen zur Unitaraquivalenz von Lorentzinvarianten Feldern"
  "Il Nuovo Cimento 22 (1961), 1051--1068"
  "10.1007/BF02787889"
  primaryMathematicalSource
  true
  true
  "cyclicity motivation for detecting reconstructed subgap vectors"
  "full local-net Reeh--Schlieder may not be inferred from the current abstract OS carrier"

harrisMixingAudit : MechanismAuditEntry
harrisMixingAudit = mechanismAudit
  "author metadata pending primary verification"
  "boundary-Langevin/Harris-mixing mass-gap programme"
  "tsizek.github.io working-paper locator"
  "vacuum-has-steps/paper.pdf; no DOI verified"
  alternativeStrategy
  false
  true
  "alternative route if a uniform boundary-process contraction is independently proved"
  "does not replace H-LOC or clustering without the uniform contraction theorem"

claimedSolutionClusterAudit : MechanismAuditEntry
claimedSolutionClusterAudit = mechanismAudit
  "multiple recent preprint authors"
  "complete or near-complete four-dimensional Yang--Mills mass-gap claims"
  "unreviewed preprints and personal repositories"
  "representative locator arXiv:2506.00284"
  systemicOverclaimRisk
  false
  true
  "isolated lemma extraction after independent reproduction only"
  "no global completion claim may enter any theorem premise"

attachmentMechanismEntries : List MechanismAuditEntry
attachmentMechanismEntries =
  su2HaarChartAudit ∷ finiteDeterminantAudit ∷ blockAdjointLocatorAudit ∷
  reehSchliederAudit ∷ harrisMixingAudit ∷ claimedSolutionClusterAudit ∷ []

attachmentMechanismAuditLevel : ProofLevel
attachmentMechanismAuditLevel = machineChecked

-- The Boolean fields above carry the fail-closed authority decision. The
-- proof-level view is therefore conjectural, not a separate quarantine tag.
locatorMechanismsAcceptedAsAuthority : ProofLevel
locatorMechanismsAcceptedAsAuthority = conjectural
