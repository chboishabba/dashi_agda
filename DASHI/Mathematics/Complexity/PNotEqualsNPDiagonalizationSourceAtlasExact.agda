module DASHI.Mathematics.Complexity.PNotEqualsNPDiagonalizationSourceAtlasExact where

------------------------------------------------------------------------
-- P != NP RESOURCE-BOUNDED SELF-REFERENCE SOURCE ATLAS
--
-- Provenance policy:
--   Docs/SourceAttributionPolicy.md
--
-- These entries are bibliographic/calibration sources.  Their presence does
-- NOT import a proof of P != NP, a resource-bounded fixed point, a succinct
-- computation certificate, or any other DASHI theorem below.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

data SourceRole : Set where
  satCompleteness : SourceRole
  relativizationBarrier : SourceRole
  naturalProofBarrier : SourceRole
  algebrizationBarrier : SourceRole
  computabilitySelfReference : SourceRole
  modernCircuitLowerBoundContext : SourceRole
  metaComplexityContext : SourceRole
  cardinalityDiagonalization : SourceRole
  sharedConstraintEncoding : SourceRole
  probabilisticallyCheckableProofs : SourceRole
  boundedSelfReference : SourceRole
  booleanSwitchingAlgebra : SourceRole
  diagonalCardinality : SourceRole

data IdentifierStatus : Set where
  verifiedDOI : IdentifierStatus
  stableReportIdentifier : IdentifierStatus
  stableBookBibliography : IdentifierStatus
  stableHistoricalBibliography : IdentifierStatus

record ComplexitySource : Set where
  constructor complexitySource
  field
    authors : String
    title : String
    year : Nat
    venue : String
    stableIdentifier : String
    role : SourceRole
    identifierStatus : IdentifierStatus
    importedBoundary : String

open ComplexitySource public

shannon1938 : ComplexitySource
shannon1938 =
  complexitySource
    "Claude E. Shannon"
    "A Symbolic Analysis of Relay and Switching Circuits"
    1938
    "Transactions of the American Institute of Electrical Engineers 57(12), 713--723"
    "doi:10.1109/T-AIEE.1938.5057767"
    booleanSwitchingAlgebra
    verifiedDOI
    "Calibrates Boolean switching-function decomposition and equivalent-circuit reasoning only.  The DASHI SAT Shannon-consistency theorem additionally uses exact SAT restriction semantics; no complexity lower bound is imported."

cook1971 : ComplexitySource
cook1971 =
  complexitySource
    "Stephen A. Cook"
    "The complexity of theorem-proving procedures"
    1971
    "Proceedings of the Third Annual ACM Symposium on Theory of Computing, pp. 151--158"
    "doi:10.1145/800157.805047"
    satCompleteness
    verifiedDOI
    "Calibrates polynomial reduction / SAT-tableau ancestry only; does not provide the resource-bounded self-fixed-point theorem proposed by DASHI."

bakerGillSolovay1975 : ComplexitySource
bakerGillSolovay1975 =
  complexitySource
    "Theodore Baker; John Gill; Robert Solovay"
    "Relativizations of the P =? NP Question"
    1975
    "SIAM Journal on Computing 4(4), 431--442"
    "doi:10.1137/0204037"
    relativizationBarrier
    verifiedDOI
    "Calibrates the relativization barrier: a proof route that relativizes cannot by itself settle P versus NP."

razborovRudich1997 : ComplexitySource
razborovRudich1997 =
  complexitySource
    "Alexander A. Razborov; Steven Rudich"
    "Natural Proofs"
    1997
    "Journal of Computer and System Sciences 55(1), 24--35"
    "doi:10.1006/jcss.1997.1494"
    naturalProofBarrier
    verifiedDOI
    "Calibrates the natural-proofs barrier under its stated hardness assumptions; no claim is made that the DASHI diagonal route is automatically non-natural."

aaronsonWigderson2009 : ComplexitySource
aaronsonWigderson2009 =
  complexitySource
    "Scott Aaronson; Avi Wigderson"
    "Algebrization: A New Barrier in Complexity Theory"
    2009
    "ACM Transactions on Computation Theory 1(1), Article 2"
    "doi:10.1145/1490270.1490272"
    algebrizationBarrier
    verifiedDOI
    "Calibrates the algebrization barrier; any future self-reference proof still needs a nonrelativizing/nonalgebrizing ingredient."

kleene1952 : ComplexitySource
kleene1952 =
  complexitySource
    "Stephen Cole Kleene"
    "Introduction to Metamathematics"
    1952
    "North-Holland"
    "book-bibliography:Kleene-Introduction-to-Metamathematics-1952"
    computabilitySelfReference
    stableBookBibliography
    "Calibrates classical computability-level recursion/fixed-point self-reference only.  It does not supply a same-size or polynomial-overhead propositional fixed point."

renWilliams2026 : ComplexitySource
renWilliams2026 =
  complexitySource
    "Hanlin Ren; Ryan Williams"
    "Near-Maximum Circuit Lower Bounds for Exponential Time with Merlin-Arthur Queries"
    2026
    "Electronic Colloquium on Computational Complexity, Report TR26-118"
    "ECCC:TR26-118"
    modernCircuitLowerBoundContext
    stableReportIdentifier
    "Context only: records a 2026 lower-bound route using iterative win-win, range avoidance and PCP machinery; it is not imported as a SAT or P-versus-NP theorem."

goldbergJuvekarKabanets2026 : ComplexitySource
goldbergJuvekarKabanets2026 =
  complexitySource
    "Halley Goldberg; Mandar Juvekar; Valentine Kabanets"
    "Non-Levin NP-Hardness of Implicit MCSP and PAC Learning under Few Assumptions"
    2026
    "Electronic Colloquium on Computational Complexity, Report TR26-091"
    "ECCC:TR26-091"
    metaComplexityContext
    stableReportIdentifier
    "Context only: meta-complexity / description-complexity motivation.  No self-diagonal SAT certificate or P != NP theorem is imported."


critch2019 : ComplexitySource
critch2019 =
  complexitySource
    "Andrew Critch"
    "A parametric, resource-bounded generalization of Löb's theorem, and a robust cooperation criterion for open-source game theory"
    2019
    "Journal of Symbolic Logic 84(4), 1368--1381"
    "doi:10.1017/JSL.2017.42"
    boundedSelfReference
    verifiedDOI
    "Calibration for proof-length-bounded self-reference/reflection only.  It does not provide a SAT self-diagonal formula, a sub-circuit semantic evaluator, or a P-versus-NP lower bound."

aroraSafra1998 : ComplexitySource
aroraSafra1998 =
  complexitySource
    "Sanjeev Arora; Shmuel Safra"
    "Probabilistic checking of proofs: A new characterization of NP"
    1998
    "Journal of the ACM 45(1), 70--122"
    "doi:10.1145/273865.273901"
    probabilisticallyCheckableProofs
    verifiedDOI
    "Calibration for genuinely nonlocal/randomized proof verification.  The current DASHI self-diagonal lane does not import PCP soundness as a deterministic sub-|C| self-evaluation theorem."

aroraLundMotwaniSudanSzegedy1998 : ComplexitySource
aroraLundMotwaniSudanSzegedy1998 =
  complexitySource
    "Sanjeev Arora; Carsten Lund; Rajeev Motwani; Madhu Sudan; Mario Szegedy"
    "Proof Verification and the Hardness of Approximation Problems"
    1998
    "Journal of the ACM 45(3), 501--555"
    "doi:10.1145/278298.278306"
    probabilisticallyCheckableProofs
    verifiedDOI
    "Calibration for PCP/nonlocal verification and hardness-of-approximation techniques only.  No exact deterministic SAT self-evaluation certificate is imported."

tseitin1968 : ComplexitySource
tseitin1968 =
  complexitySource
    "Grigori S. Tseitin"
    "On the complexity of derivations in propositional calculus"
    1968
    "Studies in Constructive Mathematics and Mathematical Logic, Part II, 115--125"
    "historical-bibliography:Tseitin-1968-115-125"
    sharedConstraintEncoding
    stableHistoricalBibliography
    "Calibrates the auxiliary-variable/shared-constraint tradition used by the circuit DAG lane.  No DOI is asserted for the 1968 source, and no P-versus-NP lower bound is imported."

cantor1891 : ComplexitySource
cantor1891 =
  complexitySource
    "Georg Cantor"
    "Über eine elementare Frage der Mannigfaltigkeitslehre"
    1891
    "Jahresbericht der Deutschen Mathematiker-Vereinigung 1, 75--78"
    "bibliographic:Cantor-1891-JDMV-1-75-78"
    diagonalCardinality
    stableBookBibliography
    "Calibrates diagonal non-enumerability only.  DASHI's Boolean-function quotation no-go is a local constructive specialization and does not by itself constrain the countable polynomial-time machine class."

record DiagonalizationSourceBoundary : Set where
  constructor diagonalization-source-boundary
  field
    sourcesAreCalibrationNotProofCertificates : Bool
    sourcesAreCalibrationNotProofCertificatesIsTrue :
      sourcesAreCalibrationNotProofCertificates ≡ true

    classicalSelfReferenceProvidesResourceBoundedSATFixedPoint : Bool
    classicalSelfReferenceProvidesResourceBoundedSATFixedPointIsFalse :
      classicalSelfReferenceProvidesResourceBoundedSATFixedPoint ≡ false

    modernLowerBoundContextPromotedToPNotEqualsNP : Bool
    modernLowerBoundContextPromotedToPNotEqualsNPIsFalse :
      modernLowerBoundContextPromotedToPNotEqualsNP ≡ false

canonicalDiagonalizationSourceBoundary : DiagonalizationSourceBoundary
canonicalDiagonalizationSourceBoundary =
  diagonalization-source-boundary
    true refl
    false refl
    false refl
