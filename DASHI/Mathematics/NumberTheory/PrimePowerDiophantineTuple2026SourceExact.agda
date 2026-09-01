module DASHI.Mathematics.NumberTheory.PrimePowerDiophantineTuple2026SourceExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- SOURCE ATTRIBUTION / CLAIM BOUNDARY
--
-- Primary mathematical source:
--   Andrej Dujella, "Prime-power Diophantine tuples", 2026 preprint,
--   13 pages.  No DOI is asserted here because none has been recovered.
--   Canonical author publication surface:
--     https://web.math.pmf.unizg.hr/~duje/papers1.html
--
-- Problem-source surface:
--   Andrej Dujella, "Open problems on Diophantine m-tuples and elliptic
--   curves", online supplement, current supplied version dated 2026-08-30,
--   Problem 5.6.
--     https://web.math.pmf.unizg.hr/~duje/pdf/open2.pdf
--
-- Historical input explicitly cited by the preprint:
--   Andrej Dujella and Florian Luca,
--   "Diophantine m-tuples for primes",
--   International Mathematics Research Notices 2005, no. 47, 2913--2940.
--
-- The theorem/proof-node graph below is a DASHI reconstruction of the source
-- dependency architecture.  It is NOT attributed back to Dujella as a formal
-- theorem graph, and it is NOT an Agda reconstruction of the full proof.
--
-- In particular:
--   source theorem statement
--   != DASHI dependency reconstruction
--   != Appendix-A external numerical replay
--   != Agda proof of the mathematical theorem
--   != independent review / publication authority.
------------------------------------------------------------------------

data SourceRole : Set where
  primePowerPreprint : SourceRole
  openProblemSupplement : SourceRole
  priorPrimeGapArgument : SourceRole
  priorBoundedNTheorem : SourceRole
  priorLargeElementEstimate : SourceRole
  appendixCertificateDescription : SourceRole
  ancillaryPythonCertificate : SourceRole

data SourceCitation : Set where
  dujellaPrimePower2026 : SourceCitation
  dujellaOpenProblems2026 : SourceCitation
  dujellaLuca2005 : SourceCitation
  dujella2002LargeElement : SourceCitation
  dujella2004BoundedN : SourceCitation
  heTogbeZiegler2019 : SourceCitation
  bonciocatCipuMignotte2022 : SourceCitation

sourceAuthor : SourceCitation → String
sourceAuthor dujellaPrimePower2026 = "Andrej Dujella"
sourceAuthor dujellaOpenProblems2026 = "Andrej Dujella"
sourceAuthor dujellaLuca2005 = "Andrej Dujella; Florian Luca"
sourceAuthor dujella2002LargeElement = "Andrej Dujella"
sourceAuthor dujella2004BoundedN = "Andrej Dujella"
sourceAuthor heTogbeZiegler2019 = "B. He; A. Togbe; V. Ziegler"
sourceAuthor bonciocatCipuMignotte2022 = "N. C. Bonciocat; M. Cipu; M. Mignotte"

sourceTitle : SourceCitation → String
sourceTitle dujellaPrimePower2026 = "Prime-power Diophantine tuples"
sourceTitle dujellaOpenProblems2026 = "Open problems on Diophantine m-tuples and elliptic curves"
sourceTitle dujellaLuca2005 = "Diophantine m-tuples for primes"
sourceTitle dujella2002LargeElement = "On the size of Diophantine m-tuples"
sourceTitle dujella2004BoundedN = "Bounds for the size of sets with the property D(n)"
sourceTitle heTogbeZiegler2019 = "There is no Diophantine quintuple"
sourceTitle bonciocatCipuMignotte2022 = "There is no Diophantine D(-1)-quadruple"

------------------------------------------------------------------------
-- Exact source theorem surfaces.
------------------------------------------------------------------------

pow2 : Nat → Nat
pow2 zero = 1
pow2 (suc n) = 2 * pow2 n

reducedPrimePowerExponent : Nat
reducedPrimePowerExponent = 121

positivePrimeSquareExponent : Nat
positivePrimeSquareExponent = 122

arbitraryIntegerPrimeSquareExponent : Nat
arbitraryIntegerPrimeSquareExponent = 123

data TheoremRole : Set where
  reducedPrimePowerBound : TheoremRole
  positivePrimeParameterBound : TheoremRole
  positivePrimeSquareBound : TheoremRole
  arbitraryIntegerPrimeSquareBound : TheoremRole
  primePowerRecurrence : TheoremRole
  uniformLinearInExponentBound : TheoremRole

record SourceTheoremSurface : Set where
  constructor theoremSurface
  field
    source : SourceCitation
    role : TheoremRole
    locator : String
    sourceStatementRecovered : Bool

open SourceTheoremSurface public

reducedPrimePowerTheorem : SourceTheoremSurface
reducedPrimePowerTheorem =
  theoremSurface dujellaPrimePower2026 reducedPrimePowerBound
    "Theorem 1.1: positive reduced D(±p^r)-tuples have < 2^121 elements"
    true

primeSquareCorollary : SourceTheoremSurface
primeSquareCorollary =
  theoremSurface dujellaPrimePower2026 arbitraryIntegerPrimeSquareBound
    "Corollary 1.3: arbitrary nonzero-integer D(p^2)-tuples have < 2^123 elements"
    true

problem56Surface : SourceTheoremSurface
problem56Surface =
  theoremSurface dujellaOpenProblems2026 arbitraryIntegerPrimeSquareBound
    "Problem 5.6, updated 2026-08-30"
    true

------------------------------------------------------------------------
-- Source proof architecture recovered BIDI from the final consumer.
------------------------------------------------------------------------

data ProofNode : Set where
  preliminaryLowerBound : ProofNode
  primePowerFactorization : ProofNode
  easyBranchGap : ProofNode
  fullModulusCongruence : ProofNode
  negativeSignHardBranch : ProofNode
  toricEliminant : ProofNode
  jacobianNonvanishingCertificate : ProofNode
  polynomialNonvanishing : ProofNode
  uniformGapPrinciple : ProofNode
  boundedNInput : ProofNode
  largeElementInput : ProofNode
  reducedPrimePowerConclusion : ProofNode
  divisibleSubtupleRecurrence : ProofNode
  terminalDPlusMinusOneInput : ProofNode
  primeSquareConclusion : ProofNode

data DependsOn : ProofNode → ProofNode → Set where
  easyUsesLower : DependsOn easyBranchGap preliminaryLowerBound
  easyUsesFactorization : DependsOn easyBranchGap primePowerFactorization
  congruenceUsesFactorization : DependsOn fullModulusCongruence primePowerFactorization
  hardNegativeUsesCongruence : DependsOn negativeSignHardBranch fullModulusCongruence
  toricUsesCongruence : DependsOn toricEliminant fullModulusCongruence
  polynomialUsesToric : DependsOn polynomialNonvanishing toricEliminant
  polynomialUsesJacobian : DependsOn polynomialNonvanishing jacobianNonvanishingCertificate
  gapUsesEasy : DependsOn uniformGapPrinciple easyBranchGap
  gapUsesHardNegative : DependsOn uniformGapPrinciple negativeSignHardBranch
  gapUsesPolynomial : DependsOn uniformGapPrinciple polynomialNonvanishing
  reducedUsesGap : DependsOn reducedPrimePowerConclusion uniformGapPrinciple
  reducedUsesBoundedN : DependsOn reducedPrimePowerConclusion boundedNInput
  reducedUsesLargeElement : DependsOn reducedPrimePowerConclusion largeElementInput
  recurrenceUsesReduced : DependsOn divisibleSubtupleRecurrence reducedPrimePowerConclusion
  primeSquareUsesRecurrence : DependsOn primeSquareConclusion divisibleSubtupleRecurrence
  primeSquareUsesTerminal : DependsOn primeSquareConclusion terminalDPlusMinusOneInput

------------------------------------------------------------------------
-- Crucial correction in the source: toric, not naive homogeneous elimination.
------------------------------------------------------------------------

data EliminationMethod : Set where
  unsaturatedHomogeneousElimination : EliminationMethod
  toricMonomialSaturatedElimination : EliminationMethod

sourceUsesToricElimination : EliminationMethod
sourceUsesToricElimination = toricMonomialSaturatedElimination

unsaturatedIsNotToric :
  unsaturatedHomogeneousElimination ≡ toricMonomialSaturatedElimination → ⊥
unsaturatedIsNotToric ()

------------------------------------------------------------------------
-- Appendix-A numerical certificate boundary.
------------------------------------------------------------------------

data CertificateStage : Set where
  sourceDescribedExactRationalIntervalCertificate : CertificateStage
  ancillaryPythonProgramRecovered : CertificateStage
  independentlyReplayedExternally : CertificateStage
  replayedInsideAgda : CertificateStage

sourceAppendixCertificateStage : CertificateStage
sourceAppendixCertificateStage = sourceDescribedExactRationalIntervalCertificate

sourceDescriptionIsNotAgdaReplay :
  sourceDescribedExactRationalIntervalCertificate ≡ replayedInsideAgda → ⊥
sourceDescriptionIsNotAgdaReplay ()

jacobianPositiveSignLowerDigits : String
jacobianPositiveSignLowerDigits = "-1.22625271490038e-31"

jacobianPositiveSignUpperDigits : String
jacobianPositiveSignUpperDigits = "-1.22625271490037e-31"

jacobianNegativeSignLowerDigits : String
jacobianNegativeSignLowerDigits = "2.9335784988635907e-29"

jacobianNegativeSignUpperDigits : String
jacobianNegativeSignUpperDigits = "2.9335784988635908e-29"

------------------------------------------------------------------------
-- AI attribution: preserve the two supplied source surfaces without merging
-- their labels or strengthening the preprint's attribution.
------------------------------------------------------------------------

data ModelLabelSurface : Set where
  chatGPT56Sol : ModelLabelSurface
  chatGPT56SolPlus : ModelLabelSurface

manuscriptModelLabel : ModelLabelSurface
manuscriptModelLabel = chatGPT56Sol

openProblemModelLabel : ModelLabelSurface
openProblemModelLabel = chatGPT56SolPlus

sourceModelLabelsDiffer : manuscriptModelLabel ≡ openProblemModelLabel → ⊥
sourceModelLabelsDiffer ()

data AIContributionSurface : Set where
  useAcknowledged : AIContributionSurface
  discussionOfEarlierManuscriptVersions : AIContributionSurface
  attemptsAtEliminantNonvanishing : AIContributionSurface
  ledToToricEliminationLemma : AIContributionSurface
  authorOwnsProofVerificationAndPresentation : AIContributionSurface

record ManuscriptAIAcknowledgement : Set where
  constructor aiAcknowledgement
  field
    model : ModelLabelSurface
    generalUse : AIContributionSurface
    earlierVersionDiscussion : AIContributionSurface
    eliminantDiscussion : AIContributionSurface
    resultingLemmaAttribution : AIContributionSurface
    responsibilityBoundary : AIContributionSurface

manuscriptAIAcknowledgement : ManuscriptAIAcknowledgement
manuscriptAIAcknowledgement =
  aiAcknowledgement
    chatGPT56Sol
    useAcknowledged
    discussionOfEarlierManuscriptVersions
    attemptsAtEliminantNonvanishing
    ledToToricEliminationLemma
    authorOwnsProofVerificationAndPresentation

------------------------------------------------------------------------
-- Current exact repo cut.
------------------------------------------------------------------------

manuscriptRecovered : Bool
manuscriptRecovered = true

exactProblem56StatementRecovered : Bool
exactProblem56StatementRecovered = true

proofDependencyGraphRecovered : Bool
proofDependencyGraphRecovered = true

appendixReplayAlgorithmDescribedBySource : Bool
appendixReplayAlgorithmDescribedBySource = true

ancillaryPythonProgramRecoveredIntoRepo : Bool
ancillaryPythonProgramRecoveredIntoRepo = false

fullDujellaProofReconstructedInAgda : Bool
fullDujellaProofReconstructedInAgda = false

independentlyReviewedByDASHI : Bool
independentlyReviewedByDASHI = false

manuscriptRecoveredIsTrue : manuscriptRecovered ≡ true
manuscriptRecoveredIsTrue = refl

proofDependencyGraphRecoveredIsTrue : proofDependencyGraphRecovered ≡ true
proofDependencyGraphRecoveredIsTrue = refl

fullDujellaProofReconstructedInAgdaIsFalse : fullDujellaProofReconstructedInAgda ≡ false
fullDujellaProofReconstructedInAgdaIsFalse = refl
