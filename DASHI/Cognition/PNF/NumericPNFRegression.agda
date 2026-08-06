module DASHI.Cognition.PNF.NumericPNFRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.BoundedMDLPlanner
open import DASHI.Cognition.PNF.ComplexityArithmetic
open import DASHI.Cognition.PNF.DirectDemandLookup
open import DASHI.Cognition.PNF.NumericAuthority
open import DASHI.Cognition.PNF.NumericHyperfabric
open import DASHI.Cognition.PNF.NumericPNFCompilation
open import DASHI.Cognition.PNF.SpacyNumericProjection

data ExampleDigest : Set where
  digestA digestB : ExampleDigest

exampleNumericSymbol : NumericSymbol ExampleDigest
exampleNumericSymbol =
  numericSymbol lemmaSymbol (symbolId (suc zero)) digestA

exampleRootHeadCommits :
  commitHead
    (projectHead
      (tokenId (suc zero))
      declaredSelfHead
      missingHead)
  ≡ just rootCommit
exampleRootHeadCommits = refl

exampleMissingDependentHeadRejected :
  commitHead
    (projectHead
      (tokenId (suc zero))
      (declaredHeadAt zero (suc zero))
      missingHead)
  ≡ nothing
exampleMissingDependentHeadRejected = refl

examplePromotionEvidence : PromotionEvidence
examplePromotionEvidence =
  promotionEvidence
    (suc zero)
    (suc zero)
    zero
    (suc zero)
    zero
    zero
    zero

examplePromotionWitness : PromotionWitness examplePromotionEvidence
examplePromotionWitness = promotionWitness (s≤s z≤n)

plannerEvaluationFormula : ∀ n window beam →
  evaluationCapacity n window beam ≡ n *ᶜ (window *ᶜ beam)
plannerEvaluationFormula = evaluationCapacityClosed

plannerMemoryFormula : ∀ n beam →
  backpointerCellCapacity n beam ≡ n *ᶜ beam
plannerMemoryFormula = backpointerCellCapacityClosed

copiedPlannerCannotClaimCanonicalLinearStorage : ∀ n window beam →
  copiedFullPaths ≡
    pathStorage (canonicalPlannerComplexityCertificate n window beam) → ⊥
copiedPlannerCannotClaimCanonicalLinearStorage =
  copiedImplementationCannotUseCanonicalCertificate

exampleProbe : ProbeContract
exampleProbe = probeContract zero zero z≤n

exampleCandidates : CandidateBound
exampleCandidates = candidateBound zero zero z≤n

exampleValidation : NearestCommonInterfaceValidation
exampleValidation =
  nearestCommonInterfaceValidation
    (interfaceId zero)
    (interfaceId zero)
    (interfaceId zero)
    zero

exampleDirectLookupCertificate : DirectLookupCertificate
exampleDirectLookupCertificate =
  directLookupCertificate
    exampleProbe
    exampleCandidates
    exampleValidation
    zero
    refl

openCoverageHasNoWorldPublication : WorldPublication openCoverage → ⊥
openCoverageHasNoWorldPublication = openCoverageCannotPublish

openCoverageHasNoStrictPublication : StrictPublication openCoverage → ⊥
openCoverageHasNoStrictPublication = openStrictPublicationImpossible
