module DASHI.Law.SensibLawWoogarooSignedPredicateFibreTreeExact where

------------------------------------------------------------------------
-- Exact receiver: proposition polarity (-P / unknown / +P), with
-- Belnap/Dunn both/neither kept in the dependent evidence fibre.
-- Source owner: ClaimIndexedEvidencePolarityExact (Belnap 1977, Dunn 1976).
-- Sign antipode is NOT automatically a logical-negation certificate:
-- only an explicitly SAME proposition/scope may name notF(P).
--
-- Hierarchy owner: RecursiveFibreTower, TypedHyperfabricCore,
-- TriadicPAdicCylinderExact, RequestedFibreInvolutionFoldExact,
-- TrialecticThreeCellCarryDepthExact and the existing seven-ground
-- Woogaroo dialectical synthesis. No face mediation or real evidence
-- receipt is created by the carrier, tree, or p-adic projection.
-- Previous Ibrahim/Monster3B proof ownership and legal sources retained.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (_++_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Algebra.ClaimIndexedEvidencePolarityExact as Indexed
import DASHI.Algebra.BalancedTernaryOppositionEvidenceBridgeExact as Antipode
import DASHI.Core.EpistemicSuspensionExact as Suspension
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as PNF
import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Cognition.PNF.HypercomplexRequestedFractranComponentExact as Fine
import DASHI.Cognition.PNF.RequestedFibreInvolutionFoldExact as Fold
import DASHI.Codec.TriadicPAdicCylinderExact as Cylinder
import DASHI.Reasoning.TrialecticThreeCellCarryDepthExact as Carry
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell
import DASHI.Law.SensibLawWoogarooAdversarialLogicalTests20261028Exact as Logic
import DASHI.Law.SensibLawWoogarooDialecticTrialecticSynthesis20261028Exact as Synthesis
import DASHI.Law.SensibLawWoogarooEPBC8575PleadableGroundsPrecedentCut20261028Exact as Ground

------------------------------------------------------------------------
-- Nine claim-indexed atoms, not nine globally true/false numbers.
-- Each has a positive P, an explicit formal negative notF(P), and
-- separate support provenance. Nested predicates add another fibre.
------------------------------------------------------------------------

data PredicateSlot : Set where
  applicableLaw allegedDefect legalMateriality : PredicateSlot
  claimedCompliance habitatConcern causalConnection : PredicateSlot
  reviewedOriginal sameProjectStage independentMediation : PredicateSlot

slotName : PredicateSlot → String
slotName applicableLaw = "applicable-law"
slotName allegedDefect = "alleged-defect"
slotName legalMateriality = "materiality"
slotName claimedCompliance = "claimed-compliance"
slotName habitatConcern = "habitat-concern"
slotName causalConnection = "causal-connection"
slotName reviewedOriginal = "reviewed-original"
slotName sameProjectStage = "same-project-stage"
slotName independentMediation = "independent-mediation"

baseProposition : Ground.Ground → PredicateSlot → PNF.Formula
baseProposition g slot =
  PNF.atom (slotName slot) (PNF.literalTerm (Logic.groundKey g) ∷ [])

negativeProposition : Ground.Ground → PredicateSlot → PNF.Formula
negativeProposition g slot = PNF.notF (baseProposition g slot)

-- This is an explicit syntax-level negation of SAME proposition and ground,
-- not an antipodal geometry-derived negation or external legal conclusion.
data SupportClass : Set where
  neitherReported positiveOnly negativeOnly bothReported : SupportClass

record SignedClaimEvidence : Set where
  constructor claim-evidence
  field
    positiveSupported : Bool
    negativeSupported : Bool
    originalReferences : List String
open SignedClaimEvidence public

classifySupport : SignedClaimEvidence → SupportClass
classifySupport (claim-evidence false false _) = neitherReported
classifySupport (claim-evidence true false _) = positiveOnly
classifySupport (claim-evidence false true _) = negativeOnly
classifySupport (claim-evidence true true _) = bothReported

coarsePolarity : SignedClaimEvidence → SSP.SSPTrit
coarsePolarity evidence with classifySupport evidence
... | neitherReported = SSP.sspZero
... | positiveOnly = SSP.sspPosOne
... | negativeOnly = SSP.sspNegOne
... | bothReported = SSP.sspZero

-- This is the existing four-view carrier, NOT two exclusive Booleans.
polarAssessment : SignedClaimEvidence → Four.PolarAssessment
polarAssessment evidence =
  Four.assess (positiveSupported evidence) (negativeSupported evidence)

mergeSamePredicate : SignedClaimEvidence → SignedClaimEvidence →
  SignedClaimEvidence
mergeSamePredicate left right with
  Indexed.mergePolarity (polarAssessment left) (polarAssessment right)
... | Four.assess pos neg =
  claim-evidence pos neg
    (originalReferences left ++ originalReferences right)

unknownEvidence : SignedClaimEvidence
unknownEvidence = claim-evidence false false []

negativeEvidence : SignedClaimEvidence
negativeEvidence = claim-evidence false true []

positiveEvidence : SignedClaimEvidence
positiveEvidence = claim-evidence true false []

contradictoryEvidence : SignedClaimEvidence
contradictoryEvidence = claim-evidence true true []

negativeReallyIsMinus :
  coarsePolarity negativeEvidence ≡ SSP.sspNegOne
negativeReallyIsMinus = refl

positiveReallyIsPlus :
  coarsePolarity positiveEvidence ≡ SSP.sspPosOne
positiveReallyIsPlus = refl

unknownIsCentre :
  coarsePolarity unknownEvidence ≡ SSP.sspZero
unknownIsCentre = refl

bothIsAlsoCentre :
  coarsePolarity contradictoryEvidence ≡ SSP.sspZero
bothIsAlsoCentre = refl

centreDoesNotDetermineKnowledgeState :
  classifySupport unknownEvidence
    ≡ classifySupport contradictoryEvidence → ⊥
centreDoesNotDetermineKnowledgeState ()

negativeDoesNotMeanMissing :
  coarsePolarity negativeEvidence ≡ coarsePolarity unknownEvidence → ⊥
negativeDoesNotMeanMissing ()

positiveDoesNotMeanNegative :
  coarsePolarity positiveEvidence ≡ coarsePolarity negativeEvidence → ⊥
positiveDoesNotMeanNegative ()

-- The historical epistemic reject/accept/refine rule is a separate
-- *decision policy*. It is not itself a certificate that notF(P) is true.
suspensionBoundary : Suspension.EpistemicSuspensionBoundary
suspensionBoundary = Suspension.canonicalEpistemicSuspensionBoundary

strictAntipodeBoundary : Antipode.BalancedTernaryOppositionEvidenceBoundary
strictAntipodeBoundary = Antipode.canonicalBalancedTernaryOppositionEvidenceBoundary

------------------------------------------------------------------------
-- Full nine-atom signed 3×3×3 representation. Three-valued observations
-- cannot erase finer 4-valued evidence; the source stays in the fibre.
------------------------------------------------------------------------

record SignedCaseFibre (g : Ground.Ground) : Set where
  constructor signed-case-fibre
  field
    at : PredicateSlot → SignedClaimEvidence
    sourceScopeRef : String
    caseProvenanceRefs : List String
open SignedCaseFibre public

signedApplicantCube : ∀ {g} → SignedCaseFibre g →
  Fabric.Ternary27Point
signedApplicantCube f =
  Fabric.ternary27Point
    (coarsePolarity (at f applicableLaw))
    (coarsePolarity (at f allegedDefect))
    (coarsePolarity (at f legalMateriality))

signedRespondentCube : ∀ {g} → SignedCaseFibre g →
  Fabric.Ternary27Point
signedRespondentCube f =
  Fabric.ternary27Point
    (coarsePolarity (at f claimedCompliance))
    (coarsePolarity (at f habitatConcern))
    (coarsePolarity (at f causalConnection))

signedIndependentCube : ∀ {g} → SignedCaseFibre g →
  Fabric.Ternary27Point
signedIndependentCube f =
  Fabric.ternary27Point
    (coarsePolarity (at f reviewedOriginal))
    (coarsePolarity (at f sameProjectStage))
    (coarsePolarity (at f independentMediation))

signedFabric : ∀ {g} → SignedCaseFibre g →
  Fabric.TernaryHyperformalPoint
signedFabric f = Fabric.ternaryHyperformalPoint
  (signedApplicantCube f)
  (signedRespondentCube f)
  (signedIndependentCube f)

-- Full 4-way source fibre is NOT recoverable from the coarse T^9 chart.
-- The collision is exact: both and neither have the same coarse sign.
noUniversalClassFromCoarse :
  (decoder : SSP.SSPTrit → SupportClass) →
  ((e : SignedClaimEvidence) →
    decoder (coarsePolarity e) ≡ classifySupport e) → ⊥
noUniversalClassFromCoarse decoder exact =
  centreDoesNotDetermineKnowledgeState
    (trans (sym (exact unknownEvidence)) (exact contradictoryEvidence))

unpaidFibre : (g : Ground.Ground) → SignedCaseFibre g
unpaidFibre g =
  signed-case-fibre (λ _ → unknownEvidence)
    (Logic.groundKey g) []

unpaidAllNeutral : (g : Ground.Ground) →
  signedFabric (unpaidFibre g)
  ≡ Fabric.ternaryHyperformalPoint
      Fabric.origin Fabric.origin Fabric.origin
unpaidAllNeutral g = refl

------------------------------------------------------------------------
-- Tree of context-indexed decisions: branches contain MORE predicates,
-- not a forced conclusion at a fixed cube coordinate. Every tree node
-- retains its full fine evidence; merely matching signs is insufficient.
------------------------------------------------------------------------

data PredicateDecisionTree (g : Ground.Ground) : Set where
  predicateLeaf : PredicateSlot → SignedClaimEvidence →
    PredicateDecisionTree g
  predicateBranch : PredicateSlot → SignedClaimEvidence →
    List (PredicateDecisionTree g) → PredicateDecisionTree g

rootEvidence : ∀ {g} → PredicateDecisionTree g → SignedClaimEvidence
rootEvidence (predicateLeaf slot evidence) = evidence
rootEvidence (predicateBranch slot evidence children) = evidence

nestedUnknownTree : (g : Ground.Ground) → PredicateDecisionTree g
nestedUnknownTree g =
  predicateBranch applicableLaw unknownEvidence
    (predicateBranch allegedDefect unknownEvidence
      (predicateLeaf legalMateriality unknownEvidence ∷
       predicateLeaf habitatConcern unknownEvidence ∷ []) ∷
     predicateBranch reviewedOriginal unknownEvidence
      (predicateLeaf sameProjectStage unknownEvidence ∷
       predicateLeaf independentMediation unknownEvidence ∷ []) ∷ [])

-- General typed hyperfabric receiver: the ground-indexed stalk is the
-- whole signed 9-atom fibre, not just a coarse trit. The identity incidence
-- avoids spurious cross-ground merges. A cross-scope comparison requires
-- a separate provenance-and-transport witness from its actual owner.
sameGroundHyperfabric :
  Hyperfabric.TypedHyperfabric Ground.Ground Ground.Ground
sameGroundHyperfabric = record
  { vertexStalk = SignedCaseFibre
  ; edgeStalk = SignedCaseFibre
  ; incidence = _≡_
  ; restrict = λ refl value → value
  ; edgeProvenance = λ g → Logic.groundKey g ∷ []
  ; edgeSalience = λ _ → 0
  ; fabricLabel = "woogaroo:signed-predicate:same-ground-only"
  }

unpaidCompatibleSection :
  Hyperfabric.GlobalSection sameGroundHyperfabric
unpaidCompatibleSection = record
  { vertexValue = unpaidFibre
  ; edgeValue = unpaidFibre
  ; compatible = λ refl → refl
  ; sectionReceipt = "hypothetical:no-originals-paid"
  }

------------------------------------------------------------------------
-- Tree-depth observation and 3-adic cylinder are separate receivers.
-- A requested sign stream records a PARTICULAR chosen branch/history.
-- This is not a universal flattening of an arbitrary predicate tree.
------------------------------------------------------------------------

toAlgebraTrit : SSP.SSPTrit → Trit.Trit
toAlgebraTrit SSP.sspNegOne = Trit.neg
toAlgebraTrit SSP.sspZero = Trit.zer
toAlgebraTrit SSP.sspPosOne = Trit.pos

signedBranchHistory :
  (Nat → SignedClaimEvidence) → Cylinder.ResidualStream
signedBranchHistory history n =
  toAlgebraTrit (coarsePolarity (history n))

-- Reuse existing exact prefix/refinement compatibility, not new p-adic
-- physics or a claim that the branch was observed from real litigation.
branchCylinderCompatible :
  (k : Nat) (history : Nat → SignedClaimEvidence) →
  Cylinder.refineKernel k
    (Cylinder.projectStream (suc k) (signedBranchHistory history))
  ≡ Cylinder.projectStream k (signedBranchHistory history)
branchCylinderCompatible k history =
  Cylinder.projectCompatible k (signedBranchHistory history)

recursiveFibreOwner : Tower.FibreTower
recursiveFibreOwner = Tower.recursivePhaseTower

hypercomplexCoarseBoundary : Fine.HypercomplexComponentBoundary
hypercomplexCoarseBoundary = Fine.canonicalHypercomplexComponentBoundary

coarseZeroIsNotNecessarilyFineFixedPoint :
  Fold.RequestedFibreFoldBoundary
coarseZeroIsNotNecessarilyFineFixedPoint =
  Fold.canonicalRequestedFibreFoldBoundary

conditionalCarryOwner : Carry.TrialecticThreeCellCarryDepthBoundary
conditionalCarryOwner = Carry.canonicalTrialecticThreeCellCarryDepthBoundary

------------------------------------------------------------------------
-- Synthesis: a signed +P requests a defeater; signed -P requests the
-- paired counter-defeater. 0 requires original acquisition; both retains
-- contradiction. The independent face remains unfilled in EVERY case.
-- The review flag here is a synthetic assumption; not a source receipt.
------------------------------------------------------------------------

focus : SignedClaimEvidence → Bool → Synthesis.WoogarooSynthesisKind
focus evidence reviewed with classifySupport evidence | reviewed
... | bothReported | _ = Synthesis.reconcileOpposingSourceAssertions
... | neitherReported | _ = Synthesis.seekOriginals
... | positiveOnly | true = Synthesis.applicantHypothesisForDefeaterSearch
... | positiveOnly | false = Synthesis.seekOriginals
... | negativeOnly | true = Synthesis.respondentHypothesisForCounterDefeaterSearch
... | negativeOnly | false = Synthesis.seekOriginals

-- MULTIPLE nested predicates must jointly satisfy the case-level
-- candidate antecedent. This is not a legal materiality theorem: all
-- inputs remain explicitly stipulated, same-ground and same-scope.
orB : Bool → Bool → Bool
orB true _ = true
orB false x = x

andB : Bool → Bool → Bool
andB true x = x
andB false _ = false

positiveOnlyEvidence : SignedClaimEvidence → Bool
positiveOnlyEvidence evidence with classifySupport evidence
... | positiveOnly = true
... | _ = false

negativeOnlyEvidence : SignedClaimEvidence → Bool
negativeOnlyEvidence evidence with classifySupport evidence
... | negativeOnly = true
... | _ = false

notPositiveOnlyEvidence : SignedClaimEvidence → Bool
notPositiveOnlyEvidence evidence with classifySupport evidence
... | positiveOnly = false
... | _ = true

bothEvidence : SignedClaimEvidence → Bool
bothEvidence evidence with classifySupport evidence
... | bothReported = true
... | _ = false

allPredicateSlots : List PredicateSlot
allPredicateSlots =
  applicableLaw ∷ allegedDefect ∷ legalMateriality ∷
  claimedCompliance ∷ habitatConcern ∷ causalConnection ∷
  reviewedOriginal ∷ sameProjectStage ∷ independentMediation ∷ []

hasAnyConflict : ∀ {g} → SignedCaseFibre g → Bool
hasAnyConflict f = go allPredicateSlots
  where
    go : List PredicateSlot → Bool
    go [] = false
    go (slot ∷ more) = orB (bothEvidence (at f slot)) (go more)

sharedSourceGates : ∀ {g} → SignedCaseFibre g → Bool
sharedSourceGates f =
  andB (positiveOnlyEvidence (at f applicableLaw))
    (andB (positiveOnlyEvidence (at f reviewedOriginal))
      (positiveOnlyEvidence (at f sameProjectStage)))

applicantPredicateConjunction : ∀ {g} → SignedCaseFibre g → Bool
applicantPredicateConjunction f =
  andB (positiveOnlyEvidence (at f allegedDefect))
    (andB (positiveOnlyEvidence (at f legalMateriality))
      (notPositiveOnlyEvidence (at f claimedCompliance)))

respondentPredicateConjunction : ∀ {g} → SignedCaseFibre g → Bool
respondentPredicateConjunction f =
  andB (negativeOnlyEvidence (at f allegedDefect))
    (positiveOnlyEvidence (at f claimedCompliance))

signedFibreFocus : ∀ {g} → SignedCaseFibre g →
  Bool → Synthesis.WoogarooSynthesisKind
signedFibreFocus f reviewed with
  hasAnyConflict f | reviewed | sharedSourceGates f |
  applicantPredicateConjunction f | respondentPredicateConjunction f
... | true  | _     | _     | _     | _     =
  Synthesis.reconcileOpposingSourceAssertions
... | false | false | _     | _     | _     =
  Synthesis.seekOriginals
... | false | true  | false | _     | _     =
  Synthesis.seekOriginals
... | false | true  | true  | true  | _     =
  Synthesis.applicantHypothesisForDefeaterSearch
... | false | true  | true  | false | true  =
  Synthesis.respondentHypothesisForCounterDefeaterSearch
... | false | true  | true  | false | false =
  Synthesis.seekOriginals

-- A one-atom sign does NOT force any candidate branch if other
-- antecedents remain unknown. This differs from the local/leaf focus.
singleNegativeDoesNotForceCaseSynthesis :
  signedFibreFocus (signed-case-fibre
    (λ slot → negativeEvidence) "hypothetical" []) false
  ≡ Synthesis.seekOriginals
singleNegativeDoesNotForceCaseSynthesis = refl

-- A full consistent conditional case can route one branch; even that
-- does not create a source receipt or determine the trialectic face.
respondentExample : PredicateSlot → SignedClaimEvidence
respondentExample applicableLaw = positiveEvidence
respondentExample allegedDefect = negativeEvidence
respondentExample claimedCompliance = positiveEvidence
respondentExample reviewedOriginal = positiveEvidence
respondentExample sameProjectStage = positiveEvidence
respondentExample _ = unknownEvidence

respondentExampleFibre : SignedCaseFibre Ground.approvedAdviceOmitted
respondentExampleFibre = signed-case-fibre respondentExample "hypothetical" []

multiPredicateRespondentBranch :
  signedFibreFocus respondentExampleFibre true
  ≡ Synthesis.respondentHypothesisForCounterDefeaterSearch
multiPredicateRespondentBranch = refl

applicantExample : PredicateSlot → SignedClaimEvidence
applicantExample applicableLaw = positiveEvidence
applicantExample allegedDefect = positiveEvidence
applicantExample legalMateriality = positiveEvidence
applicantExample claimedCompliance = negativeEvidence
applicantExample reviewedOriginal = positiveEvidence
applicantExample sameProjectStage = positiveEvidence
applicantExample _ = unknownEvidence

applicantExampleFibre : SignedCaseFibre Ground.approvedAdviceOmitted
applicantExampleFibre = signed-case-fibre applicantExample "hypothetical" []

multiPredicateApplicantBranch :
  signedFibreFocus applicantExampleFibre true
  ≡ Synthesis.applicantHypothesisForDefeaterSearch
multiPredicateApplicantBranch = refl

unpaidFibreNeverCompletesLegalBridge :
  (g : Ground.Ground) →
  signedFibreFocus (unpaidFibre g) true ≡ Synthesis.seekOriginals
unpaidFibreNeverCompletesLegalBridge g = refl

negativeCandidateRoutesToCountercase :
  focus negativeEvidence true
    ≡ Synthesis.respondentHypothesisForCounterDefeaterSearch
negativeCandidateRoutesToCountercase = refl

positiveCandidateRoutesToDefeater :
  focus positiveEvidence true
    ≡ Synthesis.applicantHypothesisForDefeaterSearch
positiveCandidateRoutesToDefeater = refl

missingEvidenceRequestsRefinement :
  focus unknownEvidence true ≡ Synthesis.seekOriginals
missingEvidenceRequestsRefinement = refl

contradictionPreservedWhenReviewed :
  focus contradictoryEvidence true
    ≡ Synthesis.reconcileOpposingSourceAssertions
contradictionPreservedWhenReviewed = refl

unreviewedNegativeDoesNotBecomeJudgment :
  focus negativeEvidence false ≡ Synthesis.seekOriginals
unreviewedNegativeDoesNotBecomeJudgment = refl

data ActualSourcePaymentFromCoarseSign : Set where
data TrialecticFaceFromTreeShape : Set where

noSourcePaymentFromSign : ActualSourcePaymentFromCoarseSign → ⊥
noSourcePaymentFromSign ()

noFaceFromTree : TrialecticFaceFromTreeShape → ⊥
noFaceFromTree ()
