module DASHI.Mathematics.Complexity.Karp21SparseEndpointConsistencySoundExact where

------------------------------------------------------------------------
-- N21: CLOSE FINITE SPARSE-CERTIFICATE SEMANTIC SOUNDNESS.
--
-- Earlier SparseEndpointCutCertificateExact has the actual 2m-bit
-- edge-endpoint code, signed cut verifier and repeated-vertex checker.
-- We now prove that an arbitrary ACCEPTED consistent local code
-- extends to a genuine full Vec Bool n graph cut, without assuming
-- that the new sparse code arose from an earlier full assignment.
--
-- Mathematical construction: assign each occurring vertex the label
-- of its first listed occurrence. Boolean pairwise consistency makes
-- all repeated occurrences equal. Assign false to isolated vertices.
-- This global extension has the SAME signed edge score and threshold.
--
-- Consequently Karp's original finite WeightedMaxCutYES has an exact
-- bidirectional iff to the actual 2m-bit word witness verifier.
--
-- IMPORTANT RESOURCE BOUNDARY: constructing a full Vec Bool n is
-- ONLY IN THE MATHEMATICAL SOUNDNESS PROOF. The executable sparse
-- verifier does not compute it, nor allocate O(n) data. An enormous
-- binary n and m=1 still have an O(m)-entry certificate/consistency
-- checker. Canonical signed GraphWord and true polynomial tape clock
-- remain separate, unproven conditions for PR.InNP.
--
-- Original mathematical reduction: Karp 1972. The existing DASHI
-- sparse endpoint verifier, source-signed graph and Fin equality
-- owners are reused rather than cloned.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Bool.Base using (T)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import Data.Fin.Base as Fin
import Data.Fin.Properties as FinP
import Data.Vec.Base as Vec
import DASHI.Mathematics.Complexity.Karp21SparseEndpointCutCertificateExact as Sparse
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Golden
open Golden public using (andLeftTrue; andRightTrue; boolEqualTrueImpliesEqual; falseNotTrue)

------------------------------------------------------------------------
-- A real membership proof, not an unproved Boolean "all-consistent"
-- flag. Pairwise proof extraction uses the ACTUAL earlier checker.
------------------------------------------------------------------------

data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {rest} → x ∈ (x ∷ rest)
  there : ∀ {head rest} → x ∈ rest → x ∈ (head ∷ rest)

compatibleSameVertexLabels :
  ∀ {n} (a b : Fin.Fin n × Bool) →
  Sparse.observationsCompatible a b ≡ true →
  proj₁ a ≡ proj₁ b →
  proj₂ a ≡ proj₂ b
compatibleSameVertexLabels (v , a) (w , b) observed equals
  with FinP._≟_ v w
... | yes proof = boolEqualTrueImpliesEqual a b observed
... | no contradiction = ⊥-elim (contradiction equals)

checkerOneAgainstMember :
  ∀ {n} (head : Fin.Fin n × Bool)
    (tail : List (Fin.Fin n × Bool))
    {target : Fin.Fin n × Bool} →
  target ∈ tail →
  Sparse.oneAgainstAll head tail ≡ true →
  Sparse.observationsCompatible head target ≡ true
checkerOneAgainstMember head (target ∷ tail) here observed =
  andLeftTrue
    (Sparse.observationsCompatible head target)
    (Sparse.oneAgainstAll head tail)
    observed
checkerOneAgainstMember head (other ∷ tail) (there proof) observed =
  checkerOneAgainstMember head tail proof
    (andRightTrue
      (Sparse.observationsCompatible head other)
      (Sparse.oneAgainstAll head tail)
      observed)

-- The checker certifies ALL pairs in its whole finite observation list,
-- including both orders of a repeated-vertex label requirement.
checkedObservationsHaveUniqueVertexLabels :
  ∀ {n} (entries : List (Fin.Fin n × Bool)) →
  Sparse.allEndpointOccurrencesConsistent entries ≡ true →
  {first second : Fin.Fin n × Bool} →
  first ∈ entries →
  second ∈ entries →
  proj₁ first ≡ proj₁ second →
  proj₂ first ≡ proj₂ second
checkedObservationsHaveUniqueVertexLabels [] valid () _ _
checkedObservationsHaveUniqueVertexLabels (head ∷ tail)
  valid here here same = refl
checkedObservationsHaveUniqueVertexLabels (head ∷ tail)
  valid {second = second} here (there later) same =
  compatibleSameVertexLabels head second
    (checkerOneAgainstMember head tail later
      (andLeftTrue
        (Sparse.oneAgainstAll head tail)
        (Sparse.allEndpointOccurrencesConsistent tail)
        valid))
    same
checkedObservationsHaveUniqueVertexLabels (head ∷ tail)
  valid {first = first} (there earlier) here same =
  sym (compatibleSameVertexLabels head first
    (checkerOneAgainstMember head tail earlier
      (andLeftTrue
        (Sparse.oneAgainstAll head tail)
        (Sparse.allEndpointOccurrencesConsistent tail)
        valid))
    (sym same))
checkedObservationsHaveUniqueVertexLabels (head ∷ tail)
  valid (there earlier) (there later) same =
  checkedObservationsHaveUniqueVertexLabels tail
    (andRightTrue
      (Sparse.oneAgainstAll head tail)
      (Sparse.allEndpointOccurrencesConsistent tail)
      valid)
    earlier later same

------------------------------------------------------------------------
-- Choose the FIRST occurrence's vertex label; default false only for
-- a vertex not present in the m-edge input. This function can be
-- defined without computing an n-sized vector.
------------------------------------------------------------------------

firstObservedLabel :
  ∀ {n} (vertex : Fin.Fin n) →
  List (Fin.Fin n × Bool) → Bool
firstObservedLabel vertex [] = false
firstObservedLabel vertex ((seen , label) ∷ tail)
  with FinP._≟_ vertex seen
... | yes _ = label
... | no _ = firstObservedLabel vertex tail

firstObservedLabelAgreesWithEveryOccurrence :
  ∀ {n} (entries : List (Fin.Fin n × Bool)) →
  Sparse.allEndpointOccurrencesConsistent entries ≡ true →
  {point : Fin.Fin n × Bool} →
  point ∈ entries →
  firstObservedLabel (proj₁ point) entries ≡ proj₂ point
firstObservedLabelAgreesWithEveryOccurrence [] valid ()
firstObservedLabelAgreesWithEveryOccurrence
  (head ∷ tail) valid here
  with FinP._≟_ (proj₁ head) (proj₁ head)
... | yes proof = refl
... | no contradiction = ⊥-elim (contradiction refl)
firstObservedLabelAgreesWithEveryOccurrence
  (head ∷ tail) valid {point = point} (there later)
  with FinP._≟_ (proj₁ point) (proj₁ head)
... | yes same =
  checkedObservationsHaveUniqueVertexLabels (head ∷ tail)
    valid here (there later) (sym same)
... | no _ =
  firstObservedLabelAgreesWithEveryOccurrence tail
    (andRightTrue
      (Sparse.oneAgainstAll head tail)
      (Sparse.allEndpointOccurrencesConsistent tail)
      valid)
    later

-- A total function Fin n→Bool has a canonical full vector. This
-- constructed vector is used ONLY to prove soundness/existence.
vectorFromVertexFunction :
  (n : Nat) → (Fin.Fin n → Bool) → Vec.Vec Bool n
vectorFromVertexFunction zero f = Vec.[]
vectorFromVertexFunction (suc n) f =
  f Fin.zero Vec.∷
  vectorFromVertexFunction n (λ i → f (Fin.suc i))

vectorFromFunctionLookup :
  ∀ {n} (f : Fin.Fin n → Bool) (vertex : Fin.Fin n) →
  Vec.lookup (vectorFromVertexFunction n f) vertex ≡ f vertex
vectorFromFunctionLookup {zero} f ()
vectorFromFunctionLookup {suc n} f Fin.zero = refl
vectorFromFunctionLookup {suc n} f (Fin.suc vertex) =
  vectorFromFunctionLookup (λ i → f (Fin.suc i)) vertex

------------------------------------------------------------------------
-- If a vertex function agrees with every actual edge-endpoint
-- occurrence, projecting its full vector recreates the WHOLE
-- dependent EdgeBits certificate (not just the same total score).
------------------------------------------------------------------------

projectionMatchesEveryLocalOccurrence :
  ∀ {n}
    (edges : List (Cut.SignedUndirectedEdge n))
    (local : Sparse.EdgeBits edges)
    (f : Fin.Fin n → Bool) →
    (∀ {point : Fin.Fin n × Bool} →
      point ∈ Sparse.endpointObservations edges local →
      f (proj₁ point) ≡ proj₂ point) →
  Sparse.projectEdgeBits edges (vectorFromVertexFunction n f)
    ≡ local
projectionMatchesEveryLocalOccurrence [] Sparse.emptyEdgeBits f agrees =
  refl
projectionMatchesEveryLocalOccurrence
  (edge ∷ tail) (Sparse.addEdgeBits a b rest) f agrees
  rewrite vectorFromFunctionLookup f (Cut.first edge)
        | vectorFromFunctionLookup f (Cut.second edge)
        | agrees here
        | agrees (there here)
        | projectionMatchesEveryLocalOccurrence tail rest f
            (λ {point} member → agrees (there (there member))) =
  refl

-- Actual finite global reconstruction from any accepted local
-- consistency proof; isolated vertex values are false.
extendConsistentSparseToFullLabels :
  ∀ {n} (graph : Cut.WeightedCutGraph n)
    (local : Sparse.EdgeBits (Cut.edges graph)) →
  Sparse.allEndpointOccurrencesConsistent
    (Sparse.endpointObservations (Cut.edges graph) local) ≡ true →
  Σ (Vec.Vec Bool n)
    (λ labels →
      Sparse.projectEdgeBits (Cut.edges graph) labels ≡ local)
extendConsistentSparseToFullLabels {n} graph local consistent =
  vectorFromVertexFunction n
    (λ vertex →
      firstObservedLabel vertex
        (Sparse.endpointObservations (Cut.edges graph) local))
  ,
  projectionMatchesEveryLocalOccurrence
    (Cut.edges graph) local
    (λ vertex →
      firstObservedLabel vertex
        (Sparse.endpointObservations (Cut.edges graph) local))
    (λ {point} member →
      firstObservedLabelAgreesWithEveryOccurrence
        (Sparse.endpointObservations (Cut.edges graph) local)
        consistent member)

------------------------------------------------------------------------
-- Sound AND COMPLETE sparse signed weighted MAX CUT verifier.
-- The independent graph-word parser/bit clock are not paid by this.
------------------------------------------------------------------------

boolTImpliesTrue : (b : Bool) → T b → b ≡ true
boolTImpliesTrue true witness = refl
boolTImpliesTrue false ()

boolTrueImpliesT : (b : Bool) → b ≡ true → T b
boolTrueImpliesT true refl = tt
boolTrueImpliesT false ()

sparseAcceptedLocalImpliesFullGraphYES :
  ∀ {n} (graph : Cut.WeightedCutGraph n)
    (local : Sparse.EdgeBits (Cut.edges graph)) →
  Sparse.verifyConsistentSparseCut graph local ≡ true →
  Cut.WeightedMaxCutYES graph
sparseAcceptedLocalImpliesFullGraphYES graph local accepted
  with extendConsistentSparseToFullLabels graph local
    (andLeftTrue
      (Sparse.allEndpointOccurrencesConsistent
        (Sparse.endpointObservations (Cut.edges graph) local))
      (Sparse.verifySparseEdgeBits graph local)
      accepted)
... | full , projectedMatches =
  full ,
    Cut.weightedMaxCutVerifierSound graph full
      (boolTrueImpliesT
        (Cut.verifyWeightedMaxCut graph full)
        (trans
          (sym (Sparse.projectedSparseVerifierExactlyEqualsFull graph full))
          (trans
            (cong (Sparse.verifySparseEdgeBits graph) projectedMatches)
            (andRightTrue
              (Sparse.allEndpointOccurrencesConsistent
                (Sparse.endpointObservations (Cut.edges graph) local))
              (Sparse.verifySparseEdgeBits graph local)
              accepted))))

sparseAcceptedBitWordImpliesFullGraphYES :
  ∀ {n} (graph : Cut.WeightedCutGraph n)
    (word : List Bool) →
  Sparse.verifySparseCutBitWord graph word ≡ true →
  Cut.WeightedMaxCutYES graph
sparseAcceptedBitWordImpliesFullGraphYES graph word accepted
  with Sparse.decodeSparseEdgeBits (Cut.edges graph) word
... | nothing = ⊥-elim (falseNotTrue accepted)
... | just local =
  sparseAcceptedLocalImpliesFullGraphYES graph local accepted

fullGraphYieldsSparseAcceptedBitWord :
  ∀ {n} (graph : Cut.WeightedCutGraph n) →
  Cut.WeightedMaxCutYES graph →
  Σ (List Bool)
    (λ word →
      Sparse.verifySparseCutBitWord graph word ≡ true)
fullGraphYieldsSparseAcceptedBitWord graph (labels , accepted) =
  Sparse.encodeSparseEdgeBits
    (Sparse.projectEdgeBits (Cut.edges graph) labels)
  ,
  trans
    (Sparse.projectedSparseBitWordVerifierEqualsOriginal graph labels)
    (boolTImpliesTrue
      (Cut.verifyWeightedMaxCut graph labels)
      (Cut.weightedMaxCutVerifierComplete graph labels accepted))

SparseBitWordYES :
  ∀ {n} → Cut.WeightedCutGraph n → Set
SparseBitWordYES graph =
  Σ (List Bool)
    (λ word → Sparse.verifySparseCutBitWord graph word ≡ true)

-- Complete SAME-OBJECT finite N21 signed graph YES iff strict 2m-bit
-- edge-endpoint certificate word acceptance; no exponential-n witness
-- requirement remains in this *semantic* equivalence.
n21SparseBitWordDecisionIff :
  ∀ {n} (graph : Cut.WeightedCutGraph n) →
  PR.Iff (Cut.WeightedMaxCutYES graph) (SparseBitWordYES graph)
n21SparseBitWordDecisionIff graph =
  PR.iff
    (fullGraphYieldsSparseAcceptedBitWord graph)
    (λ { (word , accepted) →
      sparseAcceptedBitWordImpliesFullGraphYES graph word accepted })
