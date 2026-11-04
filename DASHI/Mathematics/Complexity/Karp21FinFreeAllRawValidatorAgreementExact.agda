module DASHI.Mathematics.Complexity.Karp21FinFreeAllRawValidatorAgreementExact where

------------------------------------------------------------------------
-- N21: THE ORIGINAL FIN-FREE RAW CHECKER AND THE DEPENDENT FIN PARSER
-- HAVE IDENTICAL SUCCESS / FAILURE STATUS FOR EVERY RAW EDGE LIST.
--
-- The source-owned Bool checker Runtime.validRawEdges uses exactly the
-- same numeric inequalities and strictAfter as Graph.validateRawEdges.
-- On an accepted u<v<n pair, the latter's additional Fin equality
-- decision cannot return yes: Fin.toℕ-fromℕ< would force u=v and
-- contradict u<v. This is the only non-obvious missing branch.
--
-- Success reconstructs an actual graph edge list; failure agrees for
-- arbitrary edge order, signed weights, malformed endpoints, loops,
-- duplicates and zero/large n. We do not equate dependent offDiagonal
-- proof functions and do not allocate Fin n on the executable path.
--
-- IMPORTANT: source-written proof candidate; no Agda kernel receipt.
-- This is RAW validator status, not yet full n21FinFreeVerifierSameWord:
-- original gamma framing, sparse certificate compatibility, signed
-- score equality and bit-tape clock remain separately open.
--
-- Richard Karp 1972; DASHI original graph and sparse runtime owners.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat.Base using (_<_)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)
import Data.Nat.Properties as NatP
import Data.Fin.Base as Fin
import Data.Fin.Properties as FinP

import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Runtime
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Boolean

nothingNotJust :
  ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
nothingNotJust ()

-- The validator's strict numeric order makes its additional
-- proof-carrying Fin-equality branch impossible for EVERY raw pair,
-- not only E20-generated complete-graph edges.
strictRawFinEndpointsApart :
  ∀ {n u v : Nat}
    (u<v : u < v) (v<n : v < n) →
  Fin.fromℕ< (NatP.<-trans u<v v<n)
    ≡ Fin.fromℕ< v<n → ⊥
strictRawFinEndpointsApart {u = u} {v = v} u<v v<n same =
  NatP.<-irrefl refl
    (subst (λ right → u < right) (sym recovered) u<v)
  where
    recovered : u ≡ v
    recovered =
      trans
        (sym (FinP.toℕ-fromℕ< (NatP.<-trans u<v v<n)))
        (trans (cong Fin.toℕ same)
          (FinP.toℕ-fromℕ< v<n))

-- Positive runtime guard reconstructs an *actual* successful run of
-- the source Graph.validateRawEdges, including the Fin endpoint data.
rawGuardTrueImpliesTypedSuccess :
  (n : Nat) (prev : Graph.PreviousPair)
  (raw : List Graph.RawEdge) →
  Runtime.validRawEdges n prev raw ≡ true →
  Σ (List (Cut.SignedUndirectedEdge n))
    (λ decoded → Graph.validateRawEdges n prev raw ≡ just decoded)
rawGuardTrueImpliesTypedSuccess n prev [] _ = [] , refl
rawGuardTrueImpliesTypedSuccess n prev (Graph.raw-edge u v w ∷ rest)
    guardTrue
  with NatP._<?_ u v | NatP._<?_ v n | Graph.strictAfter prev u v
... | yes u<v | yes v<n | true
  with FinP._≟_
    (Fin.fromℕ< (NatP.<-trans u<v v<n))
    (Fin.fromℕ< v<n)
...   | yes same = ⊥-elim
        (strictRawFinEndpointsApart u<v v<n same)
...   | no apart
  with rawGuardTrueImpliesTypedSuccess
    n (Graph.previous u v) rest guardTrue
...     | decodedRest , tailSuccess
  rewrite tailSuccess =
  (Cut.edge
    (Fin.fromℕ< (NatP.<-trans u<v v<n))
    (Fin.fromℕ< v<n) apart w ∷ decodedRest) , refl
... | no _ | _ | _ =
  ⊥-elim (Boolean.falseNotTrue guardTrue)
... | yes _ | no _ | _ =
  ⊥-elim (Boolean.falseNotTrue guardTrue)
... | yes _ | yes _ | false =
  ⊥-elim (Boolean.falseNotTrue guardTrue)

-- Observe the status of the *actual* dependent parser; this avoids
-- requiring equality between different Fin proof-function fields.
RawGuardResult :
  (n : Nat) (prev : Graph.PreviousPair)
  (raw : List Graph.RawEdge) →
  Maybe (List (Cut.SignedUndirectedEdge n)) → Set
RawGuardResult n prev raw nothing = ⊤
RawGuardResult n prev raw (just _) =
  Runtime.validRawEdges n prev raw ≡ true

rawTypedOutcomeHasSameGuard :
  (n : Nat) (prev : Graph.PreviousPair)
  (raw : List Graph.RawEdge) →
  RawGuardResult n prev raw (Graph.validateRawEdges n prev raw)
rawTypedOutcomeHasSameGuard n prev [] = refl
rawTypedOutcomeHasSameGuard n prev (Graph.raw-edge u v w ∷ rest)
  with NatP._<?_ u v | NatP._<?_ v n | Graph.strictAfter prev u v
... | yes u<v | yes v<n | true
  with FinP._≟_
    (Fin.fromℕ< (NatP.<-trans u<v v<n))
    (Fin.fromℕ< v<n)
...   | yes _ = tt
...   | no apart
  with Graph.validateRawEdges n (Graph.previous u v) rest
     | rawTypedOutcomeHasSameGuard n (Graph.previous u v) rest
...     | nothing | _ = tt
...     | just decodedRest | proof = proof
... | no _ | _ | _ = tt
... | yes _ | no _ | _ = tt
... | yes _ | yes _ | false = tt

typedSuccessImpliesRawGuardTrue :
  (n : Nat) (prev : Graph.PreviousPair)
  (raw : List Graph.RawEdge)
  (decoded : List (Cut.SignedUndirectedEdge n)) →
  Graph.validateRawEdges n prev raw ≡ just decoded →
  Runtime.validRawEdges n prev raw ≡ true
typedSuccessImpliesRawGuardTrue n prev raw decoded success =
  subst (RawGuardResult n prev raw) success
    (rawTypedOutcomeHasSameGuard n prev raw)

-- Both negative directions: rejection equivalence on every original
-- raw input, not a finite test sample or E20-image-only statement.
typedRejectImpliesRawGuardFalse :
  (n : Nat) (prev : Graph.PreviousPair)
  (raw : List Graph.RawEdge) →
  Graph.validateRawEdges n prev raw ≡ nothing →
  Runtime.validRawEdges n prev raw ≡ false
typedRejectImpliesRawGuardFalse n prev raw rejected
  with Runtime.validRawEdges n prev raw
... | false = refl
... | true with rawGuardTrueImpliesTypedSuccess n prev raw refl
...   | decoded , typed =
  ⊥-elim (nothingNotJust (trans (sym rejected) typed))

rawGuardFalseImpliesTypedReject :
  (n : Nat) (prev : Graph.PreviousPair)
  (raw : List Graph.RawEdge) →
  Runtime.validRawEdges n prev raw ≡ false →
  Graph.validateRawEdges n prev raw ≡ nothing
rawGuardFalseImpliesTypedReject n prev raw rejected
  with Graph.validateRawEdges n prev raw
... | nothing = refl
... | just decoded =
  ⊥-elim
    (Boolean.falseNotTrue
      (trans (sym rejected)
        (typedSuccessImpliesRawGuardTrue
          n prev raw decoded refl)))

------------------------------------------------------------------------
-- Explicit bidirectional result, with original owners as both sides.
------------------------------------------------------------------------

rawValidationSameStatus :
  (n : Nat) (prev : Graph.PreviousPair)
  (raw : List Graph.RawEdge) →
  (Runtime.validRawEdges n prev raw ≡ true →
    Σ (List (Cut.SignedUndirectedEdge n))
      (λ decoded → Graph.validateRawEdges n prev raw ≡ just decoded))
  × (Graph.validateRawEdges n prev raw ≡ nothing →
     Runtime.validRawEdges n prev raw ≡ false)
  × (Runtime.validRawEdges n prev raw ≡ false →
     Graph.validateRawEdges n prev raw ≡ nothing)
rawValidationSameStatus n prev raw =
  rawGuardTrueImpliesTypedSuccess n prev raw ,
    (typedRejectImpliesRawGuardFalse n prev raw ,
     rawGuardFalseImpliesTypedReject n prev raw)
