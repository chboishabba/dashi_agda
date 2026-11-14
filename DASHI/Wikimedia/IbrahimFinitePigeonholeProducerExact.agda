module DASHI.Wikimedia.IbrahimFinitePigeonholeProducerExact where

open import DASHI.Core.Prelude

import Data.Fin.Base as Fin
import Data.Fin.Properties as FinProperties

import DASHI.Wikimedia.IbrahimFiniteOrbitRevisionWeldExact as Orbit
import DASHI.Wikimedia.IbrahimGeneralFiniteCertificateKernelExact as General

------------------------------------------------------------------------
-- CONSTRUCTIVE FINITE FIRST-LINK PIGEONHOLE PRODUCER
--
-- External first-link methodology:
-- M. Ibrahim, C. M. Danforth, P. S. Dodds,
-- Journal of Computational Science 19 (2017), pp. 21-30.
-- DOI 10.1016/j.jocs.2016.12.001.
--
-- NEW DASHI proof: from an exhaustive finite node list alone, derive
-- repeated orbit states, with no supplied collisions or axioms.
--
-- Reuse the stdlib constructive Fin pigeonhole theorem. The list need
-- not have unique entries: it only needs to cover all source nodes.
-- This is a theorem about total FIRST-LINK functions Node -> Node,
-- NOT partial links, redirects, real Wikipedia page identity, or
-- original dump/producer and QID source provenance.
------------------------------------------------------------------------

carrierSize : ∀ {Node : Set} → List Node → Nat
carrierSize [] = zero
carrierSize (_ ∷ xs) = suc (carrierSize xs)

lookupCarrier :
  ∀ {Node : Set} (xs : List Node) →
  Fin.Fin (carrierSize xs) → Node
lookupCarrier [] ()
lookupCarrier (x ∷ xs) Fin.zero = x
lookupCarrier (x ∷ xs) (Fin.suc i) = lookupCarrier xs i

indexOfListed :
  ∀ {Node : Set} {node : Node} {xs : List Node} →
  General.Listed node xs → Fin.Fin (carrierSize xs)
indexOfListed General.listedHere = Fin.zero
indexOfListed (General.listedThere present) =
  Fin.suc (indexOfListed present)

lookupIndexedListed :
  ∀ {Node : Set} {node : Node} {xs : List Node} →
  (present : General.Listed node xs) →
  lookupCarrier xs (indexOfListed present) ≡ node
lookupIndexedListed General.listedHere = refl
lookupIndexedListed (General.listedThere present) =
  lookupIndexedListed present

carrierEncode :
  ∀ {Node : Set} (carrier : General.CompleteFiniteCarrier Node) →
  Node → Fin.Fin (carrierSize (General.allNodes carrier))
carrierEncode carrier node =
  indexOfListed (General.covers carrier node)

carrierDecode :
  ∀ {Node : Set} (carrier : General.CompleteFiniteCarrier Node) →
  Fin.Fin (carrierSize (General.allNodes carrier)) → Node
carrierDecode carrier = lookupCarrier (General.allNodes carrier)

carrierDecodeEncode :
  ∀ {Node : Set} (carrier : General.CompleteFiniteCarrier Node) →
  (node : Node) →
  carrierDecode carrier (carrierEncode carrier node) ≡ node
carrierDecodeEncode carrier node =
  lookupIndexedListed (General.covers carrier node)

encodedEqualityReflectsOriginal :
  ∀ {Node : Set} (carrier : General.CompleteFiniteCarrier Node) →
  {a b : Node} →
  carrierEncode carrier a ≡ carrierEncode carrier b → a ≡ b
encodedEqualityReflectsOriginal carrier {a} {b} same =
  trans (sym (carrierDecodeEncode carrier a))
    (trans (cong (carrierDecode carrier) same)
      (carrierDecodeEncode carrier b))

------------------------------------------------------------------------
-- Convert strict index order to a positive orbit period:
-- m < n gives m + suc (n - suc m) = n.
-- This uses the stdlib natural subtraction/order lemma, not a
-- guess that a repeated state is adjacent on the orbit.
------------------------------------------------------------------------

strictGapRebuild :
  ∀ {m n : Nat} → m < n →
  m + suc (n ∸ suc m) ≡ n
strictGapRebuild {m} {n} m<n =
  trans (+-suc m (n ∸ suc m))
    (m+[n∸m]≡n m<n)

------------------------------------------------------------------------
-- A full orbit of N+1 entries into N finite positions has an
-- actual repeated state. The resulting positive-length certificate
-- is in the existing generic graph owner.
------------------------------------------------------------------------

finiteCarrierImpliesEveryStartRepeats :
  ∀ {Node : Set}
    (next : Node → Node)
    (carrier : General.CompleteFiniteCarrier Node) →
  (start : Node) → General.OrbitRepeat next start
finiteCarrierImpliesEveryStartRepeats next carrier start
  with FinProperties.pigeonhole
    {m = carrierSize (General.allNodes carrier)}
    {n = suc (carrierSize (General.allNodes carrier))}
    ≤-refl
    (λ k → carrierEncode carrier
      (Orbit.iterate next (Fin.toℕ k) start))
... | i , j , i<j , same =
  General.orbitRepeat
    (Fin.toℕ i)
    (Fin.toℕ j ∸ suc (Fin.toℕ i))
    (trans
      (cong (λ steps → Orbit.iterate next steps start)
        (strictGapRebuild i<j))
      (sym (encodedEqualityReflectsOriginal carrier same)))

finiteCarrierProducesAllRepeats :
  ∀ {Node : Set}
    (next : Node → Node)
    (carrier : General.CompleteFiniteCarrier Node) →
  General.FiniteOrbitRepeatCertificate next
finiteCarrierProducesAllRepeats next carrier =
  General.finiteOrbitRepeatCertificate
    (finiteCarrierImpliesEveryStartRepeats next carrier)

finiteFirstLinkOrbitClassifiesAutomatically :
  ∀ {Node : Set}
    (next : Node → Node)
    (carrier : General.CompleteFiniteCarrier Node) →
  General.VerifiedFiniteFirstLinkCensus next
finiteFirstLinkOrbitClassifiesAutomatically next carrier =
  General.finiteFirstLinkOrbitClassifies next carrier
    (finiteCarrierProducesAllRepeats next carrier)

allFiniteStartsEventuallyCycle :
  ∀ {Node : Set}
    (next : Node → Node)
    (carrier : General.CompleteFiniteCarrier Node) →
  (start : Node) → Orbit.EventualCycle next start
allFiniteStartsEventuallyCycle next carrier start =
  General.eventCycle
    (finiteFirstLinkOrbitClassifiesAutomatically next carrier) start

------------------------------------------------------------------------
-- This theorem does not assert uniqueness of a chosen cycle vertex.
-- Cycle-rotation equivalence and actual Wikipedia-source provenance
-- remain separate targets; a complete carrier is a proof obligation.
------------------------------------------------------------------------
