module DASHI.Mathematics.Complexity.Karp21VOAZ2CutOrbitExact where

------------------------------------------------------------------------
-- VOA-action REUSE PATTERN, instantiated only for the actual C2 cut
-- action. Source: Karp 1972; DASHI/Mathematics/Complexity/
-- Karp21SignedLaplacianCutExact signed global flip.
--
-- Here the real Z2 action on an n>0 labelled graph has a canonical
-- representative with first vertex false. This proves an EXACT
-- same-target accepted certificate iff and verifier-output invariance.
-- It does not identify any Monster VOA action with this finite action,
-- or turn an exponential search into polynomial-time verification.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; subst)
import Data.Integer.Base as Int
import Data.Fin.Base as Fin
import Data.Vec.Base as Vec
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
open import Data.List.Base using (List)
import Data.List.Base as List
import Data.Maybe.Base as Maybe
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21MaxCutCertificateBinaryCodecExact as BitCode
import DASHI.Mathematics.Complexity.Karp21SignedLaplacianCutExact as Lap

canonicalBitLabels :
  ∀ {n : Nat} → Vec.Vec Bool (suc n) → Vec.Vec Bool (suc n)
canonicalBitLabels (false Vec.∷ rest) = false Vec.∷ rest
canonicalBitLabels (true Vec.∷ rest) =
  Lap.flipLabels (true Vec.∷ rest)

canonicalFirstFalse :
  ∀ {n : Nat} (bits : Vec.Vec Bool (suc n)) →
  Vec.lookup (canonicalBitLabels bits) Fin.zero ≡ false
canonicalFirstFalse (false Vec.∷ rest) = refl
canonicalFirstFalse (true Vec.∷ rest) = refl

canonicalCutScore :
  ∀ {n : Nat} (graph : Cut.WeightedCutGraph (suc n))
    (bits : Vec.Vec Bool (suc n)) →
  Cut.cutValue graph (canonicalBitLabels bits) ≡
  Cut.cutValue graph bits
canonicalCutScore graph (false Vec.∷ rest) = refl
canonicalCutScore graph (true Vec.∷ rest) =
  Lap.signedMaxCutGlobalFlipInvariant
    (Cut.edges graph) (true Vec.∷ rest)

canonicalAcceptedIff :
  ∀ {n : Nat} (graph : Cut.WeightedCutGraph (suc n))
    (bits : Vec.Vec Bool (suc n)) →
  PR.Iff
    (Cut.AcceptedCut graph bits)
    (Cut.AcceptedCut graph (canonicalBitLabels bits))
canonicalAcceptedIff graph bits =
  PR.iff
    (λ accepted →
      subst
        (λ score → Int._≤_ (Cut.threshold graph) score)
        (sym (canonicalCutScore graph bits)) accepted)
    (λ accepted →
      subst
        (λ score → Int._≤_ (Cut.threshold graph) score)
        (canonicalCutScore graph bits) accepted)

CanonicalAcceptedCut :
  ∀ {n : Nat} → Cut.WeightedCutGraph (suc n) → Set
CanonicalAcceptedCut {n} graph =
  Σ (Vec.Vec Bool (suc n))
    (λ bits →
      (Vec.lookup bits Fin.zero ≡ false) ×
      Cut.AcceptedCut graph bits)

canonicalCutWitnessIff :
  ∀ {n : Nat} (graph : Cut.WeightedCutGraph (suc n)) →
  PR.Iff (Cut.WeightedMaxCutYES graph)
         (CanonicalAcceptedCut graph)
canonicalCutWitnessIff graph =
  PR.iff
    (λ { (bits , accepted) →
      canonicalBitLabels bits ,
      (canonicalFirstFalse bits ,
       PR.forward (canonicalAcceptedIff graph bits) accepted) })
    (λ { (bits , (firstFalse , accepted)) →
      bits , accepted })

canonicalVerifierValue :
  ∀ {n : Nat} (graph : Cut.WeightedCutGraph (suc n))
    (bits : Vec.Vec Bool (suc n)) →
  Cut.verifyWeightedMaxCut graph (canonicalBitLabels bits) ≡
  Cut.verifyWeightedMaxCut graph bits
canonicalVerifierValue graph bits =
  cong (Int._≤ᵇ_ (Cut.threshold graph))
    (canonicalCutScore graph bits)


------------------------------------------------------------------------
-- Same computation on the EXISTING N21 List Bool word carrier.
-- Normalisation does not change certificate size. The absolute binary
-- size does not get halved: only the search-orbit representative count.
------------------------------------------------------------------------

canonicalCertificateWord :
  ∀ {n : Nat} → Vec.Vec Bool (suc n) → List Bool
canonicalCertificateWord bits =
  BitCode.encodeCutLabels (canonicalBitLabels bits)

canonicalCertificateWordLength :
  ∀ {n : Nat} (bits : Vec.Vec Bool (suc n)) →
  Data.List.Base.length (canonicalCertificateWord bits) ≡ suc n
canonicalCertificateWordLength bits =
  BitCode.cutCertificateWordLength (canonicalBitLabels bits)

canonicalCertificateWordDecodes :
  ∀ {n : Nat} (bits : Vec.Vec Bool (suc n)) →
  BitCode.decodeCutLabels (suc n)
    (canonicalCertificateWord bits)
  ≡ Data.Maybe.Base.just (canonicalBitLabels bits)
canonicalCertificateWordDecodes bits =
  BitCode.decodeEncodeCutLabels (canonicalBitLabels bits)

canonicalCertificateWordVerifierEqualsOriginal :
  ∀ {n : Nat} (graph : Cut.WeightedCutGraph (suc n))
    (bits : Vec.Vec Bool (suc n)) →
  BitCode.wordCutVerifier graph (canonicalCertificateWord bits)
  ≡ Cut.verifyWeightedMaxCut graph bits
canonicalCertificateWordVerifierEqualsOriginal graph bits
  rewrite canonicalCertificateWordDecodes bits =
  canonicalVerifierValue graph bits
