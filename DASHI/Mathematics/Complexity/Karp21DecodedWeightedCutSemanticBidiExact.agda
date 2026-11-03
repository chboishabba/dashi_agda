module DASHI.Mathematics.Complexity.Karp21DecodedWeightedCutSemanticBidiExact where

------------------------------------------------------------------------
-- E20/N21: proof-irrelevant edge and graph semantics on SAME carrier.
--
-- The literal parser constructs a new offDiagonal proof from decidable
-- Fin equality. Equality of such *functions* is not needed to preserve
-- the physical/decision objective. What is needed and proved here:
--
--   same Fin endpoints + same signed ℤ weight
--        => same edgeContribution for every Boolean cut
--        => same weighted cut sum for entire edge lists
--        => same positive-threshold YES/NO for actual graph instances.
--
-- Source owners: DASHI.Karp21FiniteWeightedMaxCutVerifierExact,
-- DASHI.Karp21FinDecoderIndexBidiExact, original Karp (1972) reduction.
-- No postulates, alternate graph carrier, or function extensionality.
-- Agda acceptance and graph parser validation are still separate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (Σ; _,_)
open import Data.Integer.Base using (ℤ)
import Data.Integer.Base as Int
open import Data.Empty using (⊥)
import Data.Fin.Base as Fin
import Data.Vec.Base as Vec

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21FinDecoderIndexBidiExact as FinRound

------------------------------------------------------------------------
-- The original graph decision depends on the following THREE fields.
-- Neither the equality nor inequality proof carried by an edge is
-- observed by the cut score.
------------------------------------------------------------------------

record SameWeightedEdgeFields
  {n : Nat}
  (original decoded : Cut.SignedUndirectedEdge n) : Set where
  constructor same-weighted-edge
  field
    firstSame : Cut.first original ≡ Cut.first decoded
    secondSame : Cut.second original ≡ Cut.second decoded
    signedWeightSame : Cut.weight original ≡ Cut.weight decoded
open SameWeightedEdgeFields public

sameWeightedEdgeContribution :
  ∀ {n : Nat}
    (original decoded : Cut.SignedUndirectedEdge n)
    (labels : Vec.Vec Bool n) →
  SameWeightedEdgeFields original decoded →
  Cut.edgeContribution original labels
    ≡ Cut.edgeContribution decoded labels
sameWeightedEdgeContribution original decoded labels fieldsSame
  rewrite firstSame fieldsSame
        | secondSame fieldsSame
        | signedWeightSame fieldsSame =
  refl

data SameWeightedEdgeLists {n : Nat} :
  List (Cut.SignedUndirectedEdge n) →
  List (Cut.SignedUndirectedEdge n) → Set where
  sameEdgeNil : SameWeightedEdgeLists [] []
  sameEdgeCons :
    ∀ {original decoded originals decodeds} →
    SameWeightedEdgeFields original decoded →
    SameWeightedEdgeLists originals decodeds →
    SameWeightedEdgeLists
      (original ∷ originals) (decoded ∷ decodeds)

sameWeightedEdgeListScore :
  ∀ {n : Nat}
    (originals decodeds : List (Cut.SignedUndirectedEdge n))
    (labels : Vec.Vec Bool n) →
  SameWeightedEdgeLists originals decodeds →
  Cut.edgeListCutValue originals labels
    ≡ Cut.edgeListCutValue decodeds labels
sameWeightedEdgeListScore [] [] labels sameEdgeNil = refl
sameWeightedEdgeListScore
  (original ∷ originals) (decoded ∷ decodeds)
  labels (sameEdgeCons firstProof tailProof)
  rewrite sameWeightedEdgeContribution original decoded labels firstProof
        | sameWeightedEdgeListScore originals decodeds labels tailProof =
  refl

------------------------------------------------------------------------
-- Graph YES iff under the actual signed threshold and signed score.
-- No record equality or proof-field extensionality is assumed.
------------------------------------------------------------------------

sameGraphCutScore :
  ∀ {n : Nat}
    (original decoded : Cut.WeightedCutGraph n)
    (labels : Vec.Vec Bool n) →
  SameWeightedEdgeLists (Cut.edges original) (Cut.edges decoded) →
  Cut.cutValue original labels ≡ Cut.cutValue decoded labels
sameGraphCutScore original decoded labels edgesSame =
  sameWeightedEdgeListScore
    (Cut.edges original) (Cut.edges decoded) labels edgesSame

sameWeightedGraphsAccept :
  ∀ {n : Nat}
    (original decoded : Cut.WeightedCutGraph n) →
  Cut.threshold original ≡ Cut.threshold decoded →
  SameWeightedEdgeLists (Cut.edges original) (Cut.edges decoded) →
  PR.Iff (Cut.WeightedMaxCutYES original)
         (Cut.WeightedMaxCutYES decoded)
sameWeightedGraphsAccept {n} original decoded thresholdSame edgesSame =
  PR.iff forward backward
  where
    scoreSame :
      (labels : Vec.Vec Bool n) →
      Cut.cutValue original labels ≡ Cut.cutValue decoded labels
    scoreSame labels = sameGraphCutScore original decoded labels edgesSame

    forward : Cut.WeightedMaxCutYES original →
              Cut.WeightedMaxCutYES decoded
    forward (labels , accepted) =
      labels ,
      (subst
        (λ t → Int._≤_ t (Cut.cutValue decoded labels))
        thresholdSame
        (subst
          (λ score → Int._≤_ (Cut.threshold original) score)
          (scoreSame labels)
          accepted))

    backward : Cut.WeightedMaxCutYES decoded →
               Cut.WeightedMaxCutYES original
    backward (labels , accepted) =
      labels ,
      (subst
        (λ t → Int._≤_ t (Cut.cutValue original labels))
        (sym thresholdSame)
        (subst
          (λ score → Int._≤_ (Cut.threshold decoded) score)
          (sym (scoreSame labels))
          accepted))

------------------------------------------------------------------------
-- Recreate parser's Fin.fromℕ< endpoints from original edge values.
-- Its resulting edge may carry a DIFFERENT offDiagonal proof, but
-- contributes exactly the same signed cut score to every labeling.
------------------------------------------------------------------------

reconstructedOffDiagonal :
  ∀ {n : Nat}
    (original : Cut.SignedUndirectedEdge n)
    (firstInRange : Fin.toℕ (Cut.first original) < n)
    (secondInRange : Fin.toℕ (Cut.second original) < n) →
  Fin.fromℕ< firstInRange ≡ Fin.fromℕ< secondInRange → ⊥
reconstructedOffDiagonal original firstInRange secondInRange decodedEqual =
  Cut.offDiagonal original
    (trans
      (sym
        (FinRound.reconstructOriginalFin
          (Cut.first original) firstInRange))
      (trans
        decodedEqual
        (FinRound.reconstructOriginalFin
          (Cut.second original) secondInRange)))

reconstructWeightedEdge :
  ∀ {n : Nat}
    (original : Cut.SignedUndirectedEdge n)
    (firstInRange : Fin.toℕ (Cut.first original) < n)
    (secondInRange : Fin.toℕ (Cut.second original) < n) →
  Cut.SignedUndirectedEdge n
reconstructWeightedEdge original firstBound secondBound =
  Cut.edge
    (Fin.fromℕ< firstBound)
    (Fin.fromℕ< secondBound)
    (reconstructedOffDiagonal original firstBound secondBound)
    (Cut.weight original)

reconstructWeightedEdgeFields :
  ∀ {n : Nat}
    (original : Cut.SignedUndirectedEdge n)
    (firstInRange : Fin.toℕ (Cut.first original) < n)
    (secondInRange : Fin.toℕ (Cut.second original) < n) →
  SameWeightedEdgeFields original
    (reconstructWeightedEdge original firstInRange secondInRange)
reconstructWeightedEdgeFields original firstBound secondBound =
  same-weighted-edge
    (sym (FinRound.reconstructOriginalFin
      (Cut.first original) firstBound))
    (sym (FinRound.reconstructOriginalFin
      (Cut.second original) secondBound))
    refl

reconstructedWeightedEdgeScoreSame :
  ∀ {n : Nat}
    (original : Cut.SignedUndirectedEdge n)
    (firstInRange : Fin.toℕ (Cut.first original) < n)
    (secondInRange : Fin.toℕ (Cut.second original) < n)
    (labels : Vec.Vec Bool n) →
  Cut.edgeContribution original labels ≡
  Cut.edgeContribution
    (reconstructWeightedEdge original firstInRange secondInRange)
    labels
reconstructedWeightedEdgeScoreSame original firstBound secondBound labels =
  sameWeightedEdgeContribution original
    (reconstructWeightedEdge original firstBound secondBound)
    labels
    (reconstructWeightedEdgeFields original firstBound secondBound)
