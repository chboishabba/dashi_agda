module DASHI.Mathematics.Complexity.Karp21VOAGradeActionCertificateWeldExact where

------------------------------------------------------------------------
-- EXACT, CONDITIONAL VOA GRADE ACTION ↔ FINITE MAX CUT CERTIFICATE.
--
-- Reuse (do not reconstruct):
--   Moonshine.GradedVertexOperatorAlgebraBoundary: actual grade carrier;
--   Moonshine.GradedVOAHomogeneousLinearRealisationExact: a genuine
--      two-sided grade/linear-carrier identification;
--   Moonshine.GradedRepresentationLinearRealisationExact: evaluated
--      action of the existing grade representation (not just a trace);
--   Karp21FiniteWeightedMaxCutVerifierExact: actual signed W>0 graph.
--
-- The selected-3B VOA "max cut" is an *action agreement proof frontier*.
-- It does not coincide with Karp's MAX CUT. To transport it, we must
-- pay a concrete certificate-to-grade embedding, left inverse, and
-- evaluated action score preservation. This owner proves the
-- resulting sound witness/verification transport from THOSE payments.
--
-- This proves no Monster ↔ Boolean-label action without an inhabitant
-- of the weld. In particular a character/dimension/VOA identity alone
-- cannot supply the input-dependent bitword map or polynomial clock.
--
-- Attribution: Kac 1998 (VOA), Serre (representations), FLM 1988;
-- Richard Karp 1972 (weighted MAX CUT); existing DASHI VOA proof
-- owners retain their independent authorship and Ibrahim 3B context.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (Σ; _,_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans; subst)
import Data.Integer.Base as Int
import Data.Vec.Base as Vec
import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.GradedVertexOperatorAlgebraBoundary as VOA
import DASHI.Moonshine.GradedVOAHomogeneousLinearRealisationExact as Hom
import DASHI.Moonshine.GradedRepresentationLinearRealisationExact as Linear
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut

module SameGradeWitness
  {G K : Set}
  (actionData : VOA.VOAWithGroupAction G K)
  {n : Nat}
  (graph : Cut.WeightedCutGraph n)
  (homogeneous : Hom.HomogeneousGradeLinearRealisation actionData)
  where

  representation : GR.FiniteDimensionalRepresentation
    G K (VOA.group actionData)
  representation =
    GR.grade (VOA.gradedRepresentation actionData)
      (Hom.grade homogeneous)

  -- Actual evaluated G-action on the very homogeneous VOA grade.
  -- Not an action inferred from an integer trace or formal character.
  gradeAction :
    G →
    VOA.Homogeneous (VOA.voa actionData) (Hom.grade homogeneous) →
    VOA.Homogeneous (VOA.voa actionData) (Hom.grade homogeneous)
  gradeAction element state =
    Hom.toHomogeneous homogeneous
      (Linear.evaluatedEnd
        (Hom.linearEndomorphismRealisation homogeneous)
        (GR.action representation element)
        (Hom.fromHomogeneous homogeneous state))

  record ExactCertificateActionWeld : Setω where
    field
      encodeCertificate :
        Vec.Vec Bool n →
        VOA.Homogeneous
          (VOA.voa actionData) (Hom.grade homogeneous)

      decodeCertificate :
        VOA.Homogeneous
          (VOA.voa actionData) (Hom.grade homogeneous) →
        Vec.Vec Bool n

      decodeAfterEncode :
        (bits : Vec.Vec Bool n) →
        decodeCertificate (encodeCertificate bits) ≡ bits

      -- The action must preserve the SAME signed graph's cut score.
      -- A group character, dimension and grade action supply NO
      -- automatic proof of this input-sensitive combinatorial law.
      actionPreservesScore :
        (g : G) (bits : Vec.Vec Bool n) →
        Cut.cutValue graph
          (decodeCertificate
            (gradeAction g (encodeCertificate bits)))
        ≡ Cut.cutValue graph bits

  open ExactCertificateActionWeld public

  transformedLabels :
    (weld : ExactCertificateActionWeld) →
    G → Vec.Vec Bool n → Vec.Vec Bool n
  transformedLabels weld g bits =
    decodeCertificate weld
      (gradeAction g (encodeCertificate weld bits))

  sameGradeActionPreservesVerifier :
    (weld : ExactCertificateActionWeld)
    (g : G) (bits : Vec.Vec Bool n) →
    Cut.verifyWeightedMaxCut graph
      (transformedLabels weld g bits)
    ≡ Cut.verifyWeightedMaxCut graph bits
  sameGradeActionPreservesVerifier weld g bits =
    cong (Int._≤ᵇ_ (Cut.threshold graph))
      (actionPreservesScore weld g bits)

  sameGradeActionPreservesAcceptedCut :
    (weld : ExactCertificateActionWeld)
    (g : G) (bits : Vec.Vec Bool n) →
    Cut.AcceptedCut graph bits →
    Cut.AcceptedCut graph (transformedLabels weld g bits)
  sameGradeActionPreservesAcceptedCut weld g bits accepted =
    subst (λ score → Int._≤_ (Cut.threshold graph) score)
      (sym (actionPreservesScore weld g bits))
      accepted

  -- Source-level total witness transform, with no fabricated search
  -- time or false assertion that the selected Monster 3B weld is paid.
  sameGradeActionPreservesGraphYES :
    (weld : ExactCertificateActionWeld) →
    G → Cut.WeightedMaxCutYES graph → Cut.WeightedMaxCutYES graph
  sameGradeActionPreservesGraphYES weld g (bits , accepted) =
    transformedLabels weld g bits ,
    sameGradeActionPreservesAcceptedCut weld g bits accepted


  -- The same decisive lemma shape as the 3B full-grade max-cut:
  -- decoding after encoding makes certificate inclusion INJECTIVE.
  -- Dimensional agreement cannot substitute for the left inverse.
  certificateInclusionInjective :
    (weld : ExactCertificateActionWeld)
    (left right : Vec.Vec Bool n) →
    encodeCertificate weld left ≡ encodeCertificate weld right →
    left ≡ right
  certificateInclusionInjective weld left right gradeEquality =
    trans
      (sym (decodeAfterEncode weld left))
      (trans
        (cong (decodeCertificate weld) gradeEquality)
        (decodeAfterEncode weld right))

  -- If a selected VOA grade-action output is identified with the
  -- encoding of a particular Boolean witness, decoding gives the
  -- *same* finite witness. This is the exact selected-3B "compare
  -- after inclusion, then use faithfulness" strategy, without an
  -- unverified Monster 3B action or a character-only promotion.
  gradeActionAgreementReflectsCutWitness :
    (weld : ExactCertificateActionWeld)
    (g : G) (left right : Vec.Vec Bool n) →
    gradeAction g (encodeCertificate weld left)
      ≡ encodeCertificate weld right →
    transformedLabels weld g left ≡ right
  gradeActionAgreementReflectsCutWitness weld g left right equality =
    trans
      (cong (decodeCertificate weld) equality)
      (decodeAfterEncode weld right)


  -- Discharge the GLOBAL actionPreservesScore obligation from a family
  -- of LOCAL proofs against the graph's literal signed edge list.
  -- This is the bridge from proof-fibre/PNF-style local observations
  -- to the unchanged Karp signed weighted graph objective. It uses
  -- the actual edgeContribution and its full multiplicity, so a
  -- character trace or orbit count cannot be substituted here.
  module LocalEdgewiseCertificate
    (encode : Vec.Vec Bool n →
      VOA.Homogeneous (VOA.voa actionData) (Hom.grade homogeneous))
    (decode :
      VOA.Homogeneous (VOA.voa actionData) (Hom.grade homogeneous) →
      Vec.Vec Bool n)
    (roundtrip :
      ∀ bits → decode (encode bits) ≡ bits)
    (preservesEachEdge :
      (g : G) (bits : Vec.Vec Bool n)
      (edge : Cut.SignedUndirectedEdge n) →
      Cut.edgeContribution edge
        (decode (gradeAction g (encode bits)))
      ≡ Cut.edgeContribution edge bits)
    where

    actionPreservesEdgeList :
      (g : G) (bits : Vec.Vec Bool n)
      (edges : List (Cut.SignedUndirectedEdge n)) →
      Cut.edgeListCutValue edges
        (decode (gradeAction g (encode bits)))
      ≡ Cut.edgeListCutValue edges bits
    actionPreservesEdgeList g bits [] =
      refl
    actionPreservesEdgeList g bits (edge ∷ tail) =
      cong₂ Int._+_
        (preservesEachEdge g bits edge)
        (actionPreservesEdgeList g bits tail)

    constructExactWeld : ExactCertificateActionWeld
    constructExactWeld = record
      { encodeCertificate = encode
      ; decodeCertificate = decode
      ; decodeAfterEncode = roundtrip
      ; actionPreservesScore =
          λ g bits →
            actionPreservesEdgeList g bits (Cut.edges graph)
      }
