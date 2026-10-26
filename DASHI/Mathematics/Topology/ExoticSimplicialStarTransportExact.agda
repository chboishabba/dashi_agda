module DASHI.Mathematics.Topology.ExoticSimplicialStarTransportExact where

------------------------------------------------------------------------
-- FINITE-TO-ALL-DEPTH ABSTRACT STAR-TRANSPORT LEMMA
--
-- Reuses standard dependent Sigma/product and propositional equality,
-- not a competing topology or triangulation library.
--
-- A StarChain captures the source-specific *proof obligations* for
-- injective oriented simplicial collar inclusions. Given exact
-- single-step incidence transport, interior persistence and the
-- no-new-triangle condition for an already interior vertex, we
-- derive finite-ANY-LATER-DEPTH star transport by Nat induction.
--
-- Consumers must still instantiate EVERY field with their actual
-- native geometric carrier (the current triangle/vertex inclusion
-- maps in PL Python do not constitute an Agda proof instance).
-- In particular, an abstract StarChain cannot establish a genuine
-- weak geometric realisation, locally finite topological colimit,
-- proper compact exhaustion, or Richards ideal-boundary theorem.
--
-- Original mathematics: classical simplicial-complex/PL topology.
-- Source roots Brahana (1921), Kerékjártó (1923), Richards (1963)
-- belong to compact/end-surface classification, NOT this local
-- DASHI abstract proof of incidence induction.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

record StarChain : Set₁ where
  field
    Vertex Triangle : Nat → Set

    nextVertex :
      (n : Nat) → Vertex n → Vertex (suc n)

    nextTriangle :
      (n : Nat) → Triangle n → Triangle (suc n)

    incident :
      (n : Nat) → Vertex n → Triangle n → Set

    interior :
      (n : Nat) → Vertex n → Set

    oldVertexInteriorAfterCollar :
      (n : Nat) (v : Vertex n) →
      interior (suc n) (nextVertex n v)

    interiorPersists :
      (n : Nat) (v : Vertex n) →
      interior n v → interior (suc n) (nextVertex n v)

    transportIncident :
      (n : Nat) (v : Vertex n) (t : Triangle n) →
      incident n v t →
      incident (suc n) (nextVertex n v) (nextTriangle n t)

    noNewTriangleAtInterior :
      (n : Nat) (v : Vertex n) (later : Triangle (suc n)) →
      interior n v →
      incident (suc n) (nextVertex n v) later →
      Σ (Triangle n)
        (λ earlier →
          (nextTriangle n earlier ≡ later) × incident n v earlier)

open StarChain public

-- Iterated source-target stage WITHOUT relying on n + k reduction
-- on an abstract first argument (Agda Nat addition recurses first).
laterStage : Nat → Nat → Nat
laterStage n zero = n
laterStage n (suc k) = laterStage (suc n) k

futureVertex :
  (chain : StarChain) (n k : Nat) →
  Vertex chain n → Vertex chain (laterStage n k)
futureVertex chain n zero v = v
futureVertex chain n (suc k) v =
  futureVertex chain (suc n) k (nextVertex chain n v)

futureTriangle :
  (chain : StarChain) (n k : Nat) →
  Triangle chain n → Triangle chain (laterStage n k)
futureTriangle chain n zero t = t
futureTriangle chain n (suc k) t =
  futureTriangle chain (suc n) k (nextTriangle chain n t)

interiorPersistsAllDepths :
  (chain : StarChain) (n k : Nat) (v : Vertex chain n) →
  interior chain n v →
  interior chain (laterStage n k) (futureVertex chain n k v)
interiorPersistsAllDepths chain n zero v evidence = evidence
interiorPersistsAllDepths chain n (suc k) v evidence =
  interiorPersistsAllDepths chain (suc n) k
    (nextVertex chain n v)
    (interiorPersists chain n v evidence)

oldVertexEventuallyInterior :
  (chain : StarChain) (n k : Nat) (v : Vertex chain n) →
  interior chain (laterStage (suc n) k)
    (futureVertex chain (suc n) k (nextVertex chain n v))
oldVertexEventuallyInterior chain n k v =
  interiorPersistsAllDepths chain (suc n) k
    (nextVertex chain n v)
    (oldVertexInteriorAfterCollar chain n v)

incidentTransportAllDepths :
  (chain : StarChain) (n k : Nat)
  (v : Vertex chain n) (t : Triangle chain n) →
  incident chain n v t →
  incident chain (laterStage n k)
    (futureVertex chain n k v)
    (futureTriangle chain n k t)
incidentTransportAllDepths chain n zero v t proof = proof
incidentTransportAllDepths chain n (suc k) v t proof =
  incidentTransportAllDepths chain (suc n) k
    (nextVertex chain n v) (nextTriangle chain n t)
    (transportIncident chain n v t proof)

-- Central no-new-faces induction: Every face touching an old
-- interior vertex, at ANY later finite stage, is the image of
-- a face that already touched it at the original stage.
noNewTrianglesAllLaterDepths :
  (chain : StarChain) (n k : Nat)
  (v : Vertex chain n)
  (later : Triangle chain (laterStage n k)) →
  interior chain n v →
  incident chain (laterStage n k)
    (futureVertex chain n k v) later →
  Σ (Triangle chain n)
    (λ earlier →
      (futureTriangle chain n k earlier ≡ later)
      × incident chain n v earlier)
noNewTrianglesAllLaterDepths chain n zero v later hi incidence =
  later , refl , incidence
noNewTrianglesAllLaterDepths chain n (suc k) v later hi incidence
  with noNewTrianglesAllLaterDepths chain (suc n) k
         (nextVertex chain n v) later
         (interiorPersists chain n v hi) incidence
... | mid , midEquality , midIncidence
  with noNewTriangleAtInterior chain n v mid hi midIncidence
... | earlier , earlierEquality , earlierIncidence =
  earlier ,
    trans
      (cong (futureTriangle chain (suc n) k) earlierEquality)
      midEquality ,
    earlierIncidence

-- Thus for any actual StarChain:
-- every *previously interior* old star persists unchanged at
-- arbitrary future finite stages, with no new source-independent
-- incident triangles. The remaining obligation is to build
-- this StarChain from the concrete oriented PL gluing source,
-- then construct the genuine topological infinite union.
