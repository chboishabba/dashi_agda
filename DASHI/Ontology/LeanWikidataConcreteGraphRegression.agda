module DASHI.Ontology.LeanWikidataConcreteGraphRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

open import DASHI.Ontology.EpistemicTrit using (supported)
open import DASHI.Ontology.LeanWikidataVerdictBridge using (positivePropositionState)
open import DASHI.Ontology.LeanWikidataExistingContentAudit
open import DASHI.Ontology.LeanWikidataSourceRegressionBridge

------------------------------------------------------------------------
-- Content-addressed normalisation of RequestProject.ClassAlgebra's artistKB.
-- The exact canonical payload is committed as:
--   third_party/jmdupont_wikidata_lean/fixtures/artistKB.canonical.tsv
-- SHA-256:
--   05ba35f5ca702fd446a8dc290244e299e717f63bcc571b4aaf3b78e3c7927a8b
------------------------------------------------------------------------

artistGraph : ConcreteQidGraphAdapter
artistGraph =
  concreteQidGraphAdapter
    "RequestProject.ClassAlgebra:ClassAlgebraExample.artistKB"
    "05ba35f5ca702fd446a8dc290244e299e717f63bcc571b4aaf3b78e3c7927a8b"
    ("Q483501" ∷ "Q1028181" ∷ "Q1281618" ∷ "Q-painter-sculptor" ∷ "Q5592" ∷ "Q762" ∷ [])
    ("P31:Q5592->Q-painter-sculptor" ∷ "P31:Q762->Q1028181" ∷ [])
    ("P279:Q1028181->Q483501" ∷ "P279:Q1281618->Q483501" ∷
     "P279:Q-painter-sculptor->Q1028181" ∷ "P279:Q-painter-sculptor->Q1281618" ∷ [])
    []
    refs

artistUnionExecution : JamesKernelExecutionReceipt
artistUnionExecution =
  jamesKernelExecutionReceipt
    artistGraph
    "ae06ae06-2580-422a-8fc3-92aeaaca8762"
    "d394cd224742dea06a47d2cc6c150e9284e2d6ea291a02c3ba2b2dd04d4f5f88"
    "05ba35f5ca702fd446a8dc290244e299e717f63bcc571b4aaf3b78e3c7927a8b"
    "Wikidata.ClassAlgebraExample.artistKB_unionOk"
    true
    true
    true

artistUnionExecutionAccepted : executionReceiptAccepted artistUnionExecution ≡ true
artistUnionExecutionAccepted = refl

------------------------------------------------------------------------
-- Input identity is part of the proof boundary.  Reusing the same source
-- theorem receipt while presenting a different graph hash is rejected.
------------------------------------------------------------------------

wrongGraphExecution : JamesKernelExecutionReceipt
wrongGraphExecution =
  jamesKernelExecutionReceipt
    artistGraph
    "ae06ae06-2580-422a-8fc3-92aeaaca8762"
    "d394cd224742dea06a47d2cc6c150e9284e2d6ea291a02c3ba2b2dd04d4f5f88"
    "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
    "Wikidata.ClassAlgebraExample.artistKB_unionOk"
    true
    false
    true

wrongGraphExecutionRejected : executionReceiptAccepted wrongGraphExecution ≡ false
wrongGraphExecutionRejected = refl

------------------------------------------------------------------------
-- The content-addressed execution and the theorem-level source verdict agree,
-- while remaining scoped evidence rather than global truth authority.
------------------------------------------------------------------------

artistSourceVerdictAgrees :
  positivePropositionState artistUnionVerdict ≡ supported
artistSourceVerdictAgrees = refl
