module DASHI.Reasoning.JMDAristotleSymposiumSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Ontology.LeanWikidataSourceSnapshot as PriorAristotle
import DASHI.Reasoning.ZizekPNFSourceAtlas as PriorJMD

------------------------------------------------------------------------
-- JMD / ARISTOTLE SYMPOSIUM SOURCE ATLAS
--
-- Source supplied to this project on 2026-09-16 as
--   c56a9d2-output-20260916.tar.gz
-- SHA-256:
--   e00967129bdb0404cc9e2ccc55734927b89f77ba915b6bd62ce464b344a2ac27
--
-- The supplied archive contains 22 RequestProject/*.lean modules and 6,952
-- Lean source lines.  This atlas records provenance and the user's explicit
-- ownership declaration.  It does not adjudicate copyright/title, import Lean
-- proof into Agda, or turn a formal consequence of supplied axioms into an
-- externally established fact.
------------------------------------------------------------------------

archiveSha256 : String
archiveSha256 =
  "e00967129bdb0404cc9e2ccc55734927b89f77ba915b6bd62ce464b344a2ac27"

requestProjectModuleCount : Nat
requestProjectModuleCount = 22

requestProjectLeanLineCount : Nat
requestProjectLeanLineCount = 6952

priorJMDAristotleRequestId : String
priorJMDAristotleRequestId = PriorAristotle.aristotleRequestId

record OwnershipDeclaration : Set where
  constructor ownershipDeclaration
  field
    declaredOwner : String
    declarationBasis : String
    solePropertyClaimed : Bool
    legalAdjudicationPerformed : Bool
    attributionMustBeRetained : Bool
    declarationScope : String

open OwnershipDeclaration public

jmdOwnershipDeclaration : OwnershipDeclaration
jmdOwnershipDeclaration =
  ownershipDeclaration
    "James Michael DuPont (JMD / meta-introspector)"
    "user-provided ownership statement for the attached 2026-09-16 Aristotle bundle"
    true
    false
    true
    "source ownership/provenance declaration only; not an independent legal adjudication by DASHI"

jmdBundleSource : Source.AttributedSource
jmdBundleSource =
  Source.mkNoDOISource
    "James Michael DuPont (JMD / meta-introspector)"
    "Aristotle Symposium / Republic RequestProject bundle"
    "JMD-owned project material supplied to DASHI on 2026-09-16"
    "2026"
    "attachment:c56a9d2-output-20260916.tar.gz"
    (Source.namedSourceKind "JMD formal source bundle")
    "source bundle containing the Lean Symposium, Wikipedia/Wikidata analogy, IP/source-bias knowledge bases, Republic verification formalisation and finite witnessing models; citation imports neither Lean proof nor empirical authority"
    Source.publicAttribution

jmdIPBiasSource : Source.AttributedSource
jmdIPBiasSource =
  Source.mkNoDOISource
    "James Michael DuPont (JMD / meta-introspector)"
    "RequestProject/SymposiumIPBias.lean"
    "JMD-owned Aristotle RequestProject bundle supplied 2026-09-16"
    "2026"
    "attachment:c56a9d2-output-20260916.tar.gz#RequestProject/SymposiumIPBias.lean"
    (Source.namedSourceKind "Lean formalisation source")
    "transcribes a stipulated IP/office/view knowledge base and proves consequences inside that knowledge base; the bridge must not promote those stipulated premises to external authorship or bias facts"
    Source.publicAttribution

jmdSourceBiasSource : Source.AttributedSource
jmdSourceBiasSource =
  Source.mkNoDOISource
    "James Michael DuPont (JMD / meta-introspector)"
    "RequestProject/SymposiumSourceBias.lean"
    "JMD-owned Aristotle RequestProject bundle supplied 2026-09-16"
    "2026"
    "attachment:c56a9d2-output-20260916.tar.gz#RequestProject/SymposiumSourceBias.lean"
    (Source.namedSourceKind "Lean formalisation source")
    "transcribes a supplied source-preference claim, derives its logical consequences and supplies a finite model; neither satisfiability nor derivability is external evidence that the premises describe Wikipedia or any named source"
    Source.publicAttribution

jmdRepublicVerificationSource : Source.AttributedSource
jmdRepublicVerificationSource =
  Source.mkNoDOISource
    "James Michael DuPont (JMD / meta-introspector)"
    "RequestProject/RepublicVerification.lean"
    "JMD-owned Aristotle RequestProject bundle supplied 2026-09-16"
    "2026"
    "attachment:c56a9d2-output-20260916.tar.gz#RequestProject/RepublicVerification.lean"
    (Source.namedSourceKind "Lean formalisation source")
    "formal source for ContentAddressed, ReputationAddressed, factorisation and injective-CID results; imported as theorem provenance rather than automatically re-proved by Agda"
    Source.publicAttribution

jmdAristotleSymposiumSources : List Source.AttributedSource
jmdAristotleSymposiumSources =
  jmdBundleSource
  ∷ jmdIPBiasSource
  ∷ jmdSourceBiasSource
  ∷ jmdRepublicVerificationSource
  ∷ []

jmdAristotleSymposiumSourceAtlas : Source.AttributedSourceAtlas
jmdAristotleSymposiumSourceAtlas =
  Source.mkSourceAtlas
    "JMD Aristotle Symposium / Republic source atlas"
    "DASHI.Reasoning.JMDAristotleSymposiumSourceAtlasExact"
    jmdAristotleSymposiumSources
    "JMD-owned supplied Lean bundle; exact formal-source relationships for Symposium IP/source-bias and Republic content-addressed verification"

jmdAristotleSymposiumSourceAtlasReceipt : GenericReceipt.GenericReceipt
jmdAristotleSymposiumSourceAtlasReceipt =
  Source.attributedSourceAtlasReceipt
    jmdAristotleSymposiumSourceAtlas
    "source-level audit of supplied archive plus DASHI attribution bridge; Agda kernel certification tracked separately"

jmdAristotleSymposiumSourceAtlasReceiptNonPromoting :
  GenericReceipt.promotesClaim jmdAristotleSymposiumSourceAtlasReceipt ≡ false
jmdAristotleSymposiumSourceAtlasReceiptNonPromoting = refl

------------------------------------------------------------------------
-- Cross-pollination anchors.  These are references to existing JMD/Aristotle
-- attribution work, not a claim that the 2026-08-16 and 2026-09-16 archives are
-- the same object.
------------------------------------------------------------------------

priorJMDMemeSource : Source.AttributedSource
priorJMDMemeSource = PriorJMD.jmdMemeFormalismSource

priorJMDSFMSource : Source.AttributedSource
priorJMDSFMSource = PriorJMD.jmdSFMSource

sameAsPriorAristotleArchiveClaimed : Bool
sameAsPriorAristotleArchiveClaimed = false

ownershipDeclarationIsLegalAdjudication : Bool
ownershipDeclarationIsLegalAdjudication = legalAdjudicationPerformed jmdOwnershipDeclaration

ownershipDeclarationIsLegalAdjudicationIsFalse :
  ownershipDeclarationIsLegalAdjudication ≡ false
ownershipDeclarationIsLegalAdjudicationIsFalse = refl
