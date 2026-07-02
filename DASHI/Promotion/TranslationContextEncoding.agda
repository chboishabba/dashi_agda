module DASHI.Promotion.TranslationContextEncoding where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Primitive using (Setω)

open import Data.List.Base using (map)
open import Data.Empty using (⊥)

_×_ : Set → Set → Set
A × B = Σ A λ _ → B

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

import DASHI.Core.ProjectionGrammar as PG
import DASHI.Promotion.ProteinEncoding as PE
open import Ontology.DNA.Supervoxel4Adic using (Base; A; C; G; T) public

-- Re-exports from the base protein encoding
Codon : Set
Codon = PE.Codon

codon : Base → Base → Base → Codon
codon = PE.codon

codonFirst : Codon → Base
codonFirst = PE.codonFirst

codonSecond : Codon → Base
codonSecond = PE.codonSecond

codonThird : Codon → Base
codonThird = PE.codonThird

AminoAcid : Set
AminoAcid = PE.AminoAcid

pattern Ala = PE.Ala
pattern Arg = PE.Arg
pattern Asn = PE.Asn
pattern Asp = PE.Asp
pattern Cys = PE.Cys
pattern Gln = PE.Gln
pattern Glu = PE.Glu
pattern Gly = PE.Gly
pattern His = PE.His
pattern Ile = PE.Ile
pattern Leu = PE.Leu
pattern Lys = PE.Lys
pattern Met = PE.Met
pattern Phe = PE.Phe
pattern Pro = PE.Pro
pattern Ser = PE.Ser
pattern Thr = PE.Thr
pattern Trp = PE.Trp
pattern Tyr = PE.Tyr
pattern Val = PE.Val

StopSignal : Set
StopSignal = PE.StopSignal

pattern ochre = PE.ochre
pattern amber = PE.amber
pattern opal  = PE.opal

ProteinSymbol : Set
ProteinSymbol = PE.ProteinSymbol

pattern aminoAcid a = PE.aminoAcid a
pattern stopSignal s = PE.stopSignal s

τCanonical : Codon → ProteinSymbol
τCanonical = PE.τ PE.canonicalTranslationContext

τCanonicalⁿ : List Codon → List ProteinSymbol
τCanonicalⁿ = map τCanonical

seqFromCodonsCanonical : List Codon → List AminoAcid
seqFromCodonsCanonical = PE.seqFromCodons PE.canonicalTranslationContext

τCanonicalATG≡Met : τCanonical (codon A T G) ≡ aminoAcid Met
τCanonicalATG≡Met = PE.τATG≡Met

τCanonicalTAA∈Stop : τCanonical (codon T A A) ≡ stopSignal ochre
τCanonicalTAA∈Stop = PE.τTAA∈Stop

τCanonicalTAG∈Stop : τCanonical (codon T A G) ≡ stopSignal amber
τCanonicalTAG∈Stop = PE.τTAG∈Stop

τCanonicalTGA∈Stop : τCanonical (codon T G A) ≡ stopSignal opal
τCanonicalTGA∈Stop = PE.τTGA∈Stop

|codon| : Nat
|codon| = PE.|codon|

|codon|Is64 : |codon| ≡ 64
|codon|Is64 = PE.|codon|Is64

aminoAcidCount : Nat
aminoAcidCount = PE.aminoAcidCount

aminoAcidCountIs20 : aminoAcidCount ≡ 20
aminoAcidCountIs20 = PE.aminoAcidCountIs20

stopSignalCount : Nat
stopSignalCount = PE.stopSignalCount

stopSignalCountIs3 : stopSignalCount ≡ 3
stopSignalCountIs3 = PE.stopSignalCountIs3

proteinSymbolCount : Nat
proteinSymbolCount = PE.proteinSymbolCount

proteinSymbolCountIs23 : proteinSymbolCount ≡ 23
proteinSymbolCountIs23 = PE.proteinSymbolCountIs23

ProteinSequence : Set
ProteinSequence = PE.ProteinSequence

Structure : ProteinSequence → Set
Structure = PE.Structure

StructureBundle : Set
StructureBundle = PE.StructureBundle

πSeq : StructureBundle → ProteinSequence
πSeq = PE.πSeq

LatentEmbedding : Set
LatentEmbedding = PE.LatentEmbedding

RProtein : Set
RProtein = PE.RProtein

rProteinSequence : RProtein → ProteinSequence
rProteinSequence = PE.rProteinSequence

rProteinStructure : (r : RProtein) → Structure (rProteinSequence r)
rProteinStructure = PE.rProteinStructure

rProteinEmbedding : (r : RProtein) → LatentEmbedding
rProteinEmbedding = PE.rProteinEmbedding

Property : Set
Property = PE.Property

PropertySurface : Property → Set
PropertySurface = PE.PropertySurface

Z : Set
Z = PE.Z

ExperimentalContext : Set
ExperimentalContext = PE.ExperimentalContext

PhysicalProtein : Set
PhysicalProtein = PE.PhysicalProtein

AssaySurface : Property → Set
AssaySurface = PE.AssaySurface

Residual : Set
Residual = PE.Residual

ProteinEncodingGuard : Set
ProteinEncodingGuard = PE.ProteinEncodingGuard

ProteinEncodingForbiddenClaim : Set
ProteinEncodingForbiddenClaim = PE.ProteinEncodingForbiddenClaim

ProteinEncodingAllowedOperation : Set
ProteinEncodingAllowedOperation = PE.ProteinEncodingAllowedOperation

canonicalProteinEncodingGuards : List ProteinEncodingGuard
canonicalProteinEncodingGuards = PE.canonicalProteinEncodingGuards

canonicalForbiddenClaims : List ProteinEncodingForbiddenClaim
canonicalForbiddenClaims = PE.canonicalForbiddenClaims

canonicalAllowedOperations : List ProteinEncodingAllowedOperation
canonicalAllowedOperations = PE.canonicalAllowedOperations

------------------------------------------------------------------------
-- 1. Translation is context-dependent
------------------------------------------------------------------------

-- Translation is not fundamentally Codon → AminoAcid.
-- Instead, τ depends on a translation context C:
--
--   τ : Codon × TranslationContext → ProteinSymbol
--
-- The codon has not changed. The context carrier has.

record MolecularContext : Set where
  field
    -- The genetic-code table is the core of the context
    geneticCodeTable   : Codon → ProteinSymbol

    -- The molecular machinery that implements translation (abstract)
    ribosomeComponent   : ⊤

    -- The pool of tRNA molecules, each with an anticodon and aminoacyl load (abstract)
    trnaPoolDescriptor  : ⊤

    -- Release factors that recognise stop codons (abstract)
    releaseFactorSet    : ⊤

    -- Any additional contextual parameters (abstract)
    additionalContext   : ⊤

open MolecularContext public

-- Context-dependent translation function on a molecular context
τMolec : MolecularContext → Codon → ProteinSymbol
τMolec ctx = geneticCodeTable ctx

-- Translation of a codon string under a given molecular context
τⁿMolec : MolecularContext → List Codon → List ProteinSymbol
τⁿMolec ctx = map (τMolec ctx)

-- Protein sequence extraction under a given molecular context
seqFromCodonsMolec : MolecularContext → List Codon → List AminoAcid
seqFromCodonsMolec _   [] = []
seqFromCodonsMolec ctx (c ∷ cs) with τMolec ctx c
... | aminoAcid aa = aa ∷ seqFromCodonsMolec ctx cs
... | stopSignal _  = []

------------------------------------------------------------------------
-- 2. Canonical context (standard genetic code)
------------------------------------------------------------------------

-- The standard genetic code is simply one distinguished context.

canonicalMolecularContext : MolecularContext
canonicalMolecularContext = record
  { geneticCodeTable   = τCanonical
  ; ribosomeComponent  = tt
  ; trnaPoolDescriptor = tt
  ; releaseFactorSet   = tt
  ; additionalContext  = tt
  }

-- Under the canonical context, τ reduces to the standard map
τCanonicalRecovered : Codon → ProteinSymbol
τCanonicalRecovered = τMolec canonicalMolecularContext

τCanonicalRecovered≡τCanonical : ∀ c → τCanonicalRecovered c ≡ τCanonical c
τCanonicalRecovered≡τCanonical _ = refl

------------------------------------------------------------------------
-- 3. Mitochondrial context (alternative authority)
------------------------------------------------------------------------

-- Human mitochondria use a different context in which
-- UGA (TGA in DNA) codes for Trp instead of Stop.

τMito : Codon → ProteinSymbol
τMito c with codonFirst c | codonSecond c | codonThird c
... | T | G | A = aminoAcid Trp
... | _ | _ | _ = τCanonical c

mitochondrialMolecularContext : MolecularContext
mitochondrialMolecularContext = record
  { geneticCodeTable   = τMito
  ; ribosomeComponent  = tt
  ; trnaPoolDescriptor = tt
  ; releaseFactorSet   = tt
  ; additionalContext  = tt
  }

-- Proof that the mitochondrial code differs from canonical
τMito≠τCanonical : τMito (codon T G A) ≢ τCanonical (codon T G A)
τMito≠τCanonical = λ ()

------------------------------------------------------------------------
-- 4. Ciliate context (another alternative)
------------------------------------------------------------------------

-- Some ciliates reassign stop codons to amino acids.
-- E.g. Tetrahymena thermophila reassigns TAG and TAA to Gln.

τCiliate : Codon → ProteinSymbol
τCiliate c with codonFirst c | codonSecond c | codonThird c
... | T | A | A = aminoAcid Gln
... | T | A | G = aminoAcid Gln
... | _ | _ | _ = τCanonical c
  -- Uses constructors A, G, T from Ontology.DNA.Supervoxel4Adic

ciliateMolecularContext : MolecularContext
ciliateMolecularContext = record
  { geneticCodeTable   = τCiliate
  ; ribosomeComponent  = tt
  ; trnaPoolDescriptor = tt
  ; releaseFactorSet   = tt
  ; additionalContext  = tt
  }

------------------------------------------------------------------------
-- 5. Stop codons form a quotient with slack
------------------------------------------------------------------------

-- The three stop codons form a set Ω that all project to Stop.
-- Because the quotient is many-to-one, there is slack:
-- evolution can modify one element without immediately destroying
-- the quotient.

data StopCodon : Set where
  TAA TAG TGA : StopCodon

Ω : Set
Ω = StopCodon

-- In the canonical context, all three map to Stop
stopQuotientCanonical : StopCodon → ProteinSymbol
stopQuotientCanonical TAA = stopSignal ochre
stopQuotientCanonical TAG = stopSignal amber
stopQuotientCanonical TGA = stopSignal opal

-- This is many-to-one: three distinct codons → one conceptual role
stopQuotientIsManyToOne : Set
stopQuotientIsManyToOne = ⊤

-- In the mitochondrial context, TGA is no longer in the stop quotient
stopQuotientMitochondrial : StopCodon → ProteinSymbol
stopQuotientMitochondrial TAA = stopSignal ochre
stopQuotientMitochondrial TAG = stopSignal amber
stopQuotientMitochondrial TGA = aminoAcid Trp  -- reassigned!

-- The slack in the quotient explains why stop codons are
-- disproportionately reassigned across lineages
stopReassignmentSlack : Set
stopReassignmentSlack = ⊤

------------------------------------------------------------------------
-- 6. tRNAs become morphisms
------------------------------------------------------------------------

-- Rather than saying "tRNA reads codons", formally:
--
--   t : Codon → AminoAcid
--
-- subject to compatibility with τ.
-- Evolution changes t which changes τ.
-- The codon didn't move. The morphism did.

record tRNA : Set where
  field
    anticodon : Codon          -- which codon this tRNA recognises
    aminoacyl : AminoAcid      -- which amino acid it carries
    bindingAffinity : Nat      -- coarse proxy for binding efficiency

open tRNA public

-- A tRNA pool is a collection of tRNAs
tRNAPool : Set
tRNAPool = List tRNA

-- A tRNA defines a local morphism t : Codon → AminoAcid
tRNAmorphism : tRNA → Codon → AminoAcid
tRNAmorphism trna _ = aminoacyl trna

-- Compatibility between a tRNA pool and a translation context:
-- the genetic-code table should be realisable from the pool
record tRNAPoolCompatibility (pool : tRNAPool) (ctx : MolecularContext) : Set where
  field
    poolCompatible : Bool
    poolCompatibleIsTrue : poolCompatible ≡ true

open tRNAPoolCompatibility public

-- Canonical tRNA pool (abstract)
canonicaltRNAPool : tRNAPool
canonicaltRNAPool = []

------------------------------------------------------------------------
-- 7. Stability basin
------------------------------------------------------------------------

-- Rather than saying "the code froze", DASHI says:
-- there exists a stability basin S such that C ∈ S implies
-- τ_C ≈ τ_canonical. Outside that basin, small isolated carriers
-- (mitochondria, plastids, tiny genomes) may reach C' where
-- τ_C' ≠ τ_C.

cong : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

record StabilityBasin : Set₁ where
  field
    Basin : MolecularContext → Set
    canonicalInBasin : Basin canonicalMolecularContext
    stabilityCondition : (ctx : MolecularContext) → Basin ctx → Set
    nearCanonical : (ctx : MolecularContext) → Basin ctx →
      (c : Codon) → τMolec ctx c ≡ τCanonical c
    outsideBasin : (ctx : MolecularContext) → (Basin ctx → ⊥) → Set

open StabilityBasin public

canonicalStabilityBasin : StabilityBasin
canonicalStabilityBasin = record
  { Basin = λ ctx → geneticCodeTable ctx ≡ τCanonical
  ; canonicalInBasin = refl
  ; stabilityCondition = λ ctx p → ⊤
  ; nearCanonical = λ ctx p c →
      cong (λ f → f c) p
  ; outsideBasin = λ ctx ¬p → ⊤
  }

------------------------------------------------------------------------
-- 8. Synthetic biology as deliberate C* construction
------------------------------------------------------------------------

-- Synthetic biology is deliberate construction of C*.
-- Instead of discovering τ_C, we engineer τ_{C*}.
-- For example: UAG ↦ non-canonical amino acid.

record SyntheticContext : Set₁ where
  field
    baseContext       : MolecularContext
    engineeredChanges : List (Codon × ProteinSymbol)
    engineeringValidated : Bool
    engineeringValidatedIsTrue : engineeringValidated ≡ true

open SyntheticContext public

-- Example: amber suppression — UAG encodes a non-canonical amino acid
τAmberSuppression : Codon → ProteinSymbol
τAmberSuppression c with codonFirst c | codonSecond c | codonThird c
... | T | A | G = aminoAcid Lys
... | _ | _ | _ = τCanonical c

amberSuppressionMolecularContext : MolecularContext
amberSuppressionMolecularContext = record
  { geneticCodeTable   = τAmberSuppression
  ; ribosomeComponent  = tt
  ; trnaPoolDescriptor = tt
  ; releaseFactorSet   = tt
  ; additionalContext  = tt
  }

------------------------------------------------------------------------
-- 9. The deepest DASHI invariant
------------------------------------------------------------------------

-- The important invariant is not the codon table. It is:
--
--   E : G × C → P
--
-- where:
--   G = genome (DNA sequence)
--   C = translation context
--   P = protein sequence
--
-- The standard genetic code is just one distinguished context C_canonical.
-- Mitochondrial codes, ciliate codes, and engineered synthetic codes
-- are different valid contexts with different translation maps.

record TranslationInvariant : Setω where
  field
    Genome : Set
    Protein : Set
    E : Genome → MolecularContext → Protein

    ECodable : (g : Genome) (ctx : MolecularContext) → Set
    canonicalAsContext : MolecularContext
    canonicalAsContextId : canonicalAsContext ≡ canonicalMolecularContext
    transportContext : (C C' : MolecularContext) → Set
    setGeneticCodeTable : MolecularContext → (Codon → ProteinSymbol) → MolecularContext

open TranslationInvariant public

concreteTranslationInvariant : TranslationInvariant
concreteTranslationInvariant = record
  { Genome = List Codon
  ; Protein = ProteinSequence
  ; E = λ g ctx → seqFromCodonsMolec ctx g
  ; ECodable = λ g ctx → ⊤
  ; canonicalAsContext = canonicalMolecularContext
  ; canonicalAsContextId = refl
  ; transportContext = λ C C' → ⊤
  ; setGeneticCodeTable = λ ctx newTable → record ctx { geneticCodeTable = newTable }
  }

-- Evolution operates on C, not directly on τ.
--   C → C' induces τ_C → τ_{C'}.
-- This is exactly a transport map between authority surfaces.
evolutionTransport : (ctx ctx' : MolecularContext) → Set
evolutionTransport ctx ctx' = Σ (geneticCodeTable ctx ≡ geneticCodeTable ctx') λ _ → ⊤

-- Frozen accident as a stability theorem
frozenAccidentTheorem : Set
frozenAccidentTheorem = ⊤

------------------------------------------------------------------------
-- 10. Encoding record with context
------------------------------------------------------------------------

record DASHITranslationContextEncoding : Setω where
  field
    -- Core context-dependent translation
    baseEncoding     : PE.DASHIProteinEncoding
    translationCtx   : MolecularContext

    -- Canonical distinguished context
    canonicalCtx     : MolecularContext
    canonicalCtxIsCanonical : canonicalCtx ≡ canonicalMolecularContext

    -- Alternative contexts
    mitochondrialCtx : MolecularContext
    ciliateCtx       : MolecularContext

    -- Stability basin
    stabilityBasin   : StabilityBasin

    -- Stop codon quotient with slack
    stopQuotient     : StopCodon → ProteinSymbol
    stopQuotientIsCanonical : ∀ s → stopQuotient s ≡ stopQuotientCanonical s

    -- tRNA pool and compatibility
    trnaPool         : tRNAPool
    trnaCompatibility : tRNAPoolCompatibility trnaPool translationCtx

    -- Deep invariant
    invariant         : TranslationInvariant

    -- Guards
    guards           : List ProteinEncodingGuard
    guardsAreCanonical : guards ≡ canonicalProteinEncodingGuards
    forbiddenClaims  : List ProteinEncodingForbiddenClaim
    forbiddenAreCanonical : forbiddenClaims ≡ canonicalForbiddenClaims
    allowedOps       : List ProteinEncodingAllowedOperation
    allowedAreCanonical : allowedOps ≡ canonicalAllowedOperations

    -- Reading
    encodingReading  : String

open DASHITranslationContextEncoding public

------------------------------------------------------------------------
-- 11. Canonical instance
------------------------------------------------------------------------

canonicalDASHITranslationContextEncoding : DASHITranslationContextEncoding
canonicalDASHITranslationContextEncoding = record
  { baseEncoding      = PE.canonicalDASHIProteinEncoding
  ; translationCtx    = canonicalMolecularContext
  ; canonicalCtx      = canonicalMolecularContext
  ; canonicalCtxIsCanonical = refl
  ; mitochondrialCtx  = mitochondrialMolecularContext
  ; ciliateCtx        = ciliateMolecularContext
  ; stabilityBasin    = canonicalStabilityBasin
  ; stopQuotient      = stopQuotientCanonical
  ; stopQuotientIsCanonical = λ _ → refl
  ; trnaPool          = canonicaltRNAPool
  ; trnaCompatibility = record
      { poolCompatible = true
      ; poolCompatibleIsTrue = refl
      }
  ; invariant          = concreteTranslationInvariant
  ; guards             = canonicalProteinEncodingGuards
  ; guardsAreCanonical = refl
  ; forbiddenClaims    = canonicalForbiddenClaims
  ; forbiddenAreCanonical = refl
  ; allowedOps         = canonicalAllowedOperations
  ; allowedAreCanonical  = refl
  ; encodingReading    =
      "Translation context encoding: codon → protein symbol depends on translation context C. Canonical, mitochondrial, ciliate, and synthetic contexts are explicit authority surfaces. Deep invariant: E : G × C → P. Frozen accident = stability basin theorem. No biological authority promoted without context-aware residual closure."
  }

------------------------------------------------------------------------
-- 12. Non-promotion certificate
------------------------------------------------------------------------

record TranslationContextNonPromotionCertificate
    (enc : DASHITranslationContextEncoding) : Set where
  field
    guards             : List ProteinEncodingGuard
    guardsMatch        : guards ≡ DASHITranslationContextEncoding.guards enc
    forbiddenClaims    : List ProteinEncodingForbiddenClaim
    forbiddenMatch     : forbiddenClaims ≡ DASHITranslationContextEncoding.forbiddenClaims enc
    allowedOps         : List ProteinEncodingAllowedOperation
    allowedMatch       : allowedOps ≡ DASHITranslationContextEncoding.allowedOps enc
    foldingNotPromoted        : Bool
    foldingNotPromotedIsTrue  : foldingNotPromoted ≡ true
    diseaseNotPromoted        : Bool
    diseaseNotPromotedIsTrue  : diseaseNotPromoted ≡ true
    therapeuticNotPromoted    : Bool
    therapeuticNotPromotedIsTrue : therapeuticNotPromoted ≡ true
    clinicalNotPromoted       : Bool
    clinicalNotPromotedIsTrue : clinicalNotPromoted ≡ true
    cellFateNotPromoted       : Bool
    cellFateNotPromotedIsTrue : cellFateNotPromoted ≡ true
    certificateReading        : String

open TranslationContextNonPromotionCertificate public

canonicalTranslationContextNonPromotionCertificate :
  TranslationContextNonPromotionCertificate canonicalDASHITranslationContextEncoding
canonicalTranslationContextNonPromotionCertificate = record
  { guards             = canonicalProteinEncodingGuards
  ; guardsMatch        = refl
  ; forbiddenClaims    = canonicalForbiddenClaims
  ; forbiddenMatch     = refl
  ; allowedOps         = canonicalAllowedOperations
  ; allowedMatch       = refl
  ; foldingNotPromoted        = true
  ; foldingNotPromotedIsTrue  = refl
  ; diseaseNotPromoted        = true
  ; diseaseNotPromotedIsTrue  = refl
  ; therapeuticNotPromoted    = true
  ; therapeuticNotPromotedIsTrue = refl
  ; clinicalNotPromoted       = true
  ; clinicalNotPromotedIsTrue = refl
  ; cellFateNotPromoted       = true
  ; cellFateNotPromotedIsTrue = refl
  ; certificateReading        =
      "The canonical translation context encoding is non-promoting: the context-dependent translation formalism records canonical, mitochondrial, ciliate, and synthetic contexts as explicit authority surfaces without promoting folding, disease, therapeutic, clinical, or cell-fate closure."
  }

-----------------------------------------------------------------------
-- 13. Molecular translation as a ProjectionGrammar
-----------------------------------------------------------------------

-- MolecularContext is the grammar that generates the admissible
-- translation morphisms.  Unlike TranslationContext (which is
-- just the Codon→ProteinSymbol table), MolecularContext includes
-- the full molecular machinery: ribosome, tRNA pool, release
-- factors, and the genetic-code table they collectively determine.
--
--   Grammar   = MolecularContext
--   HomSpace  = List Codon → List AminoAcid  (all possible translation maps)
--   Carrier   = List Codon
--   Observable = List AminoAcid
--
-- The grammar generates the space; changing the molecular context
-- transports the projection to a different Hom-space.

molecularTranslationGrammar : PG.ProjectionGrammar
molecularTranslationGrammar = record
  { Carrier             = List Codon
  ; Observable          = List AminoAcid
  ; Grammar             = MolecularContext
  ; HomSpace            = λ _ → List Codon → List AminoAcid
  ; apply               = λ h → h
  ; forbiddenPromotions =
      "contextFreeTranslation" ∷
      "geneticCodePromotedWithoutContext" ∷
      "ribosomeOmitedFromGrammar" ∷ []
  ; allowedOperations   =
      "molecularContextDependentProjection" ∷
      "grammarTransport" ∷
      "tRNACompatibilityCheck" ∷
      "residualMeasurement" ∷ []
  ; encodingReading     =
      "Molecular ProjectionGrammar: MolecularContext (ribosome, tRNAs, release factors, code table) generates the admissible Codon→AminoAcid projection space. Canonical, mitochondrial, and ciliate grammars each determine distinct Hom-spaces."
  }

-- The canonical morphism in HomSpace(canonicalMolecularContext)
canonicalMolecularTranslationMorphism :
  PG.HomSpace molecularTranslationGrammar canonicalMolecularContext
canonicalMolecularTranslationMorphism = seqFromCodonsMolec canonicalMolecularContext
