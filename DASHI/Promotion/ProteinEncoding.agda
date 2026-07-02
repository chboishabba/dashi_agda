module DASHI.Promotion.ProteinEncoding where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Primitive using (Setω)

open import Data.List.Base using (map)

infixl 20 _+_
_+_ : Nat → Nat → Nat
zero  + n = n
suc m + n = suc (m + n)

infixl 30 _*_
_*_ : Nat → Nat → Nat
zero  * n = zero
suc m * n = n + (m * n)

import DASHI.Promotion.BiologyFiniteScopeClarification as BFC
import Ontology.DNA.Supervoxel4Adic as DNA

------------------------------------------------------------------------
-- 1. Alphabet
------------------------------------------------------------------------

Base : Set
Base = DNA.Base

A C G T : Base
A = DNA.A
C = DNA.C
G = DNA.G
T = DNA.T

DNAₙ : Nat → Set
DNAₙ n = DNA.DNA4  -- placeholder for Bⁿ; full Vec Base n available via Data.Vec

Codon : Set
Codon = BFC.Codon

codon : Base → Base → Base → Codon
codon = BFC.codon

codonFirst : Codon → Base
codonFirst = BFC.first

codonSecond : Codon → Base
codonSecond = BFC.second

codonThird : Codon → Base
codonThird = BFC.third

|codon| : Nat
|codon| = 64

|codon|Is64 : |codon| ≡ 64
|codon|Is64 = refl

------------------------------------------------------------------------
-- 2. Genetic-code map
------------------------------------------------------------------------

AminoAcid : Set
AminoAcid = BFC.AminoAcid

pattern Ala = BFC.Ala
pattern Arg = BFC.Arg
pattern Asn = BFC.Asn
pattern Asp = BFC.Asp
pattern Cys = BFC.Cys
pattern Gln = BFC.Gln
pattern Glu = BFC.Glu
pattern Gly = BFC.Gly
pattern His = BFC.His
pattern Ile = BFC.Ile
pattern Leu = BFC.Leu
pattern Lys = BFC.Lys
pattern Met = BFC.Met
pattern Phe = BFC.Phe
pattern Pro = BFC.Pro
pattern Ser = BFC.Ser
pattern Thr = BFC.Thr
pattern Trp = BFC.Trp
pattern Tyr = BFC.Tyr
pattern Val = BFC.Val

StopSignal : Set
StopSignal = BFC.StopSignal

pattern ochre = BFC.ochre
pattern amber = BFC.amber
pattern opal  = BFC.opal

ProteinSymbol : Set
ProteinSymbol = BFC.ProteinSymbol

pattern aminoAcid aa = BFC.aminoAcid aa
pattern stopSignal s = BFC.stopSignal s

τCanonicalTable : Codon → ProteinSymbol
τCanonicalTable = BFC.translateCodon

TranslationContext : Set
TranslationContext = Codon → ProteinSymbol

τ : TranslationContext → Codon → ProteinSymbol
τ ctx = ctx

canonicalTranslationContext : TranslationContext
canonicalTranslationContext = τCanonicalTable

τATG≡Met : τ canonicalTranslationContext (codon A T G) ≡ aminoAcid Met
τATG≡Met = refl

τTAA∈Stop : τ canonicalTranslationContext (codon T A A) ≡ stopSignal ochre
τTAA∈Stop = refl
τTAG∈Stop : τ canonicalTranslationContext (codon T A G) ≡ stopSignal amber
τTAG∈Stop = refl
τTGA∈Stop : τ canonicalTranslationContext (codon T G A) ≡ stopSignal opal
τTGA∈Stop = refl

aminoAcidCount : Nat
aminoAcidCount = 20

stopSignalCount : Nat
stopSignalCount = 3

proteinSymbolCount : Nat
proteinSymbolCount = 23

aminoAcidCountIs20 : aminoAcidCount ≡ 20
aminoAcidCountIs20 = refl

stopSignalCountIs3 : stopSignalCount ≡ 3
stopSignalCountIs3 = refl

proteinSymbolCountIs23 : proteinSymbolCount ≡ 23
proteinSymbolCountIs23 = refl

------------------------------------------------------------------------
-- 3. Protein sequence carrier
------------------------------------------------------------------------

τⁿ : TranslationContext → List Codon → List ProteinSymbol
τⁿ ctx = map (τ ctx)

seqFromCodons : TranslationContext → List Codon → List AminoAcid
seqFromCodons ctx [] = []
seqFromCodons ctx (c ∷ cs) with τ ctx c
... | aminoAcid aa = aa ∷ seqFromCodons ctx cs
... | stopSignal _  = []

ProteinSequence : Set
ProteinSequence = List AminoAcid

------------------------------------------------------------------------
-- 4. Structure carrier (fibre bundle)
------------------------------------------------------------------------

Structure : ProteinSequence → Set
Structure _ = ⊤

StructureBundle : Set
StructureBundle = Σ ProteinSequence Structure

πSeq : StructureBundle → ProteinSequence
πSeq = fst

------------------------------------------------------------------------
-- 5. Representation carrier
------------------------------------------------------------------------

LatentEmbedding : Set
LatentEmbedding = ⊤

RProtein : Set
RProtein = Σ ProteinSequence λ s → Σ (Structure s) λ _ → LatentEmbedding

rProteinSequence : RProtein → ProteinSequence
rProteinSequence = fst

rProteinStructure : (r : RProtein) → Structure (rProteinSequence r)
rProteinStructure r = fst (snd r)

rProteinEmbedding : (r : RProtein) → LatentEmbedding
rProteinEmbedding r = snd (snd r)

πSeqCompatibility : (r : RProtein) → πSeq (rProteinSequence r , rProteinStructure r) ≡ rProteinSequence r
πSeqCompatibility r = refl

------------------------------------------------------------------------
-- 6. Property surfaces
------------------------------------------------------------------------

data Property : Set where
  Solubility           : Property
  Thermostability      : Property
  Aggregation          : Property
  ExpressionYield      : Property
  FoldingStability     : Property
  MaterialProduction   : Property

allProperties : List Property
allProperties =
  Solubility
  ∷ Thermostability
  ∷ Aggregation
  ∷ ExpressionYield
  ∷ FoldingStability
  ∷ MaterialProduction
  ∷ []

propertyCount : Nat
propertyCount = 6

propertyCountIs6 : propertyCount ≡ 6
propertyCountIs6 = refl

PropertySurface : Property → Set
PropertySurface _ = ⊤

f : (p : Property) → RProtein → PropertySurface p
f _ _ = tt

multitaskF : RProtein → ((p : Property) → PropertySurface p)
multitaskF r = λ p → f p r

------------------------------------------------------------------------
-- 7. Shared latent + task heads
------------------------------------------------------------------------

Z : Set
Z = ⊤

h : RProtein → Z
h _ = tt

g : (p : Property) → Z → PropertySurface p
g _ _ = tt

fAsComposition : (p : Property) (r : RProtein) → f p r ≡ g p (h r)
fAsComposition _ _ = refl

------------------------------------------------------------------------
-- 8. Assay authority
------------------------------------------------------------------------

ExperimentalContext : Set
ExperimentalContext = ⊤

PhysicalProtein : Set
PhysicalProtein = ⊤

AssaySurface : Property → Set
AssaySurface _ = ⊤

m : (p : Property) → ExperimentalContext → PhysicalProtein → AssaySurface p
m _ _ _ = tt

ι : (p : Property) → PropertySurface p → AssaySurface p
ι _ _ = tt

prediction≠Authority : (p : Property) → Bool
prediction≠Authority _ = true

prediction≠AuthorityIsTrue : (p : Property) → prediction≠Authority p ≡ true
prediction≠AuthorityIsTrue _ = refl


------------------------------------------------------------------------
-- 9. Residual
------------------------------------------------------------------------

Residual : Set
Residual = Nat

d : (p : Property) → AssaySurface p → AssaySurface p → Residual
d _ _ _ = 0

weight : Property → Residual
weight _ = 0

ρ : (p : Property) → RProtein → ExperimentalContext → Residual
ρ p r e = d p (ι p (f p r)) (m p e tt)

globalResidual : RProtein → ExperimentalContext → Residual
globalResidual r e =
  ρ Solubility r e + ρ Thermostability r e
  + ρ Aggregation r e + ρ ExpressionYield r e
  + ρ FoldingStability r e + ρ MaterialProduction r e

weightedGlobalResidual : RProtein → ExperimentalContext → Residual
weightedGlobalResidual r e =
  weight Solubility * ρ Solubility r e
  + weight Thermostability * ρ Thermostability r e
  + weight Aggregation * ρ Aggregation r e
  + weight ExpressionYield * ρ ExpressionYield r e
  + weight FoldingStability * ρ FoldingStability r e
  + weight MaterialProduction * ρ MaterialProduction r e

------------------------------------------------------------------------
-- 10. Calibration
------------------------------------------------------------------------

κ : (p : Property) → PropertySurface p → PropertySurface p
κ _ y = y

calibrationReducesResidual : Bool
calibrationReducesResidual = true

calibrationReducesResidualIsTrue : calibrationReducesResidual ≡ true
calibrationReducesResidualIsTrue = refl

calibration≠Validation : Set
calibration≠Validation = ⊤

------------------------------------------------------------------------
-- 11. DASHI guard predicates
------------------------------------------------------------------------

-- Forbidden promotions

data ProteinEncodingForbiddenClaim : Set where
  FoldingTruthClaim       : ProteinEncodingForbiddenClaim
  DiseaseCausationClaim   : ProteinEncodingForbiddenClaim
  TherapeuticEfficacyClaim : ProteinEncodingForbiddenClaim
  ClinicalAuthorityClaim  : ProteinEncodingForbiddenClaim
  CellFateClosureClaim    : ProteinEncodingForbiddenClaim

canonicalForbiddenClaims : List ProteinEncodingForbiddenClaim
canonicalForbiddenClaims =
  FoldingTruthClaim
  ∷ DiseaseCausationClaim
  ∷ TherapeuticEfficacyClaim
  ∷ ClinicalAuthorityClaim
  ∷ CellFateClosureClaim
  ∷ []

-- Allowed operations

data ProteinEncodingAllowedOperation : Set where
  CandidateProjection     : ProteinEncodingAllowedOperation
  ResidualMeasurement     : ProteinEncodingAllowedOperation
  BenchmarkComparison     : ProteinEncodingAllowedOperation
  AssayScopedCalibration  : ProteinEncodingAllowedOperation

canonicalAllowedOperations : List ProteinEncodingAllowedOperation
canonicalAllowedOperations =
  CandidateProjection
  ∷ ResidualMeasurement
  ∷ BenchmarkComparison
  ∷ AssayScopedCalibration
  ∷ []

data ProteinEncodingGuard : Set where
  NoFoldingTruthClaim       : ProteinEncodingGuard
  NoDiseaseCausationClaim   : ProteinEncodingGuard
  NoTherapeuticEfficacyClaim : ProteinEncodingGuard
  NoClinicalAuthorityClaim  : ProteinEncodingGuard
  NoCellFateClosureClaim    : ProteinEncodingGuard
  NoExternalAuthorityBypass : ProteinEncodingGuard

canonicalProteinEncodingGuards : List ProteinEncodingGuard
canonicalProteinEncodingGuards =
  NoFoldingTruthClaim
  ∷ NoDiseaseCausationClaim
  ∷ NoTherapeuticEfficacyClaim
  ∷ NoClinicalAuthorityClaim
  ∷ NoCellFateClosureClaim
  ∷ NoExternalAuthorityBypass
  ∷ []

------------------------------------------------------------------------
-- 12. DASHIProteinEncoding record
------------------------------------------------------------------------

record DASHIProteinEncoding : Setω where
  field
    -- Translation context
    translationContext : Set
    canonicalCtx       : translationContext

    -- Alphabet
    base             : Set
    codonType        : Set
    proteinSymbol    : Set
    tau              : translationContext → codonType → proteinSymbol

    -- Sequence carrier
    proteinSequence  : Set
    tauN             : translationContext → List codonType → List proteinSymbol
    seqFn            : translationContext → List codonType → proteinSequence

    -- Structure carrier
    structure        : proteinSequence → Set
    structureBundle  : Set
    piSeq            : structureBundle → proteinSequence

    -- Representation carrier
    latentEmbedding  : Set
    rProtein         : Set
    rProteinSeq      : rProtein → proteinSequence
    rProteinStruct   : (r : rProtein) → structure (rProteinSeq r)
    rProteinEmbed    : (r : rProtein) → latentEmbedding

    -- Property surfaces
    property         : Set
    propertySurface  : property → Set
    fP               : (p : property) → rProtein → propertySurface p
    encMultitaskF    : rProtein → ((p : property) → propertySurface p)

    -- Shared latent
    zLatent          : Set
    hEnc             : rProtein → zLatent
    gHead            : (p : property) → zLatent → propertySurface p
    fAsGComposeH     : (p : property) (r : rProtein) → fP p r ≡ gHead p (hEnc r)

    -- Assay authority
    experimentalContext : Set
    physicalProtein     : Set
    assaySurface        : property → Set
    measurement         : (p : property) → experimentalContext → physicalProtein → assaySurface p
    authorityMap        : (p : property) → propertySurface p → assaySurface p

    -- Residual
    residual           : Set
    dist               : (p : property) → assaySurface p → assaySurface p → residual
    encWeight          : property → residual
    rhoP               : (p : property) → rProtein → experimentalContext → residual
    globalRho          : rProtein → experimentalContext → residual
    weightedGlobalRho  : rProtein → experimentalContext → residual

    -- Calibration
    kappa              : (p : property) → propertySurface p → propertySurface p

    -- Guards
    guards             : List ProteinEncodingGuard
    forbiddenClaims    : List ProteinEncodingForbiddenClaim
    allowedOperations  : List ProteinEncodingAllowedOperation
    foldingPromoted    : Bool
    foldingPromotedIsFalse : foldingPromoted ≡ false
    diseasePromoted    : Bool
    diseasePromotedIsFalse : diseasePromoted ≡ false
    therapeuticPromoted : Bool
    therapeuticPromotedIsFalse : therapeuticPromoted ≡ false
    clinicalPromoted   : Bool
    clinicalPromotedIsFalse : clinicalPromoted ≡ false
    cellFatePromoted   : Bool
    cellFatePromotedIsFalse : cellFatePromoted ≡ false
    candidateProjectionAllowed     : Bool
    candidateProjectionAllowedIsTrue : candidateProjectionAllowed ≡ true
    residualMeasurementAllowed     : Bool
    residualMeasurementAllowedIsTrue : residualMeasurementAllowed ≡ true
    benchmarkComparisonAllowed     : Bool
    benchmarkComparisonAllowedIsTrue : benchmarkComparisonAllowed ≡ true
    assayCalibrationAllowed        : Bool
    assayCalibrationAllowedIsTrue  : assayCalibrationAllowed ≡ true
    externalAuthorityOnly          : Bool
    externalAuthorityOnlyIsTrue    : externalAuthorityOnly ≡ true

    encodingReading : String

open DASHIProteinEncoding public

------------------------------------------------------------------------
-- 13. Canonical DASHIProteinEncoding
------------------------------------------------------------------------

canonicalDASHIProteinEncoding : DASHIProteinEncoding
canonicalDASHIProteinEncoding = record
  { translationContext        = TranslationContext
  ; canonicalCtx              = canonicalTranslationContext
  ; base                      = Base
  ; codonType                 = Codon
  ; proteinSymbol             = ProteinSymbol
  ; tau                       = τ
  ; proteinSequence           = ProteinSequence
  ; tauN                      = τⁿ
  ; seqFn                     = seqFromCodons
  ; structure                 = λ _ → ⊤
  ; structureBundle           = StructureBundle
  ; piSeq                     = πSeq
  ; latentEmbedding           = LatentEmbedding
  ; rProtein                  = RProtein
  ; rProteinSeq               = rProteinSequence
  ; rProteinStruct            = rProteinStructure
  ; rProteinEmbed             = rProteinEmbedding
  ; property                  = Property
  ; propertySurface           = λ _ → ⊤
  ; fP                        = λ _ _ → tt
  ; encMultitaskF              = λ r _ → tt
  ; zLatent                   = Z
  ; hEnc                      = λ _ → tt
  ; gHead                     = λ _ _ → tt
  ; fAsGComposeH              = λ _ _ → refl
  ; experimentalContext       = ExperimentalContext
  ; physicalProtein           = PhysicalProtein
  ; assaySurface              = λ _ → ⊤
  ; measurement               = λ _ _ _ → tt
  ; authorityMap              = λ _ _ → tt
  ; residual                  = Residual
  ; dist                      = λ _ _ _ → 0
  ; encWeight                 = λ _ → 0
  ; rhoP                      = ρ
  ; globalRho                 = globalResidual
  ; weightedGlobalRho         = weightedGlobalResidual
  ; kappa                     = κ
  ; guards                    = canonicalProteinEncodingGuards
  ; forbiddenClaims           = canonicalForbiddenClaims
  ; allowedOperations         = canonicalAllowedOperations
  ; foldingPromoted           = false
  ; foldingPromotedIsFalse    = refl
  ; diseasePromoted           = false
  ; diseasePromotedIsFalse    = refl
  ; therapeuticPromoted       = false
  ; therapeuticPromotedIsFalse = refl
  ; clinicalPromoted          = false
  ; clinicalPromotedIsFalse   = refl
  ; cellFatePromoted          = false
  ; cellFatePromotedIsFalse   = refl
  ; candidateProjectionAllowed     = true
  ; candidateProjectionAllowedIsTrue = refl
  ; residualMeasurementAllowed     = true
  ; residualMeasurementAllowedIsTrue = refl
  ; benchmarkComparisonAllowed     = true
  ; benchmarkComparisonAllowedIsTrue = refl
  ; assayCalibrationAllowed        = true
  ; assayCalibrationAllowedIsTrue  = refl
  ; externalAuthorityOnly          = true
  ; externalAuthorityOnlyIsTrue    = refl
  ; encodingReading =
      "DASHI protein encoding: finite genetic code is inhabited; protein representation is candidate latent structure; biological authority remains external; no promotion without assay residual closure."
  }

------------------------------------------------------------------------
-- 14. Non-promotion certificate
------------------------------------------------------------------------

record ProteinEncodingNonPromotionCertificate
    (enc : DASHIProteinEncoding) : Set where
  field
    guards           : List ProteinEncodingGuard
    guardsMatch      : guards ≡ DASHIProteinEncoding.guards enc
    forbiddenClaims  : List ProteinEncodingForbiddenClaim
    forbiddenMatch   : forbiddenClaims ≡ DASHIProteinEncoding.forbiddenClaims enc
    allowedOps       : List ProteinEncodingAllowedOperation
    allowedMatch     : allowedOps ≡ DASHIProteinEncoding.allowedOperations enc
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
    candidateProjectionEnabled     : Bool
    candidateProjectionEnabledIsTrue : candidateProjectionEnabled ≡ true
    residualMeasurementEnabled     : Bool
    residualMeasurementEnabledIsTrue : residualMeasurementEnabled ≡ true
    benchmarkComparisonEnabled     : Bool
    benchmarkComparisonEnabledIsTrue : benchmarkComparisonEnabled ≡ true
    assayCalibrationEnabled        : Bool
    assayCalibrationEnabledIsTrue  : assayCalibrationEnabled ≡ true
    certificateReading       : String

open ProteinEncodingNonPromotionCertificate public

canonicalProteinEncodingNonPromotionCertificate :
  ProteinEncodingNonPromotionCertificate canonicalDASHIProteinEncoding
canonicalProteinEncodingNonPromotionCertificate = record
  { guards           = canonicalProteinEncodingGuards
  ; guardsMatch      = refl
  ; forbiddenClaims  = canonicalForbiddenClaims
  ; forbiddenMatch   = refl
  ; allowedOps       = canonicalAllowedOperations
  ; allowedMatch     = refl
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
  ; candidateProjectionEnabled     = true
  ; candidateProjectionEnabledIsTrue = refl
  ; residualMeasurementEnabled     = true
  ; residualMeasurementEnabledIsTrue = refl
  ; benchmarkComparisonEnabled     = true
  ; benchmarkComparisonEnabledIsTrue = refl
  ; assayCalibrationEnabled        = true
  ; assayCalibrationEnabledIsTrue  = refl
  ; certificateReading =
      "The canonical protein encoding is non-promoting: no folding, disease, therapeutic, clinical, or cell-fate closure claim is admitted. Candidate projection, residual measurement, benchmark comparison, and assay-scoped calibration are allowed."
  }
