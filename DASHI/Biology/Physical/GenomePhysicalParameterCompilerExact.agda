module DASHI.Biology.Physical.GenomePhysicalParameterCompilerExact where

------------------------------------------------------------------------
-- The genome is treated as an input to parameter compilation, not as a direct
-- morphology lookup table.  The exact finite regression uses the existing DNA
-- base/UV carrier plus an epigenetic/context bit to select downstream operator
-- parameters.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.DNAChemistryCarrier as DNA

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

false≢true : false ≢ true
false≢true ()

xor : Bool → Bool → Bool
xor false false = false
xor false true = true
xor true false = true
xor true true = false

axisBit : DNA.SignedAxis → Bool
axisBit DNA.axisNegative = false
axisBit DNA.axisPositive = true

record RegulatoryLocus : Set where
  constructor regulatoryLocus
  field
    base : DNA.DNABase
    accessible : Bool

open RegulatoryLocus public

record DevelopmentalParameters : Set where
  constructor developmentalParameters
  field
    channelExpression : Bool
    adhesionProgram : Bool
    receptorProfile : Bool

open DevelopmentalParameters public

compileParameters : RegulatoryLocus → DevelopmentalParameters
compileParameters locus with DNA.toUV (base locus)
... | DNA.uv u v =
  developmentalParameters
    (xor (axisBit u) (accessible locus))
    (axisBit v)
    (xor (axisBit v) (accessible locus))

sameGenomeClosed openLocus : RegulatoryLocus
sameGenomeClosed = regulatoryLocus DNA.A false
openLocus = regulatoryLocus DNA.A true

sameGenomicBase : base sameGenomeClosed ≡ base openLocus
sameGenomicBase = refl

contextChangesCompiledChannelParameter :
  channelExpression (compileParameters sameGenomeClosed)
  ≢ channelExpression (compileParameters openLocus)
contextChangesCompiledChannelParameter = false≢true

contextChangesCompiledReceptorParameter :
  receptorProfile (compileParameters sameGenomeClosed)
  ≢ receptorProfile (compileParameters openLocus)
contextChangesCompiledReceptorParameter = true≢false
  where
  true≢false : true ≢ false
  true≢false ()

-- The exact UV chart remains recoverable at the DNA carrier level; parameter
-- compilation is intentionally context-sensitive downstream of that carrier.
dnaUVStillExact : (b : DNA.DNABase) → DNA.fromUV (DNA.toUV b) ≡ b
dnaUVStillExact = DNA.fromUV-toUV
