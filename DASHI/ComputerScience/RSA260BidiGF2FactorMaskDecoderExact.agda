module DASHI.ComputerScience.RSA260BidiGF2FactorMaskDecoderExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiGF2BasisCoordinateRowCodecExact as Basis

------------------------------------------------------------------------
-- GF(2) FACTOR-BASIS / MASK DECODER
--
-- Runtime factor packets store up to eight selected row-space basis rows and
-- one bit-mask selecting which basis rows XOR to each source row.  This owner
-- defines that exact decoding semantics on the concrete GF(2)^8 carrier.
--
-- It does not prove how the producer found the basis or masks.  Its role is the
-- smaller proof-carrying consumer: once concrete packet bytes are compiled to
-- these constructors, expansion equalities reduce inside Agda.
------------------------------------------------------------------------

xorBit : Bool → Bool → Bool
xorBit false b = b
xorBit true false = true
xorBit true true = false

xorRow : Basis.GF2Row8 → Basis.GF2Row8 → Basis.GF2Row8
xorRow
  (Basis.gf2-row8 a0 a1 a2 a3 a4 a5 a6 a7)
  (Basis.gf2-row8 b0 b1 b2 b3 b4 b5 b6 b7) =
  Basis.gf2-row8
    (xorBit a0 b0)
    (xorBit a1 b1)
    (xorBit a2 b2)
    (xorBit a3 b3)
    (xorBit a4 b4)
    (xorBit a5 b5)
    (xorBit a6 b6)
    (xorBit a7 b7)

zeroRow : Basis.GF2Row8
zeroRow = Basis.gf2-row8 false false false false false false false false

selectXor : Bool → Basis.GF2Row8 → Basis.GF2Row8 → Basis.GF2Row8
selectXor false row acc = acc
selectXor true row acc = xorRow row acc

record FactorBasis8 : Set where
  constructor factor-basis8
  field
    basis0 basis1 basis2 basis3 basis4 basis5 basis6 basis7 : Basis.GF2Row8
open FactorBasis8 public

record FactorMask8 : Set where
  constructor factor-mask8
  field
    mask0 mask1 mask2 mask3 mask4 mask5 mask6 mask7 : Bool
open FactorMask8 public

expandMask8 : FactorBasis8 → FactorMask8 → Basis.GF2Row8
expandMask8 basis mask =
  selectXor (mask7 mask) (basis7 basis)
  (selectXor (mask6 mask) (basis6 basis)
  (selectXor (mask5 mask) (basis5 basis)
  (selectXor (mask4 mask) (basis4 basis)
  (selectXor (mask3 mask) (basis3 basis)
  (selectXor (mask2 mask) (basis2 basis)
  (selectXor (mask1 mask) (basis1 basis)
  (selectXor (mask0 mask) (basis0 basis) zeroRow)))))))

------------------------------------------------------------------------
-- Small concrete reduction test retained in the production owner so the
-- semantics are not only abstractly declared.
------------------------------------------------------------------------

e0 : Basis.GF2Row8
e0 = Basis.gf2-row8 true false false false false false false false

e1 : Basis.GF2Row8
e1 = Basis.gf2-row8 false true false false false false false false

e2 : Basis.GF2Row8
e2 = Basis.gf2-row8 false false true false false false false false

sampleBasis : FactorBasis8
sampleBasis = factor-basis8 e0 e1 e2 zeroRow zeroRow zeroRow zeroRow zeroRow

sampleMask : FactorMask8
sampleMask = factor-mask8 true false true false false false false false

sampleExpectedRow : Basis.GF2Row8
sampleExpectedRow =
  Basis.gf2-row8 true false true false false false false false

sampleExpansionExact : expandMask8 sampleBasis sampleMask ≡ sampleExpectedRow
sampleExpansionExact = refl

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record GF2FactorMaskDecoderBoundary : Set where
  constructor gf2-factor-mask-decoder-boundary
  field
    concreteGF2EightBitRowInherited : Bool
    xorSemanticsDefinedBitwise : Bool
    eightBasisSlotsDefined : Bool
    eightMaskBitsDefined : Bool
    maskExpansionDefinedBySelectedXor : Bool
    concreteReductionWitnessPaid : Bool
    producerBasisSearchAlgorithmProved : Bool
    producerMaskSearchAlgorithmProved : Bool
    runtimeFactorBytesCompiledToTheseConstructors : Bool
    allRuntimeFactorPacketsKernelChecked : Bool
    productionGeneratorCodecCertified : Bool
open GF2FactorMaskDecoderBoundary public

canonicalGF2FactorMaskDecoderBoundary : GF2FactorMaskDecoderBoundary
canonicalGF2FactorMaskDecoderBoundary =
  gf2-factor-mask-decoder-boundary
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false

------------------------------------------------------------------------
-- Roadmap: generate concrete basis/mask terms for the 28 factor-mode layers,
-- pair them with the independent pre-codec expected rows, and let the equality
-- checker reduce the 224 row expansions.  This avoids trusting the producer's
-- coordinate search while preserving the exact packet semantics.
------------------------------------------------------------------------

data GF2FactorMaskDecoderResidual : Set where
  compileTwentyEightFactorPacketsToAgdaTerms : GF2FactorMaskDecoderResidual
  dischargeTwoHundredTwentyFourRowExpansionEqualities : GF2FactorMaskDecoderResidual
  weldPackedRuntimeBytesToFactorConstructors : GF2FactorMaskDecoderResidual
  provePackedEightBitRowRepresentationExact : GF2FactorMaskDecoderResidual
  compileCertifiedFactorPacketIntoHybridLayerCodec : GF2FactorMaskDecoderResidual
  acquireSameObjectAStarOrFSols : GF2FactorMaskDecoderResidual

firstGF2FactorMaskDecoderResidual : GF2FactorMaskDecoderResidual
firstGF2FactorMaskDecoderResidual = compileTwentyEightFactorPacketsToAgdaTerms

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data DecoderSemanticsMeansProducerSolverProof : Set where
data SampleReductionMeansPortfolioCertificate : Set where
data SyntheticDecoderMeansProductionCustody : Set where

decoderSemanticsDoesNotProveProducerSolver :
  DecoderSemanticsMeansProducerSolverProof → ⊥
decoderSemanticsDoesNotProveProducerSolver ()

sampleReductionDoesNotCreatePortfolioCertificate :
  SampleReductionMeansPortfolioCertificate → ⊥
sampleReductionDoesNotCreatePortfolioCertificate ()

syntheticDecoderDoesNotCreateProductionCustody :
  SyntheticDecoderMeansProductionCustody → ⊥
syntheticDecoderDoesNotCreateProductionCustody ()
