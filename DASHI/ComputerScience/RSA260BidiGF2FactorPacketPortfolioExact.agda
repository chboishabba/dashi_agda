module DASHI.ComputerScience.RSA260BidiGF2FactorPacketPortfolioExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiGF2BasisCoordinateRowCodecExact as Basis
import DASHI.ComputerScience.RSA260BidiGF2FactorMaskDecoderExact as Decoder
import DASHI.ComputerScience.RSA260BidiGF2SelectedBasisExpansionRuntimeReceiptExact as Runtime

------------------------------------------------------------------------
-- FIRST FORMALLY COMPILED FACTOR PACKET
--
-- The runtime receipt covers 28 factor-mode layers / 224 rows.  This source
-- currently compiles only the first factor layer into concrete Agda basis/mask
-- terms.  Its eight row equalities are stated against Decoder.expandMask8 and
-- reduce by refl at source level.  The remaining 27 layers are explicit proof
-- debt; no coverage inflation is allowed.
------------------------------------------------------------------------

runtimeReceipt : Runtime.SelectedBasisExpansionRuntimeReceipt
runtimeReceipt = Runtime.currentSelectedBasisExpansionRuntimeReceipt

identityLayer0Basis : Decoder.FactorBasis8
identityLayer0Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

identityLayer0Row0Mask : Decoder.FactorMask8
identityLayer0Row0Mask = Decoder.factor-mask8 false false false false false false false false

identityLayer0Row0Expected : Basis.GF2Row8
identityLayer0Row0Expected = Basis.gf2-row8 false false false false false false false false

identityLayer0Row0Exact :
  Decoder.expandMask8 identityLayer0Basis identityLayer0Row0Mask
  ≡ identityLayer0Row0Expected
identityLayer0Row0Exact = refl

identityLayer0Row1Mask : Decoder.FactorMask8
identityLayer0Row1Mask = Decoder.factor-mask8 false false false false false false false false

identityLayer0Row1Expected : Basis.GF2Row8
identityLayer0Row1Expected = Basis.gf2-row8 false false false false false false false false

identityLayer0Row1Exact :
  Decoder.expandMask8 identityLayer0Basis identityLayer0Row1Mask
  ≡ identityLayer0Row1Expected
identityLayer0Row1Exact = refl

identityLayer0Row2Mask : Decoder.FactorMask8
identityLayer0Row2Mask = Decoder.factor-mask8 false false false false false false false false

identityLayer0Row2Expected : Basis.GF2Row8
identityLayer0Row2Expected = Basis.gf2-row8 false false false false false false false false

identityLayer0Row2Exact :
  Decoder.expandMask8 identityLayer0Basis identityLayer0Row2Mask
  ≡ identityLayer0Row2Expected
identityLayer0Row2Exact = refl

identityLayer0Row3Mask : Decoder.FactorMask8
identityLayer0Row3Mask = Decoder.factor-mask8 false false false false false false false false

identityLayer0Row3Expected : Basis.GF2Row8
identityLayer0Row3Expected = Basis.gf2-row8 false false false false false false false false

identityLayer0Row3Exact :
  Decoder.expandMask8 identityLayer0Basis identityLayer0Row3Mask
  ≡ identityLayer0Row3Expected
identityLayer0Row3Exact = refl

identityLayer0Row4Mask : Decoder.FactorMask8
identityLayer0Row4Mask = Decoder.factor-mask8 false false false false false false false false

identityLayer0Row4Expected : Basis.GF2Row8
identityLayer0Row4Expected = Basis.gf2-row8 false false false false false false false false

identityLayer0Row4Exact :
  Decoder.expandMask8 identityLayer0Basis identityLayer0Row4Mask
  ≡ identityLayer0Row4Expected
identityLayer0Row4Exact = refl

identityLayer0Row5Mask : Decoder.FactorMask8
identityLayer0Row5Mask = Decoder.factor-mask8 false false false false false false false false

identityLayer0Row5Expected : Basis.GF2Row8
identityLayer0Row5Expected = Basis.gf2-row8 false false false false false false false false

identityLayer0Row5Exact :
  Decoder.expandMask8 identityLayer0Basis identityLayer0Row5Mask
  ≡ identityLayer0Row5Expected
identityLayer0Row5Exact = refl

identityLayer0Row6Mask : Decoder.FactorMask8
identityLayer0Row6Mask = Decoder.factor-mask8 false false false false false false false false

identityLayer0Row6Expected : Basis.GF2Row8
identityLayer0Row6Expected = Basis.gf2-row8 false false false false false false false false

identityLayer0Row6Exact :
  Decoder.expandMask8 identityLayer0Basis identityLayer0Row6Mask
  ≡ identityLayer0Row6Expected
identityLayer0Row6Exact = refl

identityLayer0Row7Mask : Decoder.FactorMask8
identityLayer0Row7Mask = Decoder.factor-mask8 false false false false false false false false

identityLayer0Row7Expected : Basis.GF2Row8
identityLayer0Row7Expected = Basis.gf2-row8 false false false false false false false false

identityLayer0Row7Exact :
  Decoder.expandMask8 identityLayer0Basis identityLayer0Row7Mask
  ≡ identityLayer0Row7Expected
identityLayer0Row7Exact = refl

compiledFactorLayerCount : Nat
compiledFactorLayerCount = 1

compiledFactorLayerCountIsOne : compiledFactorLayerCount ≡ 1
compiledFactorLayerCountIsOne = refl

compiledRowCount : Nat
compiledRowCount = 8

compiledRowCountIsEight : compiledRowCount ≡ 8
compiledRowCountIsEight = refl

runtimeFactorLayerCount : Nat
runtimeFactorLayerCount = 28

runtimeFactorLayerCountIsTwentyEight : runtimeFactorLayerCount ≡ 28
runtimeFactorLayerCountIsTwentyEight = refl

runtimeCheckedRowCount : Nat
runtimeCheckedRowCount = 224

runtimeCheckedRowCountIsTwoHundredTwentyFour : runtimeCheckedRowCount ≡ 224
runtimeCheckedRowCountIsTwoHundredTwentyFour = refl

record GF2FactorPacketPortfolioBoundary : Set where
  constructor gf2-factor-packet-portfolio-boundary
  field
    independentPrecodecRuntimeReceiptInherited : Bool
    runtimeTwentyEightFactorLayersPaid : Bool
    runtimeTwoHundredTwentyFourRowsPaid : Bool
    oneFactorLayerCompiledToFormalTerms : Bool
    eightFormalRowEqualitiesSourceWritten : Bool
    fullTwentyEightLayerPortfolioCompiled : Bool
    exactHeadAgdaKernelReceiptObserved : Bool
    producerBasisSearchAlgorithmProved : Bool
    packedRuntimeBytesWeldedToFormalConstructors : Bool
    productionRSA260CustodyPaid : Bool
open GF2FactorPacketPortfolioBoundary public

canonicalGF2FactorPacketPortfolioBoundary : GF2FactorPacketPortfolioBoundary
canonicalGF2FactorPacketPortfolioBoundary =
  gf2-factor-packet-portfolio-boundary
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

data GF2FactorPacketPortfolioResidual : Set where
  compileRemainingTwentySevenFactorPackets : GF2FactorPacketPortfolioResidual
  obtainExactHeadAgdaKernelReceiptForCompiledPortfolio : GF2FactorPacketPortfolioResidual
  weldPackedRuntimeBytesToFormalFactorConstructors : GF2FactorPacketPortfolioResidual
  provePackedEightBitRowRepresentationExact : GF2FactorPacketPortfolioResidual
  compileCertifiedFactorPacketsIntoHybridLayerCodec : GF2FactorPacketPortfolioResidual
  acquireSameObjectAStarOrFSols : GF2FactorPacketPortfolioResidual

firstGF2FactorPacketPortfolioResidual : GF2FactorPacketPortfolioResidual
firstGF2FactorPacketPortfolioResidual = compileRemainingTwentySevenFactorPackets

data SourceWrittenReflMeansKernelReceipt : Set where
data OneLayerMeansFullPortfolio : Set where
data SyntheticFactorPortfolioMeansProductionCustody : Set where

sourceWrittenReflDoesNotCreateKernelReceipt :
  SourceWrittenReflMeansKernelReceipt → ⊥
sourceWrittenReflDoesNotCreateKernelReceipt ()

oneLayerDoesNotCreateFullPortfolio : OneLayerMeansFullPortfolio → ⊥
oneLayerDoesNotCreateFullPortfolio ()

syntheticFactorPortfolioDoesNotCreateProductionCustody :
  SyntheticFactorPortfolioMeansProductionCustody → ⊥
syntheticFactorPortfolioDoesNotCreateProductionCustody ()
