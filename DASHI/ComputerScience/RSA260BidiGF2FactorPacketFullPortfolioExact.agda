module DASHI.ComputerScience.RSA260BidiGF2FactorPacketFullPortfolioExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiGF2BasisCoordinateRowCodecExact as Basis
import DASHI.ComputerScience.RSA260BidiGF2FactorMaskDecoderExact as Decoder
import DASHI.ComputerScience.RSA260BidiGF2SelectedBasisExpansionRuntimeReceiptExact as Runtime

------------------------------------------------------------------------
-- FULL FORMALLY COMPILED FACTOR-PACKET PORTFOLIO
--
-- This owner compiles all 28 factor-mode layers / 224 rows from the
-- independent pre-codec/runtime certificate portfolio into concrete Agda
-- basis/mask/expected-row terms. Each row theorem reduces through
-- Decoder.expandMask8 by refl. This pays source-level finite replay coverage;
-- it does not create an exact-head kernel receipt, a packed-byte weld theorem,
-- producer solver correctness, or production RSA-260 custody.
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

identityLayer1Basis : Decoder.FactorBasis8
identityLayer1Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false false false true false false true false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

identityLayer1Row0Mask : Decoder.FactorMask8
identityLayer1Row0Mask = Decoder.factor-mask8 false false false false false false false false

identityLayer1Row0Expected : Basis.GF2Row8
identityLayer1Row0Expected = Basis.gf2-row8 false false false false false false false false

identityLayer1Row0Exact :
  Decoder.expandMask8 identityLayer1Basis identityLayer1Row0Mask
  ≡ identityLayer1Row0Expected
identityLayer1Row0Exact = refl

identityLayer1Row1Mask : Decoder.FactorMask8
identityLayer1Row1Mask = Decoder.factor-mask8 true false false false false false false false

identityLayer1Row1Expected : Basis.GF2Row8
identityLayer1Row1Expected = Basis.gf2-row8 false false false true false false true false

identityLayer1Row1Exact :
  Decoder.expandMask8 identityLayer1Basis identityLayer1Row1Mask
  ≡ identityLayer1Row1Expected
identityLayer1Row1Exact = refl

identityLayer1Row2Mask : Decoder.FactorMask8
identityLayer1Row2Mask = Decoder.factor-mask8 false false false false false false false false

identityLayer1Row2Expected : Basis.GF2Row8
identityLayer1Row2Expected = Basis.gf2-row8 false false false false false false false false

identityLayer1Row2Exact :
  Decoder.expandMask8 identityLayer1Basis identityLayer1Row2Mask
  ≡ identityLayer1Row2Expected
identityLayer1Row2Exact = refl

identityLayer1Row3Mask : Decoder.FactorMask8
identityLayer1Row3Mask = Decoder.factor-mask8 false false false false false false false false

identityLayer1Row3Expected : Basis.GF2Row8
identityLayer1Row3Expected = Basis.gf2-row8 false false false false false false false false

identityLayer1Row3Exact :
  Decoder.expandMask8 identityLayer1Basis identityLayer1Row3Mask
  ≡ identityLayer1Row3Expected
identityLayer1Row3Exact = refl

identityLayer1Row4Mask : Decoder.FactorMask8
identityLayer1Row4Mask = Decoder.factor-mask8 false false false false false false false false

identityLayer1Row4Expected : Basis.GF2Row8
identityLayer1Row4Expected = Basis.gf2-row8 false false false false false false false false

identityLayer1Row4Exact :
  Decoder.expandMask8 identityLayer1Basis identityLayer1Row4Mask
  ≡ identityLayer1Row4Expected
identityLayer1Row4Exact = refl

identityLayer1Row5Mask : Decoder.FactorMask8
identityLayer1Row5Mask = Decoder.factor-mask8 false false false false false false false false

identityLayer1Row5Expected : Basis.GF2Row8
identityLayer1Row5Expected = Basis.gf2-row8 false false false false false false false false

identityLayer1Row5Exact :
  Decoder.expandMask8 identityLayer1Basis identityLayer1Row5Mask
  ≡ identityLayer1Row5Expected
identityLayer1Row5Exact = refl

identityLayer1Row6Mask : Decoder.FactorMask8
identityLayer1Row6Mask = Decoder.factor-mask8 false false false false false false false false

identityLayer1Row6Expected : Basis.GF2Row8
identityLayer1Row6Expected = Basis.gf2-row8 false false false false false false false false

identityLayer1Row6Exact :
  Decoder.expandMask8 identityLayer1Basis identityLayer1Row6Mask
  ≡ identityLayer1Row6Expected
identityLayer1Row6Exact = refl

identityLayer1Row7Mask : Decoder.FactorMask8
identityLayer1Row7Mask = Decoder.factor-mask8 false false false false false false false false

identityLayer1Row7Expected : Basis.GF2Row8
identityLayer1Row7Expected = Basis.gf2-row8 false false false false false false false false

identityLayer1Row7Exact :
  Decoder.expandMask8 identityLayer1Basis identityLayer1Row7Mask
  ≡ identityLayer1Row7Expected
identityLayer1Row7Exact = refl

identityLayer16Basis : Decoder.FactorBasis8
identityLayer16Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 true true false false true false true false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

identityLayer16Row0Mask : Decoder.FactorMask8
identityLayer16Row0Mask = Decoder.factor-mask8 false false false false false false false false

identityLayer16Row0Expected : Basis.GF2Row8
identityLayer16Row0Expected = Basis.gf2-row8 false false false false false false false false

identityLayer16Row0Exact :
  Decoder.expandMask8 identityLayer16Basis identityLayer16Row0Mask
  ≡ identityLayer16Row0Expected
identityLayer16Row0Exact = refl

identityLayer16Row1Mask : Decoder.FactorMask8
identityLayer16Row1Mask = Decoder.factor-mask8 false false false false false false false false

identityLayer16Row1Expected : Basis.GF2Row8
identityLayer16Row1Expected = Basis.gf2-row8 false false false false false false false false

identityLayer16Row1Exact :
  Decoder.expandMask8 identityLayer16Basis identityLayer16Row1Mask
  ≡ identityLayer16Row1Expected
identityLayer16Row1Exact = refl

identityLayer16Row2Mask : Decoder.FactorMask8
identityLayer16Row2Mask = Decoder.factor-mask8 false false false false false false false false

identityLayer16Row2Expected : Basis.GF2Row8
identityLayer16Row2Expected = Basis.gf2-row8 false false false false false false false false

identityLayer16Row2Exact :
  Decoder.expandMask8 identityLayer16Basis identityLayer16Row2Mask
  ≡ identityLayer16Row2Expected
identityLayer16Row2Exact = refl

identityLayer16Row3Mask : Decoder.FactorMask8
identityLayer16Row3Mask = Decoder.factor-mask8 false false false false false false false false

identityLayer16Row3Expected : Basis.GF2Row8
identityLayer16Row3Expected = Basis.gf2-row8 false false false false false false false false

identityLayer16Row3Exact :
  Decoder.expandMask8 identityLayer16Basis identityLayer16Row3Mask
  ≡ identityLayer16Row3Expected
identityLayer16Row3Exact = refl

identityLayer16Row4Mask : Decoder.FactorMask8
identityLayer16Row4Mask = Decoder.factor-mask8 false false false false false false false false

identityLayer16Row4Expected : Basis.GF2Row8
identityLayer16Row4Expected = Basis.gf2-row8 false false false false false false false false

identityLayer16Row4Exact :
  Decoder.expandMask8 identityLayer16Basis identityLayer16Row4Mask
  ≡ identityLayer16Row4Expected
identityLayer16Row4Exact = refl

identityLayer16Row5Mask : Decoder.FactorMask8
identityLayer16Row5Mask = Decoder.factor-mask8 false false false false false false false false

identityLayer16Row5Expected : Basis.GF2Row8
identityLayer16Row5Expected = Basis.gf2-row8 false false false false false false false false

identityLayer16Row5Exact :
  Decoder.expandMask8 identityLayer16Basis identityLayer16Row5Mask
  ≡ identityLayer16Row5Expected
identityLayer16Row5Exact = refl

identityLayer16Row6Mask : Decoder.FactorMask8
identityLayer16Row6Mask = Decoder.factor-mask8 true false false false false false false false

identityLayer16Row6Expected : Basis.GF2Row8
identityLayer16Row6Expected = Basis.gf2-row8 true true false false true false true false

identityLayer16Row6Exact :
  Decoder.expandMask8 identityLayer16Basis identityLayer16Row6Mask
  ≡ identityLayer16Row6Expected
identityLayer16Row6Exact = refl

identityLayer16Row7Mask : Decoder.FactorMask8
identityLayer16Row7Mask = Decoder.factor-mask8 false false false false false false false false

identityLayer16Row7Expected : Basis.GF2Row8
identityLayer16Row7Expected = Basis.gf2-row8 false false false false false false false false

identityLayer16Row7Exact :
  Decoder.expandMask8 identityLayer16Basis identityLayer16Row7Mask
  ≡ identityLayer16Row7Expected
identityLayer16Row7Exact = refl

rotate1Layer0Basis : Decoder.FactorBasis8
rotate1Layer0Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

rotate1Layer0Row0Mask : Decoder.FactorMask8
rotate1Layer0Row0Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer0Row0Expected : Basis.GF2Row8
rotate1Layer0Row0Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer0Row0Exact :
  Decoder.expandMask8 rotate1Layer0Basis rotate1Layer0Row0Mask
  ≡ rotate1Layer0Row0Expected
rotate1Layer0Row0Exact = refl

rotate1Layer0Row1Mask : Decoder.FactorMask8
rotate1Layer0Row1Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer0Row1Expected : Basis.GF2Row8
rotate1Layer0Row1Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer0Row1Exact :
  Decoder.expandMask8 rotate1Layer0Basis rotate1Layer0Row1Mask
  ≡ rotate1Layer0Row1Expected
rotate1Layer0Row1Exact = refl

rotate1Layer0Row2Mask : Decoder.FactorMask8
rotate1Layer0Row2Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer0Row2Expected : Basis.GF2Row8
rotate1Layer0Row2Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer0Row2Exact :
  Decoder.expandMask8 rotate1Layer0Basis rotate1Layer0Row2Mask
  ≡ rotate1Layer0Row2Expected
rotate1Layer0Row2Exact = refl

rotate1Layer0Row3Mask : Decoder.FactorMask8
rotate1Layer0Row3Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer0Row3Expected : Basis.GF2Row8
rotate1Layer0Row3Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer0Row3Exact :
  Decoder.expandMask8 rotate1Layer0Basis rotate1Layer0Row3Mask
  ≡ rotate1Layer0Row3Expected
rotate1Layer0Row3Exact = refl

rotate1Layer0Row4Mask : Decoder.FactorMask8
rotate1Layer0Row4Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer0Row4Expected : Basis.GF2Row8
rotate1Layer0Row4Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer0Row4Exact :
  Decoder.expandMask8 rotate1Layer0Basis rotate1Layer0Row4Mask
  ≡ rotate1Layer0Row4Expected
rotate1Layer0Row4Exact = refl

rotate1Layer0Row5Mask : Decoder.FactorMask8
rotate1Layer0Row5Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer0Row5Expected : Basis.GF2Row8
rotate1Layer0Row5Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer0Row5Exact :
  Decoder.expandMask8 rotate1Layer0Basis rotate1Layer0Row5Mask
  ≡ rotate1Layer0Row5Expected
rotate1Layer0Row5Exact = refl

rotate1Layer0Row6Mask : Decoder.FactorMask8
rotate1Layer0Row6Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer0Row6Expected : Basis.GF2Row8
rotate1Layer0Row6Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer0Row6Exact :
  Decoder.expandMask8 rotate1Layer0Basis rotate1Layer0Row6Mask
  ≡ rotate1Layer0Row6Expected
rotate1Layer0Row6Exact = refl

rotate1Layer0Row7Mask : Decoder.FactorMask8
rotate1Layer0Row7Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer0Row7Expected : Basis.GF2Row8
rotate1Layer0Row7Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer0Row7Exact :
  Decoder.expandMask8 rotate1Layer0Basis rotate1Layer0Row7Mask
  ≡ rotate1Layer0Row7Expected
rotate1Layer0Row7Exact = refl

rotate1Layer1Basis : Decoder.FactorBasis8
rotate1Layer1Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

rotate1Layer1Row0Mask : Decoder.FactorMask8
rotate1Layer1Row0Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer1Row0Expected : Basis.GF2Row8
rotate1Layer1Row0Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer1Row0Exact :
  Decoder.expandMask8 rotate1Layer1Basis rotate1Layer1Row0Mask
  ≡ rotate1Layer1Row0Expected
rotate1Layer1Row0Exact = refl

rotate1Layer1Row1Mask : Decoder.FactorMask8
rotate1Layer1Row1Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer1Row1Expected : Basis.GF2Row8
rotate1Layer1Row1Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer1Row1Exact :
  Decoder.expandMask8 rotate1Layer1Basis rotate1Layer1Row1Mask
  ≡ rotate1Layer1Row1Expected
rotate1Layer1Row1Exact = refl

rotate1Layer1Row2Mask : Decoder.FactorMask8
rotate1Layer1Row2Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer1Row2Expected : Basis.GF2Row8
rotate1Layer1Row2Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer1Row2Exact :
  Decoder.expandMask8 rotate1Layer1Basis rotate1Layer1Row2Mask
  ≡ rotate1Layer1Row2Expected
rotate1Layer1Row2Exact = refl

rotate1Layer1Row3Mask : Decoder.FactorMask8
rotate1Layer1Row3Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer1Row3Expected : Basis.GF2Row8
rotate1Layer1Row3Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer1Row3Exact :
  Decoder.expandMask8 rotate1Layer1Basis rotate1Layer1Row3Mask
  ≡ rotate1Layer1Row3Expected
rotate1Layer1Row3Exact = refl

rotate1Layer1Row4Mask : Decoder.FactorMask8
rotate1Layer1Row4Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer1Row4Expected : Basis.GF2Row8
rotate1Layer1Row4Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer1Row4Exact :
  Decoder.expandMask8 rotate1Layer1Basis rotate1Layer1Row4Mask
  ≡ rotate1Layer1Row4Expected
rotate1Layer1Row4Exact = refl

rotate1Layer1Row5Mask : Decoder.FactorMask8
rotate1Layer1Row5Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer1Row5Expected : Basis.GF2Row8
rotate1Layer1Row5Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer1Row5Exact :
  Decoder.expandMask8 rotate1Layer1Basis rotate1Layer1Row5Mask
  ≡ rotate1Layer1Row5Expected
rotate1Layer1Row5Exact = refl

rotate1Layer1Row6Mask : Decoder.FactorMask8
rotate1Layer1Row6Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer1Row6Expected : Basis.GF2Row8
rotate1Layer1Row6Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer1Row6Exact :
  Decoder.expandMask8 rotate1Layer1Basis rotate1Layer1Row6Mask
  ≡ rotate1Layer1Row6Expected
rotate1Layer1Row6Exact = refl

rotate1Layer1Row7Mask : Decoder.FactorMask8
rotate1Layer1Row7Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer1Row7Expected : Basis.GF2Row8
rotate1Layer1Row7Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer1Row7Exact :
  Decoder.expandMask8 rotate1Layer1Basis rotate1Layer1Row7Mask
  ≡ rotate1Layer1Row7Expected
rotate1Layer1Row7Exact = refl

rotate1Layer2Basis : Decoder.FactorBasis8
rotate1Layer2Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 true false false false true false false false)
    (Basis.gf2-row8 true false false true true false false true)
    (Basis.gf2-row8 true false false true false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

rotate1Layer2Row0Mask : Decoder.FactorMask8
rotate1Layer2Row0Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer2Row0Expected : Basis.GF2Row8
rotate1Layer2Row0Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer2Row0Exact :
  Decoder.expandMask8 rotate1Layer2Basis rotate1Layer2Row0Mask
  ≡ rotate1Layer2Row0Expected
rotate1Layer2Row0Exact = refl

rotate1Layer2Row1Mask : Decoder.FactorMask8
rotate1Layer2Row1Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer2Row1Expected : Basis.GF2Row8
rotate1Layer2Row1Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer2Row1Exact :
  Decoder.expandMask8 rotate1Layer2Basis rotate1Layer2Row1Mask
  ≡ rotate1Layer2Row1Expected
rotate1Layer2Row1Exact = refl

rotate1Layer2Row2Mask : Decoder.FactorMask8
rotate1Layer2Row2Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer2Row2Expected : Basis.GF2Row8
rotate1Layer2Row2Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer2Row2Exact :
  Decoder.expandMask8 rotate1Layer2Basis rotate1Layer2Row2Mask
  ≡ rotate1Layer2Row2Expected
rotate1Layer2Row2Exact = refl

rotate1Layer2Row3Mask : Decoder.FactorMask8
rotate1Layer2Row3Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer2Row3Expected : Basis.GF2Row8
rotate1Layer2Row3Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer2Row3Exact :
  Decoder.expandMask8 rotate1Layer2Basis rotate1Layer2Row3Mask
  ≡ rotate1Layer2Row3Expected
rotate1Layer2Row3Exact = refl

rotate1Layer2Row4Mask : Decoder.FactorMask8
rotate1Layer2Row4Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer2Row4Expected : Basis.GF2Row8
rotate1Layer2Row4Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer2Row4Exact :
  Decoder.expandMask8 rotate1Layer2Basis rotate1Layer2Row4Mask
  ≡ rotate1Layer2Row4Expected
rotate1Layer2Row4Exact = refl

rotate1Layer2Row5Mask : Decoder.FactorMask8
rotate1Layer2Row5Mask = Decoder.factor-mask8 true false false false false false false false

rotate1Layer2Row5Expected : Basis.GF2Row8
rotate1Layer2Row5Expected = Basis.gf2-row8 true false false false true false false false

rotate1Layer2Row5Exact :
  Decoder.expandMask8 rotate1Layer2Basis rotate1Layer2Row5Mask
  ≡ rotate1Layer2Row5Expected
rotate1Layer2Row5Exact = refl

rotate1Layer2Row6Mask : Decoder.FactorMask8
rotate1Layer2Row6Mask = Decoder.factor-mask8 false true false false false false false false

rotate1Layer2Row6Expected : Basis.GF2Row8
rotate1Layer2Row6Expected = Basis.gf2-row8 true false false true true false false true

rotate1Layer2Row6Exact :
  Decoder.expandMask8 rotate1Layer2Basis rotate1Layer2Row6Mask
  ≡ rotate1Layer2Row6Expected
rotate1Layer2Row6Exact = refl

rotate1Layer2Row7Mask : Decoder.FactorMask8
rotate1Layer2Row7Mask = Decoder.factor-mask8 false false true false false false false false

rotate1Layer2Row7Expected : Basis.GF2Row8
rotate1Layer2Row7Expected = Basis.gf2-row8 true false false true false false false false

rotate1Layer2Row7Exact :
  Decoder.expandMask8 rotate1Layer2Basis rotate1Layer2Row7Mask
  ≡ rotate1Layer2Row7Expected
rotate1Layer2Row7Exact = refl

rotate1Layer16Basis : Decoder.FactorBasis8
rotate1Layer16Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false false false false false false true false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

rotate1Layer16Row0Mask : Decoder.FactorMask8
rotate1Layer16Row0Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer16Row0Expected : Basis.GF2Row8
rotate1Layer16Row0Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer16Row0Exact :
  Decoder.expandMask8 rotate1Layer16Basis rotate1Layer16Row0Mask
  ≡ rotate1Layer16Row0Expected
rotate1Layer16Row0Exact = refl

rotate1Layer16Row1Mask : Decoder.FactorMask8
rotate1Layer16Row1Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer16Row1Expected : Basis.GF2Row8
rotate1Layer16Row1Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer16Row1Exact :
  Decoder.expandMask8 rotate1Layer16Basis rotate1Layer16Row1Mask
  ≡ rotate1Layer16Row1Expected
rotate1Layer16Row1Exact = refl

rotate1Layer16Row2Mask : Decoder.FactorMask8
rotate1Layer16Row2Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer16Row2Expected : Basis.GF2Row8
rotate1Layer16Row2Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer16Row2Exact :
  Decoder.expandMask8 rotate1Layer16Basis rotate1Layer16Row2Mask
  ≡ rotate1Layer16Row2Expected
rotate1Layer16Row2Exact = refl

rotate1Layer16Row3Mask : Decoder.FactorMask8
rotate1Layer16Row3Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer16Row3Expected : Basis.GF2Row8
rotate1Layer16Row3Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer16Row3Exact :
  Decoder.expandMask8 rotate1Layer16Basis rotate1Layer16Row3Mask
  ≡ rotate1Layer16Row3Expected
rotate1Layer16Row3Exact = refl

rotate1Layer16Row4Mask : Decoder.FactorMask8
rotate1Layer16Row4Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer16Row4Expected : Basis.GF2Row8
rotate1Layer16Row4Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer16Row4Exact :
  Decoder.expandMask8 rotate1Layer16Basis rotate1Layer16Row4Mask
  ≡ rotate1Layer16Row4Expected
rotate1Layer16Row4Exact = refl

rotate1Layer16Row5Mask : Decoder.FactorMask8
rotate1Layer16Row5Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer16Row5Expected : Basis.GF2Row8
rotate1Layer16Row5Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer16Row5Exact :
  Decoder.expandMask8 rotate1Layer16Basis rotate1Layer16Row5Mask
  ≡ rotate1Layer16Row5Expected
rotate1Layer16Row5Exact = refl

rotate1Layer16Row6Mask : Decoder.FactorMask8
rotate1Layer16Row6Mask = Decoder.factor-mask8 false false false false false false false false

rotate1Layer16Row6Expected : Basis.GF2Row8
rotate1Layer16Row6Expected = Basis.gf2-row8 false false false false false false false false

rotate1Layer16Row6Exact :
  Decoder.expandMask8 rotate1Layer16Basis rotate1Layer16Row6Mask
  ≡ rotate1Layer16Row6Expected
rotate1Layer16Row6Exact = refl

rotate1Layer16Row7Mask : Decoder.FactorMask8
rotate1Layer16Row7Mask = Decoder.factor-mask8 true false false false false false false false

rotate1Layer16Row7Expected : Basis.GF2Row8
rotate1Layer16Row7Expected = Basis.gf2-row8 false false false false false false true false

rotate1Layer16Row7Exact :
  Decoder.expandMask8 rotate1Layer16Basis rotate1Layer16Row7Mask
  ≡ rotate1Layer16Row7Expected
rotate1Layer16Row7Exact = refl

rotate2Layer0Basis : Decoder.FactorBasis8
rotate2Layer0Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false false false true false false true false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

rotate2Layer0Row0Mask : Decoder.FactorMask8
rotate2Layer0Row0Mask = Decoder.factor-mask8 false false false false false false false false

rotate2Layer0Row0Expected : Basis.GF2Row8
rotate2Layer0Row0Expected = Basis.gf2-row8 false false false false false false false false

rotate2Layer0Row0Exact :
  Decoder.expandMask8 rotate2Layer0Basis rotate2Layer0Row0Mask
  ≡ rotate2Layer0Row0Expected
rotate2Layer0Row0Exact = refl

rotate2Layer0Row1Mask : Decoder.FactorMask8
rotate2Layer0Row1Mask = Decoder.factor-mask8 true false false false false false false false

rotate2Layer0Row1Expected : Basis.GF2Row8
rotate2Layer0Row1Expected = Basis.gf2-row8 false false false true false false true false

rotate2Layer0Row1Exact :
  Decoder.expandMask8 rotate2Layer0Basis rotate2Layer0Row1Mask
  ≡ rotate2Layer0Row1Expected
rotate2Layer0Row1Exact = refl

rotate2Layer0Row2Mask : Decoder.FactorMask8
rotate2Layer0Row2Mask = Decoder.factor-mask8 false false false false false false false false

rotate2Layer0Row2Expected : Basis.GF2Row8
rotate2Layer0Row2Expected = Basis.gf2-row8 false false false false false false false false

rotate2Layer0Row2Exact :
  Decoder.expandMask8 rotate2Layer0Basis rotate2Layer0Row2Mask
  ≡ rotate2Layer0Row2Expected
rotate2Layer0Row2Exact = refl

rotate2Layer0Row3Mask : Decoder.FactorMask8
rotate2Layer0Row3Mask = Decoder.factor-mask8 false false false false false false false false

rotate2Layer0Row3Expected : Basis.GF2Row8
rotate2Layer0Row3Expected = Basis.gf2-row8 false false false false false false false false

rotate2Layer0Row3Exact :
  Decoder.expandMask8 rotate2Layer0Basis rotate2Layer0Row3Mask
  ≡ rotate2Layer0Row3Expected
rotate2Layer0Row3Exact = refl

rotate2Layer0Row4Mask : Decoder.FactorMask8
rotate2Layer0Row4Mask = Decoder.factor-mask8 false false false false false false false false

rotate2Layer0Row4Expected : Basis.GF2Row8
rotate2Layer0Row4Expected = Basis.gf2-row8 false false false false false false false false

rotate2Layer0Row4Exact :
  Decoder.expandMask8 rotate2Layer0Basis rotate2Layer0Row4Mask
  ≡ rotate2Layer0Row4Expected
rotate2Layer0Row4Exact = refl

rotate2Layer0Row5Mask : Decoder.FactorMask8
rotate2Layer0Row5Mask = Decoder.factor-mask8 false false false false false false false false

rotate2Layer0Row5Expected : Basis.GF2Row8
rotate2Layer0Row5Expected = Basis.gf2-row8 false false false false false false false false

rotate2Layer0Row5Exact :
  Decoder.expandMask8 rotate2Layer0Basis rotate2Layer0Row5Mask
  ≡ rotate2Layer0Row5Expected
rotate2Layer0Row5Exact = refl

rotate2Layer0Row6Mask : Decoder.FactorMask8
rotate2Layer0Row6Mask = Decoder.factor-mask8 false false false false false false false false

rotate2Layer0Row6Expected : Basis.GF2Row8
rotate2Layer0Row6Expected = Basis.gf2-row8 false false false false false false false false

rotate2Layer0Row6Exact :
  Decoder.expandMask8 rotate2Layer0Basis rotate2Layer0Row6Mask
  ≡ rotate2Layer0Row6Expected
rotate2Layer0Row6Exact = refl

rotate2Layer0Row7Mask : Decoder.FactorMask8
rotate2Layer0Row7Mask = Decoder.factor-mask8 false false false false false false false false

rotate2Layer0Row7Expected : Basis.GF2Row8
rotate2Layer0Row7Expected = Basis.gf2-row8 false false false false false false false false

rotate2Layer0Row7Exact :
  Decoder.expandMask8 rotate2Layer0Basis rotate2Layer0Row7Mask
  ≡ rotate2Layer0Row7Expected
rotate2Layer0Row7Exact = refl

rotate2Layer1Basis : Decoder.FactorBasis8
rotate2Layer1Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false true false false true true false true)
    (Basis.gf2-row8 false true true false true true true false)
    (Basis.gf2-row8 false true true true true true false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

rotate2Layer1Row0Mask : Decoder.FactorMask8
rotate2Layer1Row0Mask = Decoder.factor-mask8 false false false false false false false false

rotate2Layer1Row0Expected : Basis.GF2Row8
rotate2Layer1Row0Expected = Basis.gf2-row8 false false false false false false false false

rotate2Layer1Row0Exact :
  Decoder.expandMask8 rotate2Layer1Basis rotate2Layer1Row0Mask
  ≡ rotate2Layer1Row0Expected
rotate2Layer1Row0Exact = refl

rotate2Layer1Row1Mask : Decoder.FactorMask8
rotate2Layer1Row1Mask = Decoder.factor-mask8 true false false false false false false false

rotate2Layer1Row1Expected : Basis.GF2Row8
rotate2Layer1Row1Expected = Basis.gf2-row8 false true false false true true false true

rotate2Layer1Row1Exact :
  Decoder.expandMask8 rotate2Layer1Basis rotate2Layer1Row1Mask
  ≡ rotate2Layer1Row1Expected
rotate2Layer1Row1Exact = refl

rotate2Layer1Row2Mask : Decoder.FactorMask8
rotate2Layer1Row2Mask = Decoder.factor-mask8 false true false false false false false false

rotate2Layer1Row2Expected : Basis.GF2Row8
rotate2Layer1Row2Expected = Basis.gf2-row8 false true true false true true true false

rotate2Layer1Row2Exact :
  Decoder.expandMask8 rotate2Layer1Basis rotate2Layer1Row2Mask
  ≡ rotate2Layer1Row2Expected
rotate2Layer1Row2Exact = refl

rotate2Layer1Row3Mask : Decoder.FactorMask8
rotate2Layer1Row3Mask = Decoder.factor-mask8 false false true false false false false false

rotate2Layer1Row3Expected : Basis.GF2Row8
rotate2Layer1Row3Expected = Basis.gf2-row8 false true true true true true false false

rotate2Layer1Row3Exact :
  Decoder.expandMask8 rotate2Layer1Basis rotate2Layer1Row3Mask
  ≡ rotate2Layer1Row3Expected
rotate2Layer1Row3Exact = refl

rotate2Layer1Row4Mask : Decoder.FactorMask8
rotate2Layer1Row4Mask = Decoder.factor-mask8 true true false false false false false false

rotate2Layer1Row4Expected : Basis.GF2Row8
rotate2Layer1Row4Expected = Basis.gf2-row8 false false true false false false true true

rotate2Layer1Row4Exact :
  Decoder.expandMask8 rotate2Layer1Basis rotate2Layer1Row4Mask
  ≡ rotate2Layer1Row4Expected
rotate2Layer1Row4Exact = refl

rotate2Layer1Row5Mask : Decoder.FactorMask8
rotate2Layer1Row5Mask = Decoder.factor-mask8 true false true false false false false false

rotate2Layer1Row5Expected : Basis.GF2Row8
rotate2Layer1Row5Expected = Basis.gf2-row8 false false true true false false false true

rotate2Layer1Row5Exact :
  Decoder.expandMask8 rotate2Layer1Basis rotate2Layer1Row5Mask
  ≡ rotate2Layer1Row5Expected
rotate2Layer1Row5Exact = refl

rotate2Layer1Row6Mask : Decoder.FactorMask8
rotate2Layer1Row6Mask = Decoder.factor-mask8 false true true false false false false false

rotate2Layer1Row6Expected : Basis.GF2Row8
rotate2Layer1Row6Expected = Basis.gf2-row8 false false false true false false true false

rotate2Layer1Row6Exact :
  Decoder.expandMask8 rotate2Layer1Basis rotate2Layer1Row6Mask
  ≡ rotate2Layer1Row6Expected
rotate2Layer1Row6Exact = refl

rotate2Layer1Row7Mask : Decoder.FactorMask8
rotate2Layer1Row7Mask = Decoder.factor-mask8 true true true false false false false false

rotate2Layer1Row7Expected : Basis.GF2Row8
rotate2Layer1Row7Expected = Basis.gf2-row8 false true false true true true false true

rotate2Layer1Row7Exact :
  Decoder.expandMask8 rotate2Layer1Basis rotate2Layer1Row7Mask
  ≡ rotate2Layer1Row7Expected
rotate2Layer1Row7Exact = refl

rotate2Layer15Basis : Decoder.FactorBasis8
rotate2Layer15Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false false true true false true true true)
    (Basis.gf2-row8 false true true true true false true false)
    (Basis.gf2-row8 false true true true false true false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

rotate2Layer15Row0Mask : Decoder.FactorMask8
rotate2Layer15Row0Mask = Decoder.factor-mask8 false false false false false false false false

rotate2Layer15Row0Expected : Basis.GF2Row8
rotate2Layer15Row0Expected = Basis.gf2-row8 false false false false false false false false

rotate2Layer15Row0Exact :
  Decoder.expandMask8 rotate2Layer15Basis rotate2Layer15Row0Mask
  ≡ rotate2Layer15Row0Expected
rotate2Layer15Row0Exact = refl

rotate2Layer15Row1Mask : Decoder.FactorMask8
rotate2Layer15Row1Mask = Decoder.factor-mask8 true false false false false false false false

rotate2Layer15Row1Expected : Basis.GF2Row8
rotate2Layer15Row1Expected = Basis.gf2-row8 false false true true false true true true

rotate2Layer15Row1Exact :
  Decoder.expandMask8 rotate2Layer15Basis rotate2Layer15Row1Mask
  ≡ rotate2Layer15Row1Expected
rotate2Layer15Row1Exact = refl

rotate2Layer15Row2Mask : Decoder.FactorMask8
rotate2Layer15Row2Mask = Decoder.factor-mask8 false true false false false false false false

rotate2Layer15Row2Expected : Basis.GF2Row8
rotate2Layer15Row2Expected = Basis.gf2-row8 false true true true true false true false

rotate2Layer15Row2Exact :
  Decoder.expandMask8 rotate2Layer15Basis rotate2Layer15Row2Mask
  ≡ rotate2Layer15Row2Expected
rotate2Layer15Row2Exact = refl

rotate2Layer15Row3Mask : Decoder.FactorMask8
rotate2Layer15Row3Mask = Decoder.factor-mask8 false false true false false false false false

rotate2Layer15Row3Expected : Basis.GF2Row8
rotate2Layer15Row3Expected = Basis.gf2-row8 false true true true false true false false

rotate2Layer15Row3Exact :
  Decoder.expandMask8 rotate2Layer15Basis rotate2Layer15Row3Mask
  ≡ rotate2Layer15Row3Expected
rotate2Layer15Row3Exact = refl

rotate2Layer15Row4Mask : Decoder.FactorMask8
rotate2Layer15Row4Mask = Decoder.factor-mask8 true true false false false false false false

rotate2Layer15Row4Expected : Basis.GF2Row8
rotate2Layer15Row4Expected = Basis.gf2-row8 false true false false true true false true

rotate2Layer15Row4Exact :
  Decoder.expandMask8 rotate2Layer15Basis rotate2Layer15Row4Mask
  ≡ rotate2Layer15Row4Expected
rotate2Layer15Row4Exact = refl

rotate2Layer15Row5Mask : Decoder.FactorMask8
rotate2Layer15Row5Mask = Decoder.factor-mask8 true false true false false false false false

rotate2Layer15Row5Expected : Basis.GF2Row8
rotate2Layer15Row5Expected = Basis.gf2-row8 false true false false false false true true

rotate2Layer15Row5Exact :
  Decoder.expandMask8 rotate2Layer15Basis rotate2Layer15Row5Mask
  ≡ rotate2Layer15Row5Expected
rotate2Layer15Row5Exact = refl

rotate2Layer15Row6Mask : Decoder.FactorMask8
rotate2Layer15Row6Mask = Decoder.factor-mask8 false true true false false false false false

rotate2Layer15Row6Expected : Basis.GF2Row8
rotate2Layer15Row6Expected = Basis.gf2-row8 false false false false true true true false

rotate2Layer15Row6Exact :
  Decoder.expandMask8 rotate2Layer15Basis rotate2Layer15Row6Mask
  ≡ rotate2Layer15Row6Expected
rotate2Layer15Row6Exact = refl

rotate2Layer15Row7Mask : Decoder.FactorMask8
rotate2Layer15Row7Mask = Decoder.factor-mask8 true true true false false false false false

rotate2Layer15Row7Expected : Basis.GF2Row8
rotate2Layer15Row7Expected = Basis.gf2-row8 false false true true true false false true

rotate2Layer15Row7Exact :
  Decoder.expandMask8 rotate2Layer15Basis rotate2Layer15Row7Mask
  ≡ rotate2Layer15Row7Expected
rotate2Layer15Row7Exact = refl

rotate3Layer0Basis : Decoder.FactorBasis8
rotate3Layer0Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

rotate3Layer0Row0Mask : Decoder.FactorMask8
rotate3Layer0Row0Mask = Decoder.factor-mask8 false false false false false false false false

rotate3Layer0Row0Expected : Basis.GF2Row8
rotate3Layer0Row0Expected = Basis.gf2-row8 false false false false false false false false

rotate3Layer0Row0Exact :
  Decoder.expandMask8 rotate3Layer0Basis rotate3Layer0Row0Mask
  ≡ rotate3Layer0Row0Expected
rotate3Layer0Row0Exact = refl

rotate3Layer0Row1Mask : Decoder.FactorMask8
rotate3Layer0Row1Mask = Decoder.factor-mask8 false false false false false false false false

rotate3Layer0Row1Expected : Basis.GF2Row8
rotate3Layer0Row1Expected = Basis.gf2-row8 false false false false false false false false

rotate3Layer0Row1Exact :
  Decoder.expandMask8 rotate3Layer0Basis rotate3Layer0Row1Mask
  ≡ rotate3Layer0Row1Expected
rotate3Layer0Row1Exact = refl

rotate3Layer0Row2Mask : Decoder.FactorMask8
rotate3Layer0Row2Mask = Decoder.factor-mask8 false false false false false false false false

rotate3Layer0Row2Expected : Basis.GF2Row8
rotate3Layer0Row2Expected = Basis.gf2-row8 false false false false false false false false

rotate3Layer0Row2Exact :
  Decoder.expandMask8 rotate3Layer0Basis rotate3Layer0Row2Mask
  ≡ rotate3Layer0Row2Expected
rotate3Layer0Row2Exact = refl

rotate3Layer0Row3Mask : Decoder.FactorMask8
rotate3Layer0Row3Mask = Decoder.factor-mask8 false false false false false false false false

rotate3Layer0Row3Expected : Basis.GF2Row8
rotate3Layer0Row3Expected = Basis.gf2-row8 false false false false false false false false

rotate3Layer0Row3Exact :
  Decoder.expandMask8 rotate3Layer0Basis rotate3Layer0Row3Mask
  ≡ rotate3Layer0Row3Expected
rotate3Layer0Row3Exact = refl

rotate3Layer0Row4Mask : Decoder.FactorMask8
rotate3Layer0Row4Mask = Decoder.factor-mask8 false false false false false false false false

rotate3Layer0Row4Expected : Basis.GF2Row8
rotate3Layer0Row4Expected = Basis.gf2-row8 false false false false false false false false

rotate3Layer0Row4Exact :
  Decoder.expandMask8 rotate3Layer0Basis rotate3Layer0Row4Mask
  ≡ rotate3Layer0Row4Expected
rotate3Layer0Row4Exact = refl

rotate3Layer0Row5Mask : Decoder.FactorMask8
rotate3Layer0Row5Mask = Decoder.factor-mask8 false false false false false false false false

rotate3Layer0Row5Expected : Basis.GF2Row8
rotate3Layer0Row5Expected = Basis.gf2-row8 false false false false false false false false

rotate3Layer0Row5Exact :
  Decoder.expandMask8 rotate3Layer0Basis rotate3Layer0Row5Mask
  ≡ rotate3Layer0Row5Expected
rotate3Layer0Row5Exact = refl

rotate3Layer0Row6Mask : Decoder.FactorMask8
rotate3Layer0Row6Mask = Decoder.factor-mask8 false false false false false false false false

rotate3Layer0Row6Expected : Basis.GF2Row8
rotate3Layer0Row6Expected = Basis.gf2-row8 false false false false false false false false

rotate3Layer0Row6Exact :
  Decoder.expandMask8 rotate3Layer0Basis rotate3Layer0Row6Mask
  ≡ rotate3Layer0Row6Expected
rotate3Layer0Row6Exact = refl

rotate3Layer0Row7Mask : Decoder.FactorMask8
rotate3Layer0Row7Mask = Decoder.factor-mask8 false false false false false false false false

rotate3Layer0Row7Expected : Basis.GF2Row8
rotate3Layer0Row7Expected = Basis.gf2-row8 false false false false false false false false

rotate3Layer0Row7Exact :
  Decoder.expandMask8 rotate3Layer0Basis rotate3Layer0Row7Mask
  ≡ rotate3Layer0Row7Expected
rotate3Layer0Row7Exact = refl

rotate3Layer1Basis : Decoder.FactorBasis8
rotate3Layer1Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false false false true true false true true)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

rotate3Layer1Row0Mask : Decoder.FactorMask8
rotate3Layer1Row0Mask = Decoder.factor-mask8 false false false false false false false false

rotate3Layer1Row0Expected : Basis.GF2Row8
rotate3Layer1Row0Expected = Basis.gf2-row8 false false false false false false false false

rotate3Layer1Row0Exact :
  Decoder.expandMask8 rotate3Layer1Basis rotate3Layer1Row0Mask
  ≡ rotate3Layer1Row0Expected
rotate3Layer1Row0Exact = refl

rotate3Layer1Row1Mask : Decoder.FactorMask8
rotate3Layer1Row1Mask = Decoder.factor-mask8 true false false false false false false false

rotate3Layer1Row1Expected : Basis.GF2Row8
rotate3Layer1Row1Expected = Basis.gf2-row8 false false false true true false true true

rotate3Layer1Row1Exact :
  Decoder.expandMask8 rotate3Layer1Basis rotate3Layer1Row1Mask
  ≡ rotate3Layer1Row1Expected
rotate3Layer1Row1Exact = refl

rotate3Layer1Row2Mask : Decoder.FactorMask8
rotate3Layer1Row2Mask = Decoder.factor-mask8 false false false false false false false false

rotate3Layer1Row2Expected : Basis.GF2Row8
rotate3Layer1Row2Expected = Basis.gf2-row8 false false false false false false false false

rotate3Layer1Row2Exact :
  Decoder.expandMask8 rotate3Layer1Basis rotate3Layer1Row2Mask
  ≡ rotate3Layer1Row2Expected
rotate3Layer1Row2Exact = refl

rotate3Layer1Row3Mask : Decoder.FactorMask8
rotate3Layer1Row3Mask = Decoder.factor-mask8 false false false false false false false false

rotate3Layer1Row3Expected : Basis.GF2Row8
rotate3Layer1Row3Expected = Basis.gf2-row8 false false false false false false false false

rotate3Layer1Row3Exact :
  Decoder.expandMask8 rotate3Layer1Basis rotate3Layer1Row3Mask
  ≡ rotate3Layer1Row3Expected
rotate3Layer1Row3Exact = refl

rotate3Layer1Row4Mask : Decoder.FactorMask8
rotate3Layer1Row4Mask = Decoder.factor-mask8 false false false false false false false false

rotate3Layer1Row4Expected : Basis.GF2Row8
rotate3Layer1Row4Expected = Basis.gf2-row8 false false false false false false false false

rotate3Layer1Row4Exact :
  Decoder.expandMask8 rotate3Layer1Basis rotate3Layer1Row4Mask
  ≡ rotate3Layer1Row4Expected
rotate3Layer1Row4Exact = refl

rotate3Layer1Row5Mask : Decoder.FactorMask8
rotate3Layer1Row5Mask = Decoder.factor-mask8 false false false false false false false false

rotate3Layer1Row5Expected : Basis.GF2Row8
rotate3Layer1Row5Expected = Basis.gf2-row8 false false false false false false false false

rotate3Layer1Row5Exact :
  Decoder.expandMask8 rotate3Layer1Basis rotate3Layer1Row5Mask
  ≡ rotate3Layer1Row5Expected
rotate3Layer1Row5Exact = refl

rotate3Layer1Row6Mask : Decoder.FactorMask8
rotate3Layer1Row6Mask = Decoder.factor-mask8 false false false false false false false false

rotate3Layer1Row6Expected : Basis.GF2Row8
rotate3Layer1Row6Expected = Basis.gf2-row8 false false false false false false false false

rotate3Layer1Row6Exact :
  Decoder.expandMask8 rotate3Layer1Basis rotate3Layer1Row6Mask
  ≡ rotate3Layer1Row6Expected
rotate3Layer1Row6Exact = refl

rotate3Layer1Row7Mask : Decoder.FactorMask8
rotate3Layer1Row7Mask = Decoder.factor-mask8 false false false false false false false false

rotate3Layer1Row7Expected : Basis.GF2Row8
rotate3Layer1Row7Expected = Basis.gf2-row8 false false false false false false false false

rotate3Layer1Row7Exact :
  Decoder.expandMask8 rotate3Layer1Basis rotate3Layer1Row7Mask
  ≡ rotate3Layer1Row7Expected
rotate3Layer1Row7Exact = refl

rotate3Layer16Basis : Decoder.FactorBasis8
rotate3Layer16Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 true false false true false true false true)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

rotate3Layer16Row0Mask : Decoder.FactorMask8
rotate3Layer16Row0Mask = Decoder.factor-mask8 true false false false false false false false

rotate3Layer16Row0Expected : Basis.GF2Row8
rotate3Layer16Row0Expected = Basis.gf2-row8 true false false true false true false true

rotate3Layer16Row0Exact :
  Decoder.expandMask8 rotate3Layer16Basis rotate3Layer16Row0Mask
  ≡ rotate3Layer16Row0Expected
rotate3Layer16Row0Exact = refl

rotate3Layer16Row1Mask : Decoder.FactorMask8
rotate3Layer16Row1Mask = Decoder.factor-mask8 false false false false false false false false

rotate3Layer16Row1Expected : Basis.GF2Row8
rotate3Layer16Row1Expected = Basis.gf2-row8 false false false false false false false false

rotate3Layer16Row1Exact :
  Decoder.expandMask8 rotate3Layer16Basis rotate3Layer16Row1Mask
  ≡ rotate3Layer16Row1Expected
rotate3Layer16Row1Exact = refl

rotate3Layer16Row2Mask : Decoder.FactorMask8
rotate3Layer16Row2Mask = Decoder.factor-mask8 false false false false false false false false

rotate3Layer16Row2Expected : Basis.GF2Row8
rotate3Layer16Row2Expected = Basis.gf2-row8 false false false false false false false false

rotate3Layer16Row2Exact :
  Decoder.expandMask8 rotate3Layer16Basis rotate3Layer16Row2Mask
  ≡ rotate3Layer16Row2Expected
rotate3Layer16Row2Exact = refl

rotate3Layer16Row3Mask : Decoder.FactorMask8
rotate3Layer16Row3Mask = Decoder.factor-mask8 false false false false false false false false

rotate3Layer16Row3Expected : Basis.GF2Row8
rotate3Layer16Row3Expected = Basis.gf2-row8 false false false false false false false false

rotate3Layer16Row3Exact :
  Decoder.expandMask8 rotate3Layer16Basis rotate3Layer16Row3Mask
  ≡ rotate3Layer16Row3Expected
rotate3Layer16Row3Exact = refl

rotate3Layer16Row4Mask : Decoder.FactorMask8
rotate3Layer16Row4Mask = Decoder.factor-mask8 false false false false false false false false

rotate3Layer16Row4Expected : Basis.GF2Row8
rotate3Layer16Row4Expected = Basis.gf2-row8 false false false false false false false false

rotate3Layer16Row4Exact :
  Decoder.expandMask8 rotate3Layer16Basis rotate3Layer16Row4Mask
  ≡ rotate3Layer16Row4Expected
rotate3Layer16Row4Exact = refl

rotate3Layer16Row5Mask : Decoder.FactorMask8
rotate3Layer16Row5Mask = Decoder.factor-mask8 false false false false false false false false

rotate3Layer16Row5Expected : Basis.GF2Row8
rotate3Layer16Row5Expected = Basis.gf2-row8 false false false false false false false false

rotate3Layer16Row5Exact :
  Decoder.expandMask8 rotate3Layer16Basis rotate3Layer16Row5Mask
  ≡ rotate3Layer16Row5Expected
rotate3Layer16Row5Exact = refl

rotate3Layer16Row6Mask : Decoder.FactorMask8
rotate3Layer16Row6Mask = Decoder.factor-mask8 false false false false false false false false

rotate3Layer16Row6Expected : Basis.GF2Row8
rotate3Layer16Row6Expected = Basis.gf2-row8 false false false false false false false false

rotate3Layer16Row6Exact :
  Decoder.expandMask8 rotate3Layer16Basis rotate3Layer16Row6Mask
  ≡ rotate3Layer16Row6Expected
rotate3Layer16Row6Exact = refl

rotate3Layer16Row7Mask : Decoder.FactorMask8
rotate3Layer16Row7Mask = Decoder.factor-mask8 false false false false false false false false

rotate3Layer16Row7Expected : Basis.GF2Row8
rotate3Layer16Row7Expected = Basis.gf2-row8 false false false false false false false false

rotate3Layer16Row7Exact :
  Decoder.expandMask8 rotate3Layer16Basis rotate3Layer16Row7Mask
  ≡ rotate3Layer16Row7Expected
rotate3Layer16Row7Exact = refl

affine3Layer0Basis : Decoder.FactorBasis8
affine3Layer0Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false false true false false false true false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

affine3Layer0Row0Mask : Decoder.FactorMask8
affine3Layer0Row0Mask = Decoder.factor-mask8 false false false false false false false false

affine3Layer0Row0Expected : Basis.GF2Row8
affine3Layer0Row0Expected = Basis.gf2-row8 false false false false false false false false

affine3Layer0Row0Exact :
  Decoder.expandMask8 affine3Layer0Basis affine3Layer0Row0Mask
  ≡ affine3Layer0Row0Expected
affine3Layer0Row0Exact = refl

affine3Layer0Row1Mask : Decoder.FactorMask8
affine3Layer0Row1Mask = Decoder.factor-mask8 true false false false false false false false

affine3Layer0Row1Expected : Basis.GF2Row8
affine3Layer0Row1Expected = Basis.gf2-row8 false false true false false false true false

affine3Layer0Row1Exact :
  Decoder.expandMask8 affine3Layer0Basis affine3Layer0Row1Mask
  ≡ affine3Layer0Row1Expected
affine3Layer0Row1Exact = refl

affine3Layer0Row2Mask : Decoder.FactorMask8
affine3Layer0Row2Mask = Decoder.factor-mask8 false false false false false false false false

affine3Layer0Row2Expected : Basis.GF2Row8
affine3Layer0Row2Expected = Basis.gf2-row8 false false false false false false false false

affine3Layer0Row2Exact :
  Decoder.expandMask8 affine3Layer0Basis affine3Layer0Row2Mask
  ≡ affine3Layer0Row2Expected
affine3Layer0Row2Exact = refl

affine3Layer0Row3Mask : Decoder.FactorMask8
affine3Layer0Row3Mask = Decoder.factor-mask8 false false false false false false false false

affine3Layer0Row3Expected : Basis.GF2Row8
affine3Layer0Row3Expected = Basis.gf2-row8 false false false false false false false false

affine3Layer0Row3Exact :
  Decoder.expandMask8 affine3Layer0Basis affine3Layer0Row3Mask
  ≡ affine3Layer0Row3Expected
affine3Layer0Row3Exact = refl

affine3Layer0Row4Mask : Decoder.FactorMask8
affine3Layer0Row4Mask = Decoder.factor-mask8 false false false false false false false false

affine3Layer0Row4Expected : Basis.GF2Row8
affine3Layer0Row4Expected = Basis.gf2-row8 false false false false false false false false

affine3Layer0Row4Exact :
  Decoder.expandMask8 affine3Layer0Basis affine3Layer0Row4Mask
  ≡ affine3Layer0Row4Expected
affine3Layer0Row4Exact = refl

affine3Layer0Row5Mask : Decoder.FactorMask8
affine3Layer0Row5Mask = Decoder.factor-mask8 false false false false false false false false

affine3Layer0Row5Expected : Basis.GF2Row8
affine3Layer0Row5Expected = Basis.gf2-row8 false false false false false false false false

affine3Layer0Row5Exact :
  Decoder.expandMask8 affine3Layer0Basis affine3Layer0Row5Mask
  ≡ affine3Layer0Row5Expected
affine3Layer0Row5Exact = refl

affine3Layer0Row6Mask : Decoder.FactorMask8
affine3Layer0Row6Mask = Decoder.factor-mask8 false false false false false false false false

affine3Layer0Row6Expected : Basis.GF2Row8
affine3Layer0Row6Expected = Basis.gf2-row8 false false false false false false false false

affine3Layer0Row6Exact :
  Decoder.expandMask8 affine3Layer0Basis affine3Layer0Row6Mask
  ≡ affine3Layer0Row6Expected
affine3Layer0Row6Exact = refl

affine3Layer0Row7Mask : Decoder.FactorMask8
affine3Layer0Row7Mask = Decoder.factor-mask8 false false false false false false false false

affine3Layer0Row7Expected : Basis.GF2Row8
affine3Layer0Row7Expected = Basis.gf2-row8 false false false false false false false false

affine3Layer0Row7Exact :
  Decoder.expandMask8 affine3Layer0Basis affine3Layer0Row7Mask
  ≡ affine3Layer0Row7Expected
affine3Layer0Row7Exact = refl

affine3Layer15Basis : Decoder.FactorBasis8
affine3Layer15Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false false true true false false false true)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

affine3Layer15Row0Mask : Decoder.FactorMask8
affine3Layer15Row0Mask = Decoder.factor-mask8 false false false false false false false false

affine3Layer15Row0Expected : Basis.GF2Row8
affine3Layer15Row0Expected = Basis.gf2-row8 false false false false false false false false

affine3Layer15Row0Exact :
  Decoder.expandMask8 affine3Layer15Basis affine3Layer15Row0Mask
  ≡ affine3Layer15Row0Expected
affine3Layer15Row0Exact = refl

affine3Layer15Row1Mask : Decoder.FactorMask8
affine3Layer15Row1Mask = Decoder.factor-mask8 false false false false false false false false

affine3Layer15Row1Expected : Basis.GF2Row8
affine3Layer15Row1Expected = Basis.gf2-row8 false false false false false false false false

affine3Layer15Row1Exact :
  Decoder.expandMask8 affine3Layer15Basis affine3Layer15Row1Mask
  ≡ affine3Layer15Row1Expected
affine3Layer15Row1Exact = refl

affine3Layer15Row2Mask : Decoder.FactorMask8
affine3Layer15Row2Mask = Decoder.factor-mask8 false false false false false false false false

affine3Layer15Row2Expected : Basis.GF2Row8
affine3Layer15Row2Expected = Basis.gf2-row8 false false false false false false false false

affine3Layer15Row2Exact :
  Decoder.expandMask8 affine3Layer15Basis affine3Layer15Row2Mask
  ≡ affine3Layer15Row2Expected
affine3Layer15Row2Exact = refl

affine3Layer15Row3Mask : Decoder.FactorMask8
affine3Layer15Row3Mask = Decoder.factor-mask8 false false false false false false false false

affine3Layer15Row3Expected : Basis.GF2Row8
affine3Layer15Row3Expected = Basis.gf2-row8 false false false false false false false false

affine3Layer15Row3Exact :
  Decoder.expandMask8 affine3Layer15Basis affine3Layer15Row3Mask
  ≡ affine3Layer15Row3Expected
affine3Layer15Row3Exact = refl

affine3Layer15Row4Mask : Decoder.FactorMask8
affine3Layer15Row4Mask = Decoder.factor-mask8 false false false false false false false false

affine3Layer15Row4Expected : Basis.GF2Row8
affine3Layer15Row4Expected = Basis.gf2-row8 false false false false false false false false

affine3Layer15Row4Exact :
  Decoder.expandMask8 affine3Layer15Basis affine3Layer15Row4Mask
  ≡ affine3Layer15Row4Expected
affine3Layer15Row4Exact = refl

affine3Layer15Row5Mask : Decoder.FactorMask8
affine3Layer15Row5Mask = Decoder.factor-mask8 false false false false false false false false

affine3Layer15Row5Expected : Basis.GF2Row8
affine3Layer15Row5Expected = Basis.gf2-row8 false false false false false false false false

affine3Layer15Row5Exact :
  Decoder.expandMask8 affine3Layer15Basis affine3Layer15Row5Mask
  ≡ affine3Layer15Row5Expected
affine3Layer15Row5Exact = refl

affine3Layer15Row6Mask : Decoder.FactorMask8
affine3Layer15Row6Mask = Decoder.factor-mask8 false false false false false false false false

affine3Layer15Row6Expected : Basis.GF2Row8
affine3Layer15Row6Expected = Basis.gf2-row8 false false false false false false false false

affine3Layer15Row6Exact :
  Decoder.expandMask8 affine3Layer15Basis affine3Layer15Row6Mask
  ≡ affine3Layer15Row6Expected
affine3Layer15Row6Exact = refl

affine3Layer15Row7Mask : Decoder.FactorMask8
affine3Layer15Row7Mask = Decoder.factor-mask8 true false false false false false false false

affine3Layer15Row7Expected : Basis.GF2Row8
affine3Layer15Row7Expected = Basis.gf2-row8 false false true true false false false true

affine3Layer15Row7Exact :
  Decoder.expandMask8 affine3Layer15Basis affine3Layer15Row7Mask
  ≡ affine3Layer15Row7Expected
affine3Layer15Row7Exact = refl

affine5Layer0Basis : Decoder.FactorBasis8
affine5Layer0Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

affine5Layer0Row0Mask : Decoder.FactorMask8
affine5Layer0Row0Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer0Row0Expected : Basis.GF2Row8
affine5Layer0Row0Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer0Row0Exact :
  Decoder.expandMask8 affine5Layer0Basis affine5Layer0Row0Mask
  ≡ affine5Layer0Row0Expected
affine5Layer0Row0Exact = refl

affine5Layer0Row1Mask : Decoder.FactorMask8
affine5Layer0Row1Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer0Row1Expected : Basis.GF2Row8
affine5Layer0Row1Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer0Row1Exact :
  Decoder.expandMask8 affine5Layer0Basis affine5Layer0Row1Mask
  ≡ affine5Layer0Row1Expected
affine5Layer0Row1Exact = refl

affine5Layer0Row2Mask : Decoder.FactorMask8
affine5Layer0Row2Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer0Row2Expected : Basis.GF2Row8
affine5Layer0Row2Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer0Row2Exact :
  Decoder.expandMask8 affine5Layer0Basis affine5Layer0Row2Mask
  ≡ affine5Layer0Row2Expected
affine5Layer0Row2Exact = refl

affine5Layer0Row3Mask : Decoder.FactorMask8
affine5Layer0Row3Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer0Row3Expected : Basis.GF2Row8
affine5Layer0Row3Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer0Row3Exact :
  Decoder.expandMask8 affine5Layer0Basis affine5Layer0Row3Mask
  ≡ affine5Layer0Row3Expected
affine5Layer0Row3Exact = refl

affine5Layer0Row4Mask : Decoder.FactorMask8
affine5Layer0Row4Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer0Row4Expected : Basis.GF2Row8
affine5Layer0Row4Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer0Row4Exact :
  Decoder.expandMask8 affine5Layer0Basis affine5Layer0Row4Mask
  ≡ affine5Layer0Row4Expected
affine5Layer0Row4Exact = refl

affine5Layer0Row5Mask : Decoder.FactorMask8
affine5Layer0Row5Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer0Row5Expected : Basis.GF2Row8
affine5Layer0Row5Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer0Row5Exact :
  Decoder.expandMask8 affine5Layer0Basis affine5Layer0Row5Mask
  ≡ affine5Layer0Row5Expected
affine5Layer0Row5Exact = refl

affine5Layer0Row6Mask : Decoder.FactorMask8
affine5Layer0Row6Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer0Row6Expected : Basis.GF2Row8
affine5Layer0Row6Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer0Row6Exact :
  Decoder.expandMask8 affine5Layer0Basis affine5Layer0Row6Mask
  ≡ affine5Layer0Row6Expected
affine5Layer0Row6Exact = refl

affine5Layer0Row7Mask : Decoder.FactorMask8
affine5Layer0Row7Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer0Row7Expected : Basis.GF2Row8
affine5Layer0Row7Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer0Row7Exact :
  Decoder.expandMask8 affine5Layer0Basis affine5Layer0Row7Mask
  ≡ affine5Layer0Row7Expected
affine5Layer0Row7Exact = refl

affine5Layer1Basis : Decoder.FactorBasis8
affine5Layer1Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

affine5Layer1Row0Mask : Decoder.FactorMask8
affine5Layer1Row0Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer1Row0Expected : Basis.GF2Row8
affine5Layer1Row0Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer1Row0Exact :
  Decoder.expandMask8 affine5Layer1Basis affine5Layer1Row0Mask
  ≡ affine5Layer1Row0Expected
affine5Layer1Row0Exact = refl

affine5Layer1Row1Mask : Decoder.FactorMask8
affine5Layer1Row1Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer1Row1Expected : Basis.GF2Row8
affine5Layer1Row1Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer1Row1Exact :
  Decoder.expandMask8 affine5Layer1Basis affine5Layer1Row1Mask
  ≡ affine5Layer1Row1Expected
affine5Layer1Row1Exact = refl

affine5Layer1Row2Mask : Decoder.FactorMask8
affine5Layer1Row2Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer1Row2Expected : Basis.GF2Row8
affine5Layer1Row2Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer1Row2Exact :
  Decoder.expandMask8 affine5Layer1Basis affine5Layer1Row2Mask
  ≡ affine5Layer1Row2Expected
affine5Layer1Row2Exact = refl

affine5Layer1Row3Mask : Decoder.FactorMask8
affine5Layer1Row3Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer1Row3Expected : Basis.GF2Row8
affine5Layer1Row3Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer1Row3Exact :
  Decoder.expandMask8 affine5Layer1Basis affine5Layer1Row3Mask
  ≡ affine5Layer1Row3Expected
affine5Layer1Row3Exact = refl

affine5Layer1Row4Mask : Decoder.FactorMask8
affine5Layer1Row4Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer1Row4Expected : Basis.GF2Row8
affine5Layer1Row4Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer1Row4Exact :
  Decoder.expandMask8 affine5Layer1Basis affine5Layer1Row4Mask
  ≡ affine5Layer1Row4Expected
affine5Layer1Row4Exact = refl

affine5Layer1Row5Mask : Decoder.FactorMask8
affine5Layer1Row5Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer1Row5Expected : Basis.GF2Row8
affine5Layer1Row5Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer1Row5Exact :
  Decoder.expandMask8 affine5Layer1Basis affine5Layer1Row5Mask
  ≡ affine5Layer1Row5Expected
affine5Layer1Row5Exact = refl

affine5Layer1Row6Mask : Decoder.FactorMask8
affine5Layer1Row6Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer1Row6Expected : Basis.GF2Row8
affine5Layer1Row6Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer1Row6Exact :
  Decoder.expandMask8 affine5Layer1Basis affine5Layer1Row6Mask
  ≡ affine5Layer1Row6Expected
affine5Layer1Row6Exact = refl

affine5Layer1Row7Mask : Decoder.FactorMask8
affine5Layer1Row7Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer1Row7Expected : Basis.GF2Row8
affine5Layer1Row7Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer1Row7Exact :
  Decoder.expandMask8 affine5Layer1Basis affine5Layer1Row7Mask
  ≡ affine5Layer1Row7Expected
affine5Layer1Row7Exact = refl

affine5Layer2Basis : Decoder.FactorBasis8
affine5Layer2Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

affine5Layer2Row0Mask : Decoder.FactorMask8
affine5Layer2Row0Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer2Row0Expected : Basis.GF2Row8
affine5Layer2Row0Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer2Row0Exact :
  Decoder.expandMask8 affine5Layer2Basis affine5Layer2Row0Mask
  ≡ affine5Layer2Row0Expected
affine5Layer2Row0Exact = refl

affine5Layer2Row1Mask : Decoder.FactorMask8
affine5Layer2Row1Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer2Row1Expected : Basis.GF2Row8
affine5Layer2Row1Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer2Row1Exact :
  Decoder.expandMask8 affine5Layer2Basis affine5Layer2Row1Mask
  ≡ affine5Layer2Row1Expected
affine5Layer2Row1Exact = refl

affine5Layer2Row2Mask : Decoder.FactorMask8
affine5Layer2Row2Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer2Row2Expected : Basis.GF2Row8
affine5Layer2Row2Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer2Row2Exact :
  Decoder.expandMask8 affine5Layer2Basis affine5Layer2Row2Mask
  ≡ affine5Layer2Row2Expected
affine5Layer2Row2Exact = refl

affine5Layer2Row3Mask : Decoder.FactorMask8
affine5Layer2Row3Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer2Row3Expected : Basis.GF2Row8
affine5Layer2Row3Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer2Row3Exact :
  Decoder.expandMask8 affine5Layer2Basis affine5Layer2Row3Mask
  ≡ affine5Layer2Row3Expected
affine5Layer2Row3Exact = refl

affine5Layer2Row4Mask : Decoder.FactorMask8
affine5Layer2Row4Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer2Row4Expected : Basis.GF2Row8
affine5Layer2Row4Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer2Row4Exact :
  Decoder.expandMask8 affine5Layer2Basis affine5Layer2Row4Mask
  ≡ affine5Layer2Row4Expected
affine5Layer2Row4Exact = refl

affine5Layer2Row5Mask : Decoder.FactorMask8
affine5Layer2Row5Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer2Row5Expected : Basis.GF2Row8
affine5Layer2Row5Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer2Row5Exact :
  Decoder.expandMask8 affine5Layer2Basis affine5Layer2Row5Mask
  ≡ affine5Layer2Row5Expected
affine5Layer2Row5Exact = refl

affine5Layer2Row6Mask : Decoder.FactorMask8
affine5Layer2Row6Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer2Row6Expected : Basis.GF2Row8
affine5Layer2Row6Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer2Row6Exact :
  Decoder.expandMask8 affine5Layer2Basis affine5Layer2Row6Mask
  ≡ affine5Layer2Row6Expected
affine5Layer2Row6Exact = refl

affine5Layer2Row7Mask : Decoder.FactorMask8
affine5Layer2Row7Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer2Row7Expected : Basis.GF2Row8
affine5Layer2Row7Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer2Row7Exact :
  Decoder.expandMask8 affine5Layer2Basis affine5Layer2Row7Mask
  ≡ affine5Layer2Row7Expected
affine5Layer2Row7Exact = refl

affine5Layer16Basis : Decoder.FactorBasis8
affine5Layer16Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false false false false false false true false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

affine5Layer16Row0Mask : Decoder.FactorMask8
affine5Layer16Row0Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer16Row0Expected : Basis.GF2Row8
affine5Layer16Row0Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer16Row0Exact :
  Decoder.expandMask8 affine5Layer16Basis affine5Layer16Row0Mask
  ≡ affine5Layer16Row0Expected
affine5Layer16Row0Exact = refl

affine5Layer16Row1Mask : Decoder.FactorMask8
affine5Layer16Row1Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer16Row1Expected : Basis.GF2Row8
affine5Layer16Row1Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer16Row1Exact :
  Decoder.expandMask8 affine5Layer16Basis affine5Layer16Row1Mask
  ≡ affine5Layer16Row1Expected
affine5Layer16Row1Exact = refl

affine5Layer16Row2Mask : Decoder.FactorMask8
affine5Layer16Row2Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer16Row2Expected : Basis.GF2Row8
affine5Layer16Row2Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer16Row2Exact :
  Decoder.expandMask8 affine5Layer16Basis affine5Layer16Row2Mask
  ≡ affine5Layer16Row2Expected
affine5Layer16Row2Exact = refl

affine5Layer16Row3Mask : Decoder.FactorMask8
affine5Layer16Row3Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer16Row3Expected : Basis.GF2Row8
affine5Layer16Row3Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer16Row3Exact :
  Decoder.expandMask8 affine5Layer16Basis affine5Layer16Row3Mask
  ≡ affine5Layer16Row3Expected
affine5Layer16Row3Exact = refl

affine5Layer16Row4Mask : Decoder.FactorMask8
affine5Layer16Row4Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer16Row4Expected : Basis.GF2Row8
affine5Layer16Row4Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer16Row4Exact :
  Decoder.expandMask8 affine5Layer16Basis affine5Layer16Row4Mask
  ≡ affine5Layer16Row4Expected
affine5Layer16Row4Exact = refl

affine5Layer16Row5Mask : Decoder.FactorMask8
affine5Layer16Row5Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer16Row5Expected : Basis.GF2Row8
affine5Layer16Row5Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer16Row5Exact :
  Decoder.expandMask8 affine5Layer16Basis affine5Layer16Row5Mask
  ≡ affine5Layer16Row5Expected
affine5Layer16Row5Exact = refl

affine5Layer16Row6Mask : Decoder.FactorMask8
affine5Layer16Row6Mask = Decoder.factor-mask8 false false false false false false false false

affine5Layer16Row6Expected : Basis.GF2Row8
affine5Layer16Row6Expected = Basis.gf2-row8 false false false false false false false false

affine5Layer16Row6Exact :
  Decoder.expandMask8 affine5Layer16Basis affine5Layer16Row6Mask
  ≡ affine5Layer16Row6Expected
affine5Layer16Row6Exact = refl

affine5Layer16Row7Mask : Decoder.FactorMask8
affine5Layer16Row7Mask = Decoder.factor-mask8 true false false false false false false false

affine5Layer16Row7Expected : Basis.GF2Row8
affine5Layer16Row7Expected = Basis.gf2-row8 false false false false false false true false

affine5Layer16Row7Exact :
  Decoder.expandMask8 affine5Layer16Basis affine5Layer16Row7Mask
  ≡ affine5Layer16Row7Expected
affine5Layer16Row7Exact = refl

affine7Layer0Basis : Decoder.FactorBasis8
affine7Layer0Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

affine7Layer0Row0Mask : Decoder.FactorMask8
affine7Layer0Row0Mask = Decoder.factor-mask8 false false false false false false false false

affine7Layer0Row0Expected : Basis.GF2Row8
affine7Layer0Row0Expected = Basis.gf2-row8 false false false false false false false false

affine7Layer0Row0Exact :
  Decoder.expandMask8 affine7Layer0Basis affine7Layer0Row0Mask
  ≡ affine7Layer0Row0Expected
affine7Layer0Row0Exact = refl

affine7Layer0Row1Mask : Decoder.FactorMask8
affine7Layer0Row1Mask = Decoder.factor-mask8 false false false false false false false false

affine7Layer0Row1Expected : Basis.GF2Row8
affine7Layer0Row1Expected = Basis.gf2-row8 false false false false false false false false

affine7Layer0Row1Exact :
  Decoder.expandMask8 affine7Layer0Basis affine7Layer0Row1Mask
  ≡ affine7Layer0Row1Expected
affine7Layer0Row1Exact = refl

affine7Layer0Row2Mask : Decoder.FactorMask8
affine7Layer0Row2Mask = Decoder.factor-mask8 false false false false false false false false

affine7Layer0Row2Expected : Basis.GF2Row8
affine7Layer0Row2Expected = Basis.gf2-row8 false false false false false false false false

affine7Layer0Row2Exact :
  Decoder.expandMask8 affine7Layer0Basis affine7Layer0Row2Mask
  ≡ affine7Layer0Row2Expected
affine7Layer0Row2Exact = refl

affine7Layer0Row3Mask : Decoder.FactorMask8
affine7Layer0Row3Mask = Decoder.factor-mask8 false false false false false false false false

affine7Layer0Row3Expected : Basis.GF2Row8
affine7Layer0Row3Expected = Basis.gf2-row8 false false false false false false false false

affine7Layer0Row3Exact :
  Decoder.expandMask8 affine7Layer0Basis affine7Layer0Row3Mask
  ≡ affine7Layer0Row3Expected
affine7Layer0Row3Exact = refl

affine7Layer0Row4Mask : Decoder.FactorMask8
affine7Layer0Row4Mask = Decoder.factor-mask8 false false false false false false false false

affine7Layer0Row4Expected : Basis.GF2Row8
affine7Layer0Row4Expected = Basis.gf2-row8 false false false false false false false false

affine7Layer0Row4Exact :
  Decoder.expandMask8 affine7Layer0Basis affine7Layer0Row4Mask
  ≡ affine7Layer0Row4Expected
affine7Layer0Row4Exact = refl

affine7Layer0Row5Mask : Decoder.FactorMask8
affine7Layer0Row5Mask = Decoder.factor-mask8 false false false false false false false false

affine7Layer0Row5Expected : Basis.GF2Row8
affine7Layer0Row5Expected = Basis.gf2-row8 false false false false false false false false

affine7Layer0Row5Exact :
  Decoder.expandMask8 affine7Layer0Basis affine7Layer0Row5Mask
  ≡ affine7Layer0Row5Expected
affine7Layer0Row5Exact = refl

affine7Layer0Row6Mask : Decoder.FactorMask8
affine7Layer0Row6Mask = Decoder.factor-mask8 false false false false false false false false

affine7Layer0Row6Expected : Basis.GF2Row8
affine7Layer0Row6Expected = Basis.gf2-row8 false false false false false false false false

affine7Layer0Row6Exact :
  Decoder.expandMask8 affine7Layer0Basis affine7Layer0Row6Mask
  ≡ affine7Layer0Row6Expected
affine7Layer0Row6Exact = refl

affine7Layer0Row7Mask : Decoder.FactorMask8
affine7Layer0Row7Mask = Decoder.factor-mask8 false false false false false false false false

affine7Layer0Row7Expected : Basis.GF2Row8
affine7Layer0Row7Expected = Basis.gf2-row8 false false false false false false false false

affine7Layer0Row7Exact :
  Decoder.expandMask8 affine7Layer0Basis affine7Layer0Row7Mask
  ≡ affine7Layer0Row7Expected
affine7Layer0Row7Exact = refl

affine7Layer1Basis : Decoder.FactorBasis8
affine7Layer1Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false false false true true false true true)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

affine7Layer1Row0Mask : Decoder.FactorMask8
affine7Layer1Row0Mask = Decoder.factor-mask8 false false false false false false false false

affine7Layer1Row0Expected : Basis.GF2Row8
affine7Layer1Row0Expected = Basis.gf2-row8 false false false false false false false false

affine7Layer1Row0Exact :
  Decoder.expandMask8 affine7Layer1Basis affine7Layer1Row0Mask
  ≡ affine7Layer1Row0Expected
affine7Layer1Row0Exact = refl

affine7Layer1Row1Mask : Decoder.FactorMask8
affine7Layer1Row1Mask = Decoder.factor-mask8 true false false false false false false false

affine7Layer1Row1Expected : Basis.GF2Row8
affine7Layer1Row1Expected = Basis.gf2-row8 false false false true true false true true

affine7Layer1Row1Exact :
  Decoder.expandMask8 affine7Layer1Basis affine7Layer1Row1Mask
  ≡ affine7Layer1Row1Expected
affine7Layer1Row1Exact = refl

affine7Layer1Row2Mask : Decoder.FactorMask8
affine7Layer1Row2Mask = Decoder.factor-mask8 false false false false false false false false

affine7Layer1Row2Expected : Basis.GF2Row8
affine7Layer1Row2Expected = Basis.gf2-row8 false false false false false false false false

affine7Layer1Row2Exact :
  Decoder.expandMask8 affine7Layer1Basis affine7Layer1Row2Mask
  ≡ affine7Layer1Row2Expected
affine7Layer1Row2Exact = refl

affine7Layer1Row3Mask : Decoder.FactorMask8
affine7Layer1Row3Mask = Decoder.factor-mask8 false false false false false false false false

affine7Layer1Row3Expected : Basis.GF2Row8
affine7Layer1Row3Expected = Basis.gf2-row8 false false false false false false false false

affine7Layer1Row3Exact :
  Decoder.expandMask8 affine7Layer1Basis affine7Layer1Row3Mask
  ≡ affine7Layer1Row3Expected
affine7Layer1Row3Exact = refl

affine7Layer1Row4Mask : Decoder.FactorMask8
affine7Layer1Row4Mask = Decoder.factor-mask8 false false false false false false false false

affine7Layer1Row4Expected : Basis.GF2Row8
affine7Layer1Row4Expected = Basis.gf2-row8 false false false false false false false false

affine7Layer1Row4Exact :
  Decoder.expandMask8 affine7Layer1Basis affine7Layer1Row4Mask
  ≡ affine7Layer1Row4Expected
affine7Layer1Row4Exact = refl

affine7Layer1Row5Mask : Decoder.FactorMask8
affine7Layer1Row5Mask = Decoder.factor-mask8 false false false false false false false false

affine7Layer1Row5Expected : Basis.GF2Row8
affine7Layer1Row5Expected = Basis.gf2-row8 false false false false false false false false

affine7Layer1Row5Exact :
  Decoder.expandMask8 affine7Layer1Basis affine7Layer1Row5Mask
  ≡ affine7Layer1Row5Expected
affine7Layer1Row5Exact = refl

affine7Layer1Row6Mask : Decoder.FactorMask8
affine7Layer1Row6Mask = Decoder.factor-mask8 false false false false false false false false

affine7Layer1Row6Expected : Basis.GF2Row8
affine7Layer1Row6Expected = Basis.gf2-row8 false false false false false false false false

affine7Layer1Row6Exact :
  Decoder.expandMask8 affine7Layer1Basis affine7Layer1Row6Mask
  ≡ affine7Layer1Row6Expected
affine7Layer1Row6Exact = refl

affine7Layer1Row7Mask : Decoder.FactorMask8
affine7Layer1Row7Mask = Decoder.factor-mask8 false false false false false false false false

affine7Layer1Row7Expected : Basis.GF2Row8
affine7Layer1Row7Expected = Basis.gf2-row8 false false false false false false false false

affine7Layer1Row7Exact :
  Decoder.expandMask8 affine7Layer1Basis affine7Layer1Row7Mask
  ≡ affine7Layer1Row7Expected
affine7Layer1Row7Exact = refl

affine7Layer16Basis : Decoder.FactorBasis8
affine7Layer16Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 true false false true false true false true)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

affine7Layer16Row0Mask : Decoder.FactorMask8
affine7Layer16Row0Mask = Decoder.factor-mask8 true false false false false false false false

affine7Layer16Row0Expected : Basis.GF2Row8
affine7Layer16Row0Expected = Basis.gf2-row8 true false false true false true false true

affine7Layer16Row0Exact :
  Decoder.expandMask8 affine7Layer16Basis affine7Layer16Row0Mask
  ≡ affine7Layer16Row0Expected
affine7Layer16Row0Exact = refl

affine7Layer16Row1Mask : Decoder.FactorMask8
affine7Layer16Row1Mask = Decoder.factor-mask8 false false false false false false false false

affine7Layer16Row1Expected : Basis.GF2Row8
affine7Layer16Row1Expected = Basis.gf2-row8 false false false false false false false false

affine7Layer16Row1Exact :
  Decoder.expandMask8 affine7Layer16Basis affine7Layer16Row1Mask
  ≡ affine7Layer16Row1Expected
affine7Layer16Row1Exact = refl

affine7Layer16Row2Mask : Decoder.FactorMask8
affine7Layer16Row2Mask = Decoder.factor-mask8 false false false false false false false false

affine7Layer16Row2Expected : Basis.GF2Row8
affine7Layer16Row2Expected = Basis.gf2-row8 false false false false false false false false

affine7Layer16Row2Exact :
  Decoder.expandMask8 affine7Layer16Basis affine7Layer16Row2Mask
  ≡ affine7Layer16Row2Expected
affine7Layer16Row2Exact = refl

affine7Layer16Row3Mask : Decoder.FactorMask8
affine7Layer16Row3Mask = Decoder.factor-mask8 false false false false false false false false

affine7Layer16Row3Expected : Basis.GF2Row8
affine7Layer16Row3Expected = Basis.gf2-row8 false false false false false false false false

affine7Layer16Row3Exact :
  Decoder.expandMask8 affine7Layer16Basis affine7Layer16Row3Mask
  ≡ affine7Layer16Row3Expected
affine7Layer16Row3Exact = refl

affine7Layer16Row4Mask : Decoder.FactorMask8
affine7Layer16Row4Mask = Decoder.factor-mask8 false false false false false false false false

affine7Layer16Row4Expected : Basis.GF2Row8
affine7Layer16Row4Expected = Basis.gf2-row8 false false false false false false false false

affine7Layer16Row4Exact :
  Decoder.expandMask8 affine7Layer16Basis affine7Layer16Row4Mask
  ≡ affine7Layer16Row4Expected
affine7Layer16Row4Exact = refl

affine7Layer16Row5Mask : Decoder.FactorMask8
affine7Layer16Row5Mask = Decoder.factor-mask8 false false false false false false false false

affine7Layer16Row5Expected : Basis.GF2Row8
affine7Layer16Row5Expected = Basis.gf2-row8 false false false false false false false false

affine7Layer16Row5Exact :
  Decoder.expandMask8 affine7Layer16Basis affine7Layer16Row5Mask
  ≡ affine7Layer16Row5Expected
affine7Layer16Row5Exact = refl

affine7Layer16Row6Mask : Decoder.FactorMask8
affine7Layer16Row6Mask = Decoder.factor-mask8 false false false false false false false false

affine7Layer16Row6Expected : Basis.GF2Row8
affine7Layer16Row6Expected = Basis.gf2-row8 false false false false false false false false

affine7Layer16Row6Exact :
  Decoder.expandMask8 affine7Layer16Basis affine7Layer16Row6Mask
  ≡ affine7Layer16Row6Expected
affine7Layer16Row6Exact = refl

affine7Layer16Row7Mask : Decoder.FactorMask8
affine7Layer16Row7Mask = Decoder.factor-mask8 false false false false false false false false

affine7Layer16Row7Expected : Basis.GF2Row8
affine7Layer16Row7Expected = Basis.gf2-row8 false false false false false false false false

affine7Layer16Row7Exact :
  Decoder.expandMask8 affine7Layer16Basis affine7Layer16Row7Mask
  ≡ affine7Layer16Row7Expected
affine7Layer16Row7Exact = refl

affine9Layer0Basis : Decoder.FactorBasis8
affine9Layer0Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false false true false true false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

affine9Layer0Row0Mask : Decoder.FactorMask8
affine9Layer0Row0Mask = Decoder.factor-mask8 false false false false false false false false

affine9Layer0Row0Expected : Basis.GF2Row8
affine9Layer0Row0Expected = Basis.gf2-row8 false false false false false false false false

affine9Layer0Row0Exact :
  Decoder.expandMask8 affine9Layer0Basis affine9Layer0Row0Mask
  ≡ affine9Layer0Row0Expected
affine9Layer0Row0Exact = refl

affine9Layer0Row1Mask : Decoder.FactorMask8
affine9Layer0Row1Mask = Decoder.factor-mask8 true false false false false false false false

affine9Layer0Row1Expected : Basis.GF2Row8
affine9Layer0Row1Expected = Basis.gf2-row8 false false true false true false false false

affine9Layer0Row1Exact :
  Decoder.expandMask8 affine9Layer0Basis affine9Layer0Row1Mask
  ≡ affine9Layer0Row1Expected
affine9Layer0Row1Exact = refl

affine9Layer0Row2Mask : Decoder.FactorMask8
affine9Layer0Row2Mask = Decoder.factor-mask8 false false false false false false false false

affine9Layer0Row2Expected : Basis.GF2Row8
affine9Layer0Row2Expected = Basis.gf2-row8 false false false false false false false false

affine9Layer0Row2Exact :
  Decoder.expandMask8 affine9Layer0Basis affine9Layer0Row2Mask
  ≡ affine9Layer0Row2Expected
affine9Layer0Row2Exact = refl

affine9Layer0Row3Mask : Decoder.FactorMask8
affine9Layer0Row3Mask = Decoder.factor-mask8 false false false false false false false false

affine9Layer0Row3Expected : Basis.GF2Row8
affine9Layer0Row3Expected = Basis.gf2-row8 false false false false false false false false

affine9Layer0Row3Exact :
  Decoder.expandMask8 affine9Layer0Basis affine9Layer0Row3Mask
  ≡ affine9Layer0Row3Expected
affine9Layer0Row3Exact = refl

affine9Layer0Row4Mask : Decoder.FactorMask8
affine9Layer0Row4Mask = Decoder.factor-mask8 false false false false false false false false

affine9Layer0Row4Expected : Basis.GF2Row8
affine9Layer0Row4Expected = Basis.gf2-row8 false false false false false false false false

affine9Layer0Row4Exact :
  Decoder.expandMask8 affine9Layer0Basis affine9Layer0Row4Mask
  ≡ affine9Layer0Row4Expected
affine9Layer0Row4Exact = refl

affine9Layer0Row5Mask : Decoder.FactorMask8
affine9Layer0Row5Mask = Decoder.factor-mask8 false false false false false false false false

affine9Layer0Row5Expected : Basis.GF2Row8
affine9Layer0Row5Expected = Basis.gf2-row8 false false false false false false false false

affine9Layer0Row5Exact :
  Decoder.expandMask8 affine9Layer0Basis affine9Layer0Row5Mask
  ≡ affine9Layer0Row5Expected
affine9Layer0Row5Exact = refl

affine9Layer0Row6Mask : Decoder.FactorMask8
affine9Layer0Row6Mask = Decoder.factor-mask8 false false false false false false false false

affine9Layer0Row6Expected : Basis.GF2Row8
affine9Layer0Row6Expected = Basis.gf2-row8 false false false false false false false false

affine9Layer0Row6Exact :
  Decoder.expandMask8 affine9Layer0Basis affine9Layer0Row6Mask
  ≡ affine9Layer0Row6Expected
affine9Layer0Row6Exact = refl

affine9Layer0Row7Mask : Decoder.FactorMask8
affine9Layer0Row7Mask = Decoder.factor-mask8 false false false false false false false false

affine9Layer0Row7Expected : Basis.GF2Row8
affine9Layer0Row7Expected = Basis.gf2-row8 false false false false false false false false

affine9Layer0Row7Exact :
  Decoder.expandMask8 affine9Layer0Basis affine9Layer0Row7Mask
  ≡ affine9Layer0Row7Expected
affine9Layer0Row7Exact = refl

affine9Layer15Basis : Decoder.FactorBasis8
affine9Layer15Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false false true false true true false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

affine9Layer15Row0Mask : Decoder.FactorMask8
affine9Layer15Row0Mask = Decoder.factor-mask8 false false false false false false false false

affine9Layer15Row0Expected : Basis.GF2Row8
affine9Layer15Row0Expected = Basis.gf2-row8 false false false false false false false false

affine9Layer15Row0Exact :
  Decoder.expandMask8 affine9Layer15Basis affine9Layer15Row0Mask
  ≡ affine9Layer15Row0Expected
affine9Layer15Row0Exact = refl

affine9Layer15Row1Mask : Decoder.FactorMask8
affine9Layer15Row1Mask = Decoder.factor-mask8 false false false false false false false false

affine9Layer15Row1Expected : Basis.GF2Row8
affine9Layer15Row1Expected = Basis.gf2-row8 false false false false false false false false

affine9Layer15Row1Exact :
  Decoder.expandMask8 affine9Layer15Basis affine9Layer15Row1Mask
  ≡ affine9Layer15Row1Expected
affine9Layer15Row1Exact = refl

affine9Layer15Row2Mask : Decoder.FactorMask8
affine9Layer15Row2Mask = Decoder.factor-mask8 false false false false false false false false

affine9Layer15Row2Expected : Basis.GF2Row8
affine9Layer15Row2Expected = Basis.gf2-row8 false false false false false false false false

affine9Layer15Row2Exact :
  Decoder.expandMask8 affine9Layer15Basis affine9Layer15Row2Mask
  ≡ affine9Layer15Row2Expected
affine9Layer15Row2Exact = refl

affine9Layer15Row3Mask : Decoder.FactorMask8
affine9Layer15Row3Mask = Decoder.factor-mask8 false false false false false false false false

affine9Layer15Row3Expected : Basis.GF2Row8
affine9Layer15Row3Expected = Basis.gf2-row8 false false false false false false false false

affine9Layer15Row3Exact :
  Decoder.expandMask8 affine9Layer15Basis affine9Layer15Row3Mask
  ≡ affine9Layer15Row3Expected
affine9Layer15Row3Exact = refl

affine9Layer15Row4Mask : Decoder.FactorMask8
affine9Layer15Row4Mask = Decoder.factor-mask8 false false false false false false false false

affine9Layer15Row4Expected : Basis.GF2Row8
affine9Layer15Row4Expected = Basis.gf2-row8 false false false false false false false false

affine9Layer15Row4Exact :
  Decoder.expandMask8 affine9Layer15Basis affine9Layer15Row4Mask
  ≡ affine9Layer15Row4Expected
affine9Layer15Row4Exact = refl

affine9Layer15Row5Mask : Decoder.FactorMask8
affine9Layer15Row5Mask = Decoder.factor-mask8 false false false false false false false false

affine9Layer15Row5Expected : Basis.GF2Row8
affine9Layer15Row5Expected = Basis.gf2-row8 false false false false false false false false

affine9Layer15Row5Exact :
  Decoder.expandMask8 affine9Layer15Basis affine9Layer15Row5Mask
  ≡ affine9Layer15Row5Expected
affine9Layer15Row5Exact = refl

affine9Layer15Row6Mask : Decoder.FactorMask8
affine9Layer15Row6Mask = Decoder.factor-mask8 false false false false false false false false

affine9Layer15Row6Expected : Basis.GF2Row8
affine9Layer15Row6Expected = Basis.gf2-row8 false false false false false false false false

affine9Layer15Row6Exact :
  Decoder.expandMask8 affine9Layer15Basis affine9Layer15Row6Mask
  ≡ affine9Layer15Row6Expected
affine9Layer15Row6Exact = refl

affine9Layer15Row7Mask : Decoder.FactorMask8
affine9Layer15Row7Mask = Decoder.factor-mask8 true false false false false false false false

affine9Layer15Row7Expected : Basis.GF2Row8
affine9Layer15Row7Expected = Basis.gf2-row8 false false true false true true false false

affine9Layer15Row7Exact :
  Decoder.expandMask8 affine9Layer15Basis affine9Layer15Row7Mask
  ≡ affine9Layer15Row7Expected
affine9Layer15Row7Exact = refl

xor1Layer0Basis : Decoder.FactorBasis8
xor1Layer0Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

xor1Layer0Row0Mask : Decoder.FactorMask8
xor1Layer0Row0Mask = Decoder.factor-mask8 false false false false false false false false

xor1Layer0Row0Expected : Basis.GF2Row8
xor1Layer0Row0Expected = Basis.gf2-row8 false false false false false false false false

xor1Layer0Row0Exact :
  Decoder.expandMask8 xor1Layer0Basis xor1Layer0Row0Mask
  ≡ xor1Layer0Row0Expected
xor1Layer0Row0Exact = refl

xor1Layer0Row1Mask : Decoder.FactorMask8
xor1Layer0Row1Mask = Decoder.factor-mask8 false false false false false false false false

xor1Layer0Row1Expected : Basis.GF2Row8
xor1Layer0Row1Expected = Basis.gf2-row8 false false false false false false false false

xor1Layer0Row1Exact :
  Decoder.expandMask8 xor1Layer0Basis xor1Layer0Row1Mask
  ≡ xor1Layer0Row1Expected
xor1Layer0Row1Exact = refl

xor1Layer0Row2Mask : Decoder.FactorMask8
xor1Layer0Row2Mask = Decoder.factor-mask8 false false false false false false false false

xor1Layer0Row2Expected : Basis.GF2Row8
xor1Layer0Row2Expected = Basis.gf2-row8 false false false false false false false false

xor1Layer0Row2Exact :
  Decoder.expandMask8 xor1Layer0Basis xor1Layer0Row2Mask
  ≡ xor1Layer0Row2Expected
xor1Layer0Row2Exact = refl

xor1Layer0Row3Mask : Decoder.FactorMask8
xor1Layer0Row3Mask = Decoder.factor-mask8 false false false false false false false false

xor1Layer0Row3Expected : Basis.GF2Row8
xor1Layer0Row3Expected = Basis.gf2-row8 false false false false false false false false

xor1Layer0Row3Exact :
  Decoder.expandMask8 xor1Layer0Basis xor1Layer0Row3Mask
  ≡ xor1Layer0Row3Expected
xor1Layer0Row3Exact = refl

xor1Layer0Row4Mask : Decoder.FactorMask8
xor1Layer0Row4Mask = Decoder.factor-mask8 false false false false false false false false

xor1Layer0Row4Expected : Basis.GF2Row8
xor1Layer0Row4Expected = Basis.gf2-row8 false false false false false false false false

xor1Layer0Row4Exact :
  Decoder.expandMask8 xor1Layer0Basis xor1Layer0Row4Mask
  ≡ xor1Layer0Row4Expected
xor1Layer0Row4Exact = refl

xor1Layer0Row5Mask : Decoder.FactorMask8
xor1Layer0Row5Mask = Decoder.factor-mask8 false false false false false false false false

xor1Layer0Row5Expected : Basis.GF2Row8
xor1Layer0Row5Expected = Basis.gf2-row8 false false false false false false false false

xor1Layer0Row5Exact :
  Decoder.expandMask8 xor1Layer0Basis xor1Layer0Row5Mask
  ≡ xor1Layer0Row5Expected
xor1Layer0Row5Exact = refl

xor1Layer0Row6Mask : Decoder.FactorMask8
xor1Layer0Row6Mask = Decoder.factor-mask8 false false false false false false false false

xor1Layer0Row6Expected : Basis.GF2Row8
xor1Layer0Row6Expected = Basis.gf2-row8 false false false false false false false false

xor1Layer0Row6Exact :
  Decoder.expandMask8 xor1Layer0Basis xor1Layer0Row6Mask
  ≡ xor1Layer0Row6Expected
xor1Layer0Row6Exact = refl

xor1Layer0Row7Mask : Decoder.FactorMask8
xor1Layer0Row7Mask = Decoder.factor-mask8 false false false false false false false false

xor1Layer0Row7Expected : Basis.GF2Row8
xor1Layer0Row7Expected = Basis.gf2-row8 false false false false false false false false

xor1Layer0Row7Exact :
  Decoder.expandMask8 xor1Layer0Basis xor1Layer0Row7Mask
  ≡ xor1Layer0Row7Expected
xor1Layer0Row7Exact = refl

xor1Layer1Basis : Decoder.FactorBasis8
xor1Layer1Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false false false true false false true false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

xor1Layer1Row0Mask : Decoder.FactorMask8
xor1Layer1Row0Mask = Decoder.factor-mask8 false false false false false false false false

xor1Layer1Row0Expected : Basis.GF2Row8
xor1Layer1Row0Expected = Basis.gf2-row8 false false false false false false false false

xor1Layer1Row0Exact :
  Decoder.expandMask8 xor1Layer1Basis xor1Layer1Row0Mask
  ≡ xor1Layer1Row0Expected
xor1Layer1Row0Exact = refl

xor1Layer1Row1Mask : Decoder.FactorMask8
xor1Layer1Row1Mask = Decoder.factor-mask8 true false false false false false false false

xor1Layer1Row1Expected : Basis.GF2Row8
xor1Layer1Row1Expected = Basis.gf2-row8 false false false true false false true false

xor1Layer1Row1Exact :
  Decoder.expandMask8 xor1Layer1Basis xor1Layer1Row1Mask
  ≡ xor1Layer1Row1Expected
xor1Layer1Row1Exact = refl

xor1Layer1Row2Mask : Decoder.FactorMask8
xor1Layer1Row2Mask = Decoder.factor-mask8 false false false false false false false false

xor1Layer1Row2Expected : Basis.GF2Row8
xor1Layer1Row2Expected = Basis.gf2-row8 false false false false false false false false

xor1Layer1Row2Exact :
  Decoder.expandMask8 xor1Layer1Basis xor1Layer1Row2Mask
  ≡ xor1Layer1Row2Expected
xor1Layer1Row2Exact = refl

xor1Layer1Row3Mask : Decoder.FactorMask8
xor1Layer1Row3Mask = Decoder.factor-mask8 false false false false false false false false

xor1Layer1Row3Expected : Basis.GF2Row8
xor1Layer1Row3Expected = Basis.gf2-row8 false false false false false false false false

xor1Layer1Row3Exact :
  Decoder.expandMask8 xor1Layer1Basis xor1Layer1Row3Mask
  ≡ xor1Layer1Row3Expected
xor1Layer1Row3Exact = refl

xor1Layer1Row4Mask : Decoder.FactorMask8
xor1Layer1Row4Mask = Decoder.factor-mask8 false false false false false false false false

xor1Layer1Row4Expected : Basis.GF2Row8
xor1Layer1Row4Expected = Basis.gf2-row8 false false false false false false false false

xor1Layer1Row4Exact :
  Decoder.expandMask8 xor1Layer1Basis xor1Layer1Row4Mask
  ≡ xor1Layer1Row4Expected
xor1Layer1Row4Exact = refl

xor1Layer1Row5Mask : Decoder.FactorMask8
xor1Layer1Row5Mask = Decoder.factor-mask8 false false false false false false false false

xor1Layer1Row5Expected : Basis.GF2Row8
xor1Layer1Row5Expected = Basis.gf2-row8 false false false false false false false false

xor1Layer1Row5Exact :
  Decoder.expandMask8 xor1Layer1Basis xor1Layer1Row5Mask
  ≡ xor1Layer1Row5Expected
xor1Layer1Row5Exact = refl

xor1Layer1Row6Mask : Decoder.FactorMask8
xor1Layer1Row6Mask = Decoder.factor-mask8 false false false false false false false false

xor1Layer1Row6Expected : Basis.GF2Row8
xor1Layer1Row6Expected = Basis.gf2-row8 false false false false false false false false

xor1Layer1Row6Exact :
  Decoder.expandMask8 xor1Layer1Basis xor1Layer1Row6Mask
  ≡ xor1Layer1Row6Expected
xor1Layer1Row6Exact = refl

xor1Layer1Row7Mask : Decoder.FactorMask8
xor1Layer1Row7Mask = Decoder.factor-mask8 false false false false false false false false

xor1Layer1Row7Expected : Basis.GF2Row8
xor1Layer1Row7Expected = Basis.gf2-row8 false false false false false false false false

xor1Layer1Row7Exact :
  Decoder.expandMask8 xor1Layer1Basis xor1Layer1Row7Mask
  ≡ xor1Layer1Row7Expected
xor1Layer1Row7Exact = refl

xor1Layer16Basis : Decoder.FactorBasis8
xor1Layer16Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false false false true false true false true)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

xor1Layer16Row0Mask : Decoder.FactorMask8
xor1Layer16Row0Mask = Decoder.factor-mask8 true false false false false false false false

xor1Layer16Row0Expected : Basis.GF2Row8
xor1Layer16Row0Expected = Basis.gf2-row8 false false false true false true false true

xor1Layer16Row0Exact :
  Decoder.expandMask8 xor1Layer16Basis xor1Layer16Row0Mask
  ≡ xor1Layer16Row0Expected
xor1Layer16Row0Exact = refl

xor1Layer16Row1Mask : Decoder.FactorMask8
xor1Layer16Row1Mask = Decoder.factor-mask8 false false false false false false false false

xor1Layer16Row1Expected : Basis.GF2Row8
xor1Layer16Row1Expected = Basis.gf2-row8 false false false false false false false false

xor1Layer16Row1Exact :
  Decoder.expandMask8 xor1Layer16Basis xor1Layer16Row1Mask
  ≡ xor1Layer16Row1Expected
xor1Layer16Row1Exact = refl

xor1Layer16Row2Mask : Decoder.FactorMask8
xor1Layer16Row2Mask = Decoder.factor-mask8 false false false false false false false false

xor1Layer16Row2Expected : Basis.GF2Row8
xor1Layer16Row2Expected = Basis.gf2-row8 false false false false false false false false

xor1Layer16Row2Exact :
  Decoder.expandMask8 xor1Layer16Basis xor1Layer16Row2Mask
  ≡ xor1Layer16Row2Expected
xor1Layer16Row2Exact = refl

xor1Layer16Row3Mask : Decoder.FactorMask8
xor1Layer16Row3Mask = Decoder.factor-mask8 false false false false false false false false

xor1Layer16Row3Expected : Basis.GF2Row8
xor1Layer16Row3Expected = Basis.gf2-row8 false false false false false false false false

xor1Layer16Row3Exact :
  Decoder.expandMask8 xor1Layer16Basis xor1Layer16Row3Mask
  ≡ xor1Layer16Row3Expected
xor1Layer16Row3Exact = refl

xor1Layer16Row4Mask : Decoder.FactorMask8
xor1Layer16Row4Mask = Decoder.factor-mask8 false false false false false false false false

xor1Layer16Row4Expected : Basis.GF2Row8
xor1Layer16Row4Expected = Basis.gf2-row8 false false false false false false false false

xor1Layer16Row4Exact :
  Decoder.expandMask8 xor1Layer16Basis xor1Layer16Row4Mask
  ≡ xor1Layer16Row4Expected
xor1Layer16Row4Exact = refl

xor1Layer16Row5Mask : Decoder.FactorMask8
xor1Layer16Row5Mask = Decoder.factor-mask8 false false false false false false false false

xor1Layer16Row5Expected : Basis.GF2Row8
xor1Layer16Row5Expected = Basis.gf2-row8 false false false false false false false false

xor1Layer16Row5Exact :
  Decoder.expandMask8 xor1Layer16Basis xor1Layer16Row5Mask
  ≡ xor1Layer16Row5Expected
xor1Layer16Row5Exact = refl

xor1Layer16Row6Mask : Decoder.FactorMask8
xor1Layer16Row6Mask = Decoder.factor-mask8 false false false false false false false false

xor1Layer16Row6Expected : Basis.GF2Row8
xor1Layer16Row6Expected = Basis.gf2-row8 false false false false false false false false

xor1Layer16Row6Exact :
  Decoder.expandMask8 xor1Layer16Basis xor1Layer16Row6Mask
  ≡ xor1Layer16Row6Expected
xor1Layer16Row6Exact = refl

xor1Layer16Row7Mask : Decoder.FactorMask8
xor1Layer16Row7Mask = Decoder.factor-mask8 false false false false false false false false

xor1Layer16Row7Expected : Basis.GF2Row8
xor1Layer16Row7Expected = Basis.gf2-row8 false false false false false false false false

xor1Layer16Row7Exact :
  Decoder.expandMask8 xor1Layer16Basis xor1Layer16Row7Mask
  ≡ xor1Layer16Row7Expected
xor1Layer16Row7Exact = refl

bitrev9Layer0Basis : Decoder.FactorBasis8
bitrev9Layer0Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false false false false true true false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

bitrev9Layer0Row0Mask : Decoder.FactorMask8
bitrev9Layer0Row0Mask = Decoder.factor-mask8 false false false false false false false false

bitrev9Layer0Row0Expected : Basis.GF2Row8
bitrev9Layer0Row0Expected = Basis.gf2-row8 false false false false false false false false

bitrev9Layer0Row0Exact :
  Decoder.expandMask8 bitrev9Layer0Basis bitrev9Layer0Row0Mask
  ≡ bitrev9Layer0Row0Expected
bitrev9Layer0Row0Exact = refl

bitrev9Layer0Row1Mask : Decoder.FactorMask8
bitrev9Layer0Row1Mask = Decoder.factor-mask8 true false false false false false false false

bitrev9Layer0Row1Expected : Basis.GF2Row8
bitrev9Layer0Row1Expected = Basis.gf2-row8 false false false false true true false false

bitrev9Layer0Row1Exact :
  Decoder.expandMask8 bitrev9Layer0Basis bitrev9Layer0Row1Mask
  ≡ bitrev9Layer0Row1Expected
bitrev9Layer0Row1Exact = refl

bitrev9Layer0Row2Mask : Decoder.FactorMask8
bitrev9Layer0Row2Mask = Decoder.factor-mask8 false false false false false false false false

bitrev9Layer0Row2Expected : Basis.GF2Row8
bitrev9Layer0Row2Expected = Basis.gf2-row8 false false false false false false false false

bitrev9Layer0Row2Exact :
  Decoder.expandMask8 bitrev9Layer0Basis bitrev9Layer0Row2Mask
  ≡ bitrev9Layer0Row2Expected
bitrev9Layer0Row2Exact = refl

bitrev9Layer0Row3Mask : Decoder.FactorMask8
bitrev9Layer0Row3Mask = Decoder.factor-mask8 false false false false false false false false

bitrev9Layer0Row3Expected : Basis.GF2Row8
bitrev9Layer0Row3Expected = Basis.gf2-row8 false false false false false false false false

bitrev9Layer0Row3Exact :
  Decoder.expandMask8 bitrev9Layer0Basis bitrev9Layer0Row3Mask
  ≡ bitrev9Layer0Row3Expected
bitrev9Layer0Row3Exact = refl

bitrev9Layer0Row4Mask : Decoder.FactorMask8
bitrev9Layer0Row4Mask = Decoder.factor-mask8 false false false false false false false false

bitrev9Layer0Row4Expected : Basis.GF2Row8
bitrev9Layer0Row4Expected = Basis.gf2-row8 false false false false false false false false

bitrev9Layer0Row4Exact :
  Decoder.expandMask8 bitrev9Layer0Basis bitrev9Layer0Row4Mask
  ≡ bitrev9Layer0Row4Expected
bitrev9Layer0Row4Exact = refl

bitrev9Layer0Row5Mask : Decoder.FactorMask8
bitrev9Layer0Row5Mask = Decoder.factor-mask8 false false false false false false false false

bitrev9Layer0Row5Expected : Basis.GF2Row8
bitrev9Layer0Row5Expected = Basis.gf2-row8 false false false false false false false false

bitrev9Layer0Row5Exact :
  Decoder.expandMask8 bitrev9Layer0Basis bitrev9Layer0Row5Mask
  ≡ bitrev9Layer0Row5Expected
bitrev9Layer0Row5Exact = refl

bitrev9Layer0Row6Mask : Decoder.FactorMask8
bitrev9Layer0Row6Mask = Decoder.factor-mask8 false false false false false false false false

bitrev9Layer0Row6Expected : Basis.GF2Row8
bitrev9Layer0Row6Expected = Basis.gf2-row8 false false false false false false false false

bitrev9Layer0Row6Exact :
  Decoder.expandMask8 bitrev9Layer0Basis bitrev9Layer0Row6Mask
  ≡ bitrev9Layer0Row6Expected
bitrev9Layer0Row6Exact = refl

bitrev9Layer0Row7Mask : Decoder.FactorMask8
bitrev9Layer0Row7Mask = Decoder.factor-mask8 false false false false false false false false

bitrev9Layer0Row7Expected : Basis.GF2Row8
bitrev9Layer0Row7Expected = Basis.gf2-row8 false false false false false false false false

bitrev9Layer0Row7Exact :
  Decoder.expandMask8 bitrev9Layer0Basis bitrev9Layer0Row7Mask
  ≡ bitrev9Layer0Row7Expected
bitrev9Layer0Row7Exact = refl

bitrev9Layer15Basis : Decoder.FactorBasis8
bitrev9Layer15Basis =
  Decoder.factor-basis8
    (Basis.gf2-row8 false false false false true false false true)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)
    (Basis.gf2-row8 false false false false false false false false)

bitrev9Layer15Row0Mask : Decoder.FactorMask8
bitrev9Layer15Row0Mask = Decoder.factor-mask8 false false false false false false false false

bitrev9Layer15Row0Expected : Basis.GF2Row8
bitrev9Layer15Row0Expected = Basis.gf2-row8 false false false false false false false false

bitrev9Layer15Row0Exact :
  Decoder.expandMask8 bitrev9Layer15Basis bitrev9Layer15Row0Mask
  ≡ bitrev9Layer15Row0Expected
bitrev9Layer15Row0Exact = refl

bitrev9Layer15Row1Mask : Decoder.FactorMask8
bitrev9Layer15Row1Mask = Decoder.factor-mask8 false false false false false false false false

bitrev9Layer15Row1Expected : Basis.GF2Row8
bitrev9Layer15Row1Expected = Basis.gf2-row8 false false false false false false false false

bitrev9Layer15Row1Exact :
  Decoder.expandMask8 bitrev9Layer15Basis bitrev9Layer15Row1Mask
  ≡ bitrev9Layer15Row1Expected
bitrev9Layer15Row1Exact = refl

bitrev9Layer15Row2Mask : Decoder.FactorMask8
bitrev9Layer15Row2Mask = Decoder.factor-mask8 false false false false false false false false

bitrev9Layer15Row2Expected : Basis.GF2Row8
bitrev9Layer15Row2Expected = Basis.gf2-row8 false false false false false false false false

bitrev9Layer15Row2Exact :
  Decoder.expandMask8 bitrev9Layer15Basis bitrev9Layer15Row2Mask
  ≡ bitrev9Layer15Row2Expected
bitrev9Layer15Row2Exact = refl

bitrev9Layer15Row3Mask : Decoder.FactorMask8
bitrev9Layer15Row3Mask = Decoder.factor-mask8 false false false false false false false false

bitrev9Layer15Row3Expected : Basis.GF2Row8
bitrev9Layer15Row3Expected = Basis.gf2-row8 false false false false false false false false

bitrev9Layer15Row3Exact :
  Decoder.expandMask8 bitrev9Layer15Basis bitrev9Layer15Row3Mask
  ≡ bitrev9Layer15Row3Expected
bitrev9Layer15Row3Exact = refl

bitrev9Layer15Row4Mask : Decoder.FactorMask8
bitrev9Layer15Row4Mask = Decoder.factor-mask8 false false false false false false false false

bitrev9Layer15Row4Expected : Basis.GF2Row8
bitrev9Layer15Row4Expected = Basis.gf2-row8 false false false false false false false false

bitrev9Layer15Row4Exact :
  Decoder.expandMask8 bitrev9Layer15Basis bitrev9Layer15Row4Mask
  ≡ bitrev9Layer15Row4Expected
bitrev9Layer15Row4Exact = refl

bitrev9Layer15Row5Mask : Decoder.FactorMask8
bitrev9Layer15Row5Mask = Decoder.factor-mask8 false false false false false false false false

bitrev9Layer15Row5Expected : Basis.GF2Row8
bitrev9Layer15Row5Expected = Basis.gf2-row8 false false false false false false false false

bitrev9Layer15Row5Exact :
  Decoder.expandMask8 bitrev9Layer15Basis bitrev9Layer15Row5Mask
  ≡ bitrev9Layer15Row5Expected
bitrev9Layer15Row5Exact = refl

bitrev9Layer15Row6Mask : Decoder.FactorMask8
bitrev9Layer15Row6Mask = Decoder.factor-mask8 false false false false false false false false

bitrev9Layer15Row6Expected : Basis.GF2Row8
bitrev9Layer15Row6Expected = Basis.gf2-row8 false false false false false false false false

bitrev9Layer15Row6Exact :
  Decoder.expandMask8 bitrev9Layer15Basis bitrev9Layer15Row6Mask
  ≡ bitrev9Layer15Row6Expected
bitrev9Layer15Row6Exact = refl

bitrev9Layer15Row7Mask : Decoder.FactorMask8
bitrev9Layer15Row7Mask = Decoder.factor-mask8 true false false false false false false false

bitrev9Layer15Row7Expected : Basis.GF2Row8
bitrev9Layer15Row7Expected = Basis.gf2-row8 false false false false true false false true

bitrev9Layer15Row7Exact :
  Decoder.expandMask8 bitrev9Layer15Basis bitrev9Layer15Row7Mask
  ≡ bitrev9Layer15Row7Expected
bitrev9Layer15Row7Exact = refl

compiledFactorLayerCount : Nat
compiledFactorLayerCount = 28

compiledFactorLayerCountIsTwentyEight : compiledFactorLayerCount ≡ 28
compiledFactorLayerCountIsTwentyEight = refl

compiledRowCount : Nat
compiledRowCount = 224

compiledRowCountIsTwoHundredTwentyFour : compiledRowCount ≡ 224
compiledRowCountIsTwoHundredTwentyFour = refl

record GF2FactorPacketFullPortfolioBoundary : Set where
  constructor gf2-factor-packet-full-portfolio-boundary
  field
    independentPrecodecRuntimeReceiptInherited : Bool
    allTwentyEightFactorLayersCompiledToFormalTerms : Bool
    allTwoHundredTwentyFourRowEqualitiesSourceWritten : Bool
    factorMaskDecoderSemanticsInherited : Bool
    sourceLevelFiniteReplayPortfolioComplete : Bool
    exactHeadAgdaKernelReceiptObserved : Bool
    packedRuntimeBytesWeldedToFormalConstructors : Bool
    producerBasisSearchAlgorithmProved : Bool
    productionRSA260CustodyPaid : Bool
open GF2FactorPacketFullPortfolioBoundary public

canonicalGF2FactorPacketFullPortfolioBoundary :
  GF2FactorPacketFullPortfolioBoundary
canonicalGF2FactorPacketFullPortfolioBoundary =
  gf2-factor-packet-full-portfolio-boundary
    true
    true
    true
    true
    true
    false
    false
    false
    false

data GF2FactorPacketFullPortfolioResidual : Set where
  obtainExactHeadAgdaKernelReceiptForCompiledPortfolio : GF2FactorPacketFullPortfolioResidual
  weldPackedRuntimeBytesToFormalFactorConstructors : GF2FactorPacketFullPortfolioResidual
  provePackedEightBitRowRepresentationExact : GF2FactorPacketFullPortfolioResidual
  compileCertifiedFactorPacketsIntoHybridLayerCodec : GF2FactorPacketFullPortfolioResidual
  acquireSameObjectAStarOrFSols : GF2FactorPacketFullPortfolioResidual

firstGF2FactorPacketFullPortfolioResidual :
  GF2FactorPacketFullPortfolioResidual
firstGF2FactorPacketFullPortfolioResidual =
  obtainExactHeadAgdaKernelReceiptForCompiledPortfolio

data SourcePortfolioMeansKernelReceipt : Set where
data FormalRowsMeanPackedByteWeld : Set where
data SyntheticPortfolioMeansProductionCustody : Set where

sourcePortfolioDoesNotCreateKernelReceipt :
  SourcePortfolioMeansKernelReceipt → ⊥
sourcePortfolioDoesNotCreateKernelReceipt ()

formalRowsDoNotCreatePackedByteWeld : FormalRowsMeanPackedByteWeld → ⊥
formalRowsDoNotCreatePackedByteWeld ()

syntheticPortfolioDoesNotCreateProductionCustody :
  SyntheticPortfolioMeansProductionCustody → ⊥
syntheticPortfolioDoesNotCreateProductionCustody ()
