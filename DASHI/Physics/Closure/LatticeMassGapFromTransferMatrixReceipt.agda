module DASHI.Physics.Closure.LatticeMassGapFromTransferMatrixReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ReflectionPositivityForWilsonReceipt as RP

data LatticeGapReason : Set where
  compactGaugeGroupPeterWeyl :
    LatticeGapReason

  finiteSpatialLatticeDiscreteSpectrum :
    LatticeGapReason

  continuumLimitMayCloseGap :
    LatticeGapReason

canonicalLatticeGapReasons : List LatticeGapReason
canonicalLatticeGapReasons =
  compactGaugeGroupPeterWeyl
  ∷ finiteSpatialLatticeDiscreteSpectrum
  ∷ continuumLimitMayCloseGap
  ∷ []

record LatticeMassGapFromTransferMatrixReceipt : Setω where
  field
    reflectionReceipt :
      RP.ReflectionPositivityForWilsonReceipt

    finiteReflectionPositive :
      RP.finiteLatticeReflectionPositivityInherited reflectionReceipt ≡ true

    transferMatrixDefined :
      Bool

    transferMatrixDefinedIsTrue :
      transferMatrixDefined ≡ true

    finiteLatticeSpectrumDiscrete :
      Bool

    finiteLatticeSpectrumDiscreteIsTrue :
      finiteLatticeSpectrumDiscrete ≡ true

    finiteLatticeGapPositive :
      Bool

    finiteLatticeGapPositiveIsTrue :
      finiteLatticeGapPositive ≡ true

    uniformContinuumGapProved :
      Bool

    uniformContinuumGapProvedIsFalse :
      uniformContinuumGapProved ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    reasons :
      List LatticeGapReason

    reasonsAreCanonical :
      reasons ≡ canonicalLatticeGapReasons

open LatticeMassGapFromTransferMatrixReceipt public

canonicalLatticeMassGapFromTransferMatrixReceipt :
  LatticeMassGapFromTransferMatrixReceipt
canonicalLatticeMassGapFromTransferMatrixReceipt =
  record
    { reflectionReceipt =
        RP.canonicalReflectionPositivityForWilsonReceipt
    ; finiteReflectionPositive =
        refl
    ; transferMatrixDefined =
        true
    ; transferMatrixDefinedIsTrue =
        refl
    ; finiteLatticeSpectrumDiscrete =
        true
    ; finiteLatticeSpectrumDiscreteIsTrue =
        refl
    ; finiteLatticeGapPositive =
        true
    ; finiteLatticeGapPositiveIsTrue =
        refl
    ; uniformContinuumGapProved =
        false
    ; uniformContinuumGapProvedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; reasons =
        canonicalLatticeGapReasons
    ; reasonsAreCanonical =
        refl
    }

latticeMassGapFromTransferMatrixKeepsClayFalse :
  clayYangMillsPromoted canonicalLatticeMassGapFromTransferMatrixReceipt
  ≡
  false
latticeMassGapFromTransferMatrixKeepsClayFalse =
  refl

latticeMassGapFromTransferMatrixKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalLatticeMassGapFromTransferMatrixReceipt
  ≡
  false
latticeMassGapFromTransferMatrixKeepsTerminalFalse =
  refl
