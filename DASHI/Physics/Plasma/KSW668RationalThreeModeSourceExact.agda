module DASHI.Physics.Plasma.KSW668RationalThreeModeSourceExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; -_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Plasma.MHDPlusMinusProjectedPseudoEnergyExact as State

------------------------------------------------------------------------
-- A1 REAL SOURCE COEFFICIENTS ON THE ORIGINAL C3 RATIONAL CARRIER.
-- This is a total sparse function on ALL integer Fourier modes, not
-- merely an unrelated finite vector record. Negative modes are original
-- conjugates, zero outside the six explicitly selected nonzero modes.
--
-- p=(1,0,0); q=(0,1,0); k=p+q=(1,1,0).
-- z+(q)=e_x, z+(k)=e_x-e_y, at negative modes same real values.
-- z-(p)=+i e_y or -i e_y, at -p its original conjugate.
--
-- Physical magnetic b=(z+ - z-)/2:
-- |b(k)|²=1/2 > |b(q)|²=1/4 for BOTH signs.
-- Selected original normal-form transfer Re[-i(z-(p)·q)
--   <z+(k),z+(q)>] is +1 or -1.
--
-- Proving all-mode Fourier RealityCondition, DivergenceFreeCondition
-- and normalized original rational inverse-square projector in Agda is
-- NOT done by these source definitions or isolated row reductions.
------------------------------------------------------------------------

F : C3.RealField _
F = Rational.rationalRealField

p q k : Z3.FourierMode
p = Z3.mode (+ 1) (+ 0) (+ 0)
q = Z3.mode (+ 0) (+ 1) (+ 0)
k = Z3.mode (+ 1) (+ 1) (+ 0)

zeroC unitC negUnitC iC negIC : C3.Complex F
zeroC = C3.complex 0ℚ 0ℚ
unitC = C3.complex 1ℚ 0ℚ
negUnitC = C3.complex (- 1ℚ) 0ℚ
iC = C3.complex 0ℚ 1ℚ
negIC = C3.complex 0ℚ (- 1ℚ)

plusQ plusK minusP minusNegativeP : C3.Complex3 F
plusQ = C3.complex3 unitC zeroC zeroC
plusK = C3.complex3 unitC negUnitC zeroC
minusP = C3.complex3 zeroC iC zeroC
minusNegativeP = C3.complex3 zeroC negIC zeroC

chooseVector : Bool → C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
chooseVector true yes no = yes
chooseVector false yes no = no

data SelectedTransferSign : Set where
  plusSigned minusSigned : SelectedTransferSign

positiveMinusSource : SelectedTransferSign → C3.Complex3 F
positiveMinusSource plusSigned = minusP
positiveMinusSource minusSigned = minusNegativeP

negativeMinusSource : SelectedTransferSign → C3.Complex3 F
negativeMinusSource plusSigned = minusNegativeP
negativeMinusSource minusSigned = minusP

sourceZPlus : Z3.FourierMode → C3.Complex3 F
sourceZPlus mode =
  chooseVector (Output.modeEqual mode q) plusQ
  (chooseVector (Output.modeEqual mode (Z3.negateMode q)) plusQ
  (chooseVector (Output.modeEqual mode k) plusK
  (chooseVector (Output.modeEqual mode (Z3.negateMode k)) plusK
    (C3.complex3Zero F))))

sourceZMinus :
  SelectedTransferSign → Z3.FourierMode → C3.Complex3 F
sourceZMinus sign mode =
  chooseVector (Output.modeEqual mode p)
    (positiveMinusSource sign)
  (chooseVector (Output.modeEqual mode (Z3.negateMode p))
    (negativeMinusSource sign)
    (C3.complex3Zero F))

sourcePhysicalDoubledMagnetic :
  SelectedTransferSign → Z3.FourierMode → C3.Complex3 F
sourcePhysicalDoubledMagnetic sign mode =
  C3.complex3Subtract
    (sourceZPlus mode) (sourceZMinus sign mode)

sourceDoubledSquaredMagnetic :
  SelectedTransferSign → Z3.FourierMode → ℚ
sourceDoubledSquaredMagnetic sign mode =
  C3.real
    (C3.hermitianPairing3
      (sourcePhysicalDoubledMagnetic sign mode)
      (sourcePhysicalDoubledMagnetic sign mode))

------------------------------------------------------------------------
-- ORIGINAL state constructor: its proof arguments are not replaced by
-- a marker, and must be discharged globally before inhabiting the state.
------------------------------------------------------------------------

stateFromGloballyCheckedSource :
  (E : C3.IntegerEmbedding F) →
  (sign : SelectedTransferSign) →
  Audit.RealityCondition sourceZPlus →
  Audit.RealityCondition (sourceZMinus sign) →
  Audit.DivergenceFreeCondition E sourceZPlus →
  Audit.DivergenceFreeCondition E (sourceZMinus sign) →
  State.IdealElsasserFourierState F E
stateFromGloballyCheckedSource E sign plusReality minusReality
    plusDivergence minusDivergence =
  State.ideal-elsasser-fourier-state
    sourceZPlus (sourceZMinus sign)
    plusReality minusReality
    plusDivergence minusDivergence
    "KSW668 original rational sparse six-mode source; global proof gates are explicit"

------------------------------------------------------------------------
-- This module is a genuine source definition and conditional constructor;
-- NOT an Agda proof of the all-mode conditions or signed strength theorem.
-- Python exact source-form check:
-- scripts/ksw668_a1_original_rational_fourier_witness.py
------------------------------------------------------------------------
