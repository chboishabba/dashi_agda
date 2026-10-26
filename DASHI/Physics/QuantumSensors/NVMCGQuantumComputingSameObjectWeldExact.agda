module DASHI.Physics.QuantumSensors.NVMCGQuantumComputingSameObjectWeldExact where

-- Same-object bridge in the *diamond MCG PR lineage*.
-- This module consumes its existing NV axial Hamiltonian / qutrit basis.
-- C3 level labels below are a chart only, not a physical C3 symmetry.
-- The spin-one/cyclic chart and finite SUSY-QM consumer in PR #1262
-- remain independently owned, pending an explicit stacked merge.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Algebra.Quantum.FiniteQutrit as Q
import DASHI.Physics.QuantumSensors.NVSpinOneAxialExact as NV

-- Convention fixed in existing MCG implementation:
-- c0 = ket0 = m_s +1; c1 = ket1 = m_s 0; c2 = ket2 = m_s -1.
labelToKet : C3.C3 → Q.QutritBasis
labelToKet C3.c0 = Q.ket0
labelToKet C3.c1 = Q.ket1
labelToKet C3.c2 = Q.ket2

ketToLabel : Q.QutritBasis → C3.C3
ketToLabel Q.ket0 = C3.c0
ketToLabel Q.ket1 = C3.c1
ketToLabel Q.ket2 = C3.c2

labelKetRoundTrip : ∀ x → ketToLabel (labelToKet x) ≡ x
labelKetRoundTrip C3.c0 = refl
labelKetRoundTrip C3.c1 = refl
labelKetRoundTrip C3.c2 = refl

ketLabelRoundTrip : ∀ x → labelToKet (ketToLabel x) ≡ x
ketLabelRoundTrip Q.ket0 = refl
ketLabelRoundTrip Q.ket1 = refl
ketLabelRoundTrip Q.ket2 = refl

levelEnergy : NV.AxialNV → C3.C3 → ℚ
levelEnergy p x = NV.energy p (labelToKet x)

-- +1 <-> -1 exchanges the axial Zeeman field's sign.
swapPlusMinus : C3.C3 → C3.C3
swapPlusMinus C3.c0 = C3.c2
swapPlusMinus C3.c1 = C3.c1
swapPlusMinus C3.c2 = C3.c0

swapInvolution : ∀ x → swapPlusMinus (swapPlusMinus x) ≡ x
swapInvolution C3.c0 = refl
swapInvolution C3.c1 = refl
swapInvolution C3.c2 = refl

reverseField : NV.AxialNV → NV.AxialNV
reverseField (NV.axial-nv d gamma b) = NV.axial-nv d gamma (- b)

-- This is a source-native, parameterised physical *axial spectral*
-- symmetry; it is not a gate operation or a cross-core transport.
axialSwapFieldReversal :
  ∀ (p : NV.AxialNV) (x : C3.C3) →
  levelEnergy p (swapPlusMinus x) ≡
  levelEnergy (reverseField p) x
axialSwapFieldReversal (NV.axial-nv d gamma b) C3.c0 =
  solve (d ∷ gamma ∷ b ∷ [])
axialSwapFieldReversal (NV.axial-nv d gamma b) C3.c1 = refl
axialSwapFieldReversal (NV.axial-nv d gamma b) C3.c2 =
  solve (d ∷ gamma ∷ b ∷ [])

-- At B=0, exchange of the m_s=±1 branches is spectral symmetry.
axialSwapZeroField :
  ∀ (d gamma : ℚ) (x : C3.C3) →
  levelEnergy (NV.axial-nv d gamma 0ℚ) (swapPlusMinus x)
  ≡ levelEnergy (NV.axial-nv d gamma 0ℚ) x
axialSwapZeroField d gamma C3.c0 =
  solve (d ∷ gamma ∷ [])
axialSwapZeroField d gamma C3.c1 = refl
axialSwapZeroField d gamma C3.c2 =
  solve (d ∷ gamma ∷ [])

-- Do not infer a local C3v spin representation, optical interference
-- invariance or an experimentally implementable SUSY supercharge from
-- this finite index/basis identification alone.
