module DASHI.Physics.Plasma.KSW668SparsePairRealityExact where

------------------------------------------------------------------------
-- A1: a *genuinely global* Z^3 Fourier reality proof for one selected
-- original rational C3 vector and its negative-mode conjugate partner.
-- The arguments range over ALL integer lattice modes, not a finite grid.
--
-- This module deliberately uses the existing Output.modeEqual decider,
-- Symmetry.negateModeInvolutive and the previously published C3 conjugate
-- involution/zero laws. A self-opposite positive mode is explicitly
-- forbidden; the positive/negative hit collision is proved impossible.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNCanonicalVelocityRealityRound35Exact as Canonical
import DASHI.Physics.Plasma.KSW668SparseModeLookupNegationExact as Lookup
import DASHI.Physics.Plasma.KSW668RationalThreeModeSourceExact as Source

F : C3.RealField _
F = Source.F

pairedSparseFourier :
  (positive : Z3.FourierMode) →
  C3.Complex3 F →
  Z3.FourierMode → C3.Complex3 F
pairedSparseFourier positive vector mode =
  Source.chooseVector (Output.modeEqual mode positive) vector
    (Source.chooseVector
      (Output.modeEqual mode (Z3.negateMode positive))
      (C3.complex3Conjugate vector)
      (C3.complex3Zero F))

pairedSparseReality :
  (positive : Z3.FourierMode) →
  (vector : C3.Complex3 F) →
  (notSelfOpposite : positive ≡ Z3.negateMode positive → ⊥) →
  (mode : Z3.FourierMode) →
  pairedSparseFourier positive vector (Z3.negateMode mode)
  ≡ C3.complex3Conjugate (pairedSparseFourier positive vector mode)
pairedSparseReality positive vector notSelfOpposite mode
  rewrite Lookup.sourceModeEqualNegateCorrespondence mode positive
    | Lookup.sourceModeEqualNegateCorrespondence
        mode (Z3.negateMode positive)
    | Symmetry.negateModeInvolutive positive
  with Output.modeEqual mode positive in originalPositive
     | Output.modeEqual mode (Z3.negateMode positive) in originalNegative
... | true | true =
  let
    eqPositive = Output.modeEqualSound originalPositive
    eqNegative = Output.modeEqualSound originalNegative
  in ⊥-elim (notSelfOpposite (trans (sym eqPositive) eqNegative))
... | true | false = refl
... | false | true =
  sym (C3.complex3ConjugateInvolutive vector)
... | false | false =
  sym Canonical.complex3ConjugateZero

sourcePNotSelfOpposite :
  Source.p ≡ Z3.negateMode Source.p → ⊥
sourcePNotSelfOpposite ()

-- One-component positive p-mode for the actual sign-selected zMinus.
sourceMinusPaired :
  (sign : Source.SelectedTransferSign) →
  (mode : Z3.FourierMode) → C3.Complex3 F
sourceMinusPaired sign =
  pairedSparseFourier Source.p (Source.positiveMinusSource sign)

sourceMinusPairedIsOriginal :
  (sign : Source.SelectedTransferSign) →
  (mode : Z3.FourierMode) →
  sourceMinusPaired sign mode ≡ Source.sourceZMinus sign mode
sourceMinusPairedIsOriginal Source.plusSigned mode = refl
sourceMinusPairedIsOriginal Source.minusSigned mode = refl

-- No caller-supplied RealityCondition parameter: the original complete
-- Z3-indexed zMinus is a Fourier-real state for BOTH transfer signs.
sourceMinusAllModeReality :
  (sign : Source.SelectedTransferSign) →
  (mode : Z3.FourierMode) →
  Source.sourceZMinus sign (Z3.negateMode mode)
  ≡ C3.complex3Conjugate (Source.sourceZMinus sign mode)
sourceMinusAllModeReality sign mode =
  trans
    (sym (sourceMinusPairedIsOriginal sign (Z3.negateMode mode)))
    (trans
      (pairedSparseReality Source.p
        (Source.positiveMinusSource sign)
        sourcePNotSelfOpposite mode)
      (cong C3.complex3Conjugate
        (sourceMinusPairedIsOriginal sign mode)))

------------------------------------------------------------------------
-- This proves reality for sourceZMinus on all modes. SourceZPlus has TWO
-- distinct positive representatives (q and k) and still requires the
-- no-collision/compatibility weld to the original nested source selector.
-- Original modewise divergence and inverse square are separately OPEN.
------------------------------------------------------------------------
