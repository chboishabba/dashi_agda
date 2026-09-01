module DASHI.Physics.Closure.NSTriadKNLiteralNonzeroCutoffSupportRound404Exact where

------------------------------------------------------------------------
-- ROUND404 / `nonzeroCutoffModes` REALLY CARRIES NONZERO MODES
--
-- The generic Audit marker `zeroModeExcluded : Set` is intentionally useless
-- as proof authority.  The canonical support list itself is stronger:
-- Round34 defines it by executable removal of exactly the zero Fourier mode.
--
-- This file proves directly from that recursion that every member of
-- `nonzeroCutoffModes N` is a NonZeroMode.  In particular Round71's
-- `fixedAuditSystem`, whose modes field is definitionally this list, supplies
-- the support realization required by R403 without consulting the weak Audit
-- marker.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNFixedCanonicalRealityVectorFieldRound71Exact as Fixed

removeZeroMemberNonzero :
  ∀ {mode modes} →
  mode Cube.∈ Canonical.removeZero modes →
  Z3.NonZeroMode mode
removeZeroMemberNonzero {modes = []} ()
removeZeroMemberNonzero {mode} {modes = head ∷ tail} member
  with Output.modeEqual head Z3.zeroMode in headDecision
... | true = removeZeroMemberNonzero {mode = mode} {modes = tail} member
... | false with member
...   | Cube.here refl = record
      { Z3.notZero = λ headZero →
          Output.falseNotTrue
            (Agda.Builtin.Equality.trans
              (Agda.Builtin.Equality.sym headDecision)
              (Output.modeEqualComplete headZero))
      }
...   | Cube.there rest =
      removeZeroMemberNonzero {mode = mode} {modes = tail} rest

nonzeroCutoffMemberNonzero :
  ∀ {N mode} →
  mode Cube.∈ Canonical.nonzeroCutoffModes N →
  Z3.NonZeroMode mode
nonzeroCutoffMemberNonzero = removeZeroMemberNonzero

fixedAuditRetainedModeNonzero :
  ∀ {r} {F : DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier.RealField r}
    {E : DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier.IntegerEmbedding F}
    (geometry : Fixed.FixedCanonicalGeometry F E)
    (state : Fixed.CanonicalRealityState F (Fixed.cutoff geometry))
    (mode : Z3.FourierMode) →
  mode Cube.∈
    DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit.modes
      (Fixed.fixedAuditSystem geometry state) →
  Z3.NonZeroMode mode
fixedAuditRetainedModeNonzero geometry state mode member =
  nonzeroCutoffMemberNonzero member

round404AuditMarkerUsedAsProofAuthority : Bool
round404AuditMarkerUsedAsProofAuthority = false

round404LiteralRemoveZeroSupportCarriesNonzeroProof : Bool
round404LiteralRemoveZeroSupportCarriesNonzeroProof = true

round404Round71FixedAuditSupportRecovered : Bool
round404Round71FixedAuditSupportRecovered = true
