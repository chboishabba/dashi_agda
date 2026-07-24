module DASHI.Algebra.Quantum.QutritWeyl where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Algebra.Quantum.FiniteQutrit

------------------------------------------------------------------------
-- Symbolic qutrit phase arithmetic and generalized Pauli/Weyl operators.

data Phase3 : Set where
  one : Phase3
  omega : Phase3
  omegaSquared : Phase3

phaseMul : Phase3 → Phase3 → Phase3
phaseMul one p = p
phaseMul omega one = omega
phaseMul omega omega = omegaSquared
phaseMul omega omegaSquared = one
phaseMul omegaSquared one = omegaSquared
phaseMul omegaSquared omega = one
phaseMul omegaSquared omegaSquared = omega

record PhasedBasis : Set where
  constructor phased
  field
    phase : Phase3
    basis : QutritBasis

open PhasedBasis public

X : QutritBasis → QutritBasis
X ket0 = ket1
X ket1 = ket2
X ket2 = ket0

Z : QutritBasis → PhasedBasis
Z ket0 = phased one ket0
Z ket1 = phased omega ket1
Z ket2 = phased omegaSquared ket2

X³IsIdentity : (q : QutritBasis) → X (X (X q)) ≡ q
X³IsIdentity ket0 = refl
X³IsIdentity ket1 = refl
X³IsIdentity ket2 = refl

ZPhase : QutritBasis → Phase3
ZPhase ket0 = one
ZPhase ket1 = omega
ZPhase ket2 = omegaSquared

Z³PhaseIsIdentity :
  (q : QutritBasis) →
  phaseMul (ZPhase q) (phaseMul (ZPhase q) (ZPhase q)) ≡ one
Z³PhaseIsIdentity ket0 = refl
Z³PhaseIsIdentity ket1 = refl
Z³PhaseIsIdentity ket2 = refl

ZX : QutritBasis → PhasedBasis
ZX q = Z (X q)

omegaXZ : QutritBasis → PhasedBasis
omegaXZ q = phased (phaseMul omega (ZPhase q)) (X q)

qutritWeylCommutation : (q : QutritBasis) → ZX q ≡ omegaXZ q
qutritWeylCommutation ket0 = refl
qutritWeylCommutation ket1 = refl
qutritWeylCommutation ket2 = refl

record FiniteQutritWeylCertificate : Set where
  field
    shift : QutritBasis → QutritBasis
    clock : QutritBasis → PhasedBasis
    shiftOrderThree : (q : QutritBasis) → shift (shift (shift q)) ≡ q
    clockPhaseOrderThree :
      (q : QutritBasis) →
      phaseMul (phase (clock q))
        (phaseMul (phase (clock q)) (phase (clock q))) ≡ one
    weylCommutation : (q : QutritBasis) → clock (shift q) ≡ omegaXZ q

open FiniteQutritWeylCertificate public

canonicalFiniteQutritWeylCertificate : FiniteQutritWeylCertificate
canonicalFiniteQutritWeylCertificate =
  record
    { shift = X
    ; clock = Z
    ; shiftOrderThree = X³IsIdentity
    ; clockPhaseOrderThree = Z³PhaseIsIdentity
    ; weylCommutation = qutritWeylCommutation
    }
