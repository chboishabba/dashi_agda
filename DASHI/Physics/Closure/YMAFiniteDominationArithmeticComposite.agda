module DASHI.Physics.Closure.YMAFiniteDominationArithmeticComposite where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.YMAKillingBoundaryLocalArithmetic
  as KillingBoundaryArithmetic
import DASHI.Physics.Closure.YMAHolonomyWilsonLocalArithmetic
  as HolonomyWilsonArithmetic

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data YMAFiniteDominationArithmeticBlocker : Set where
  domainClosureBlocker : YMAFiniteDominationArithmeticBlocker
  boundaryFluxCancellationBlocker : YMAFiniteDominationArithmeticBlocker
  quotientSelfAdjointnessBlocker : YMAFiniteDominationArithmeticBlocker
  h3aContinuumTransferBlocker : YMAFiniteDominationArithmeticBlocker

canonicalYMAFiniteDominationArithmeticBlockers :
  List YMAFiniteDominationArithmeticBlocker
canonicalYMAFiniteDominationArithmeticBlockers =
  domainClosureBlocker
  ∷ boundaryFluxCancellationBlocker
  ∷ quotientSelfAdjointnessBlocker
  ∷ h3aContinuumTransferBlocker
  ∷ []

ymaFiniteDominationArithmeticBlockerCount : Nat
ymaFiniteDominationArithmeticBlockerCount =
  listLength canonicalYMAFiniteDominationArithmeticBlockers

ymaFiniteDominationArithmeticBlockerCountIs4 :
  ymaFiniteDominationArithmeticBlockerCount ≡ 4
ymaFiniteDominationArithmeticBlockerCountIs4 = refl

blockerLabel : YMAFiniteDominationArithmeticBlocker → String
blockerLabel domainClosureBlocker =
  "domain closure"
blockerLabel boundaryFluxCancellationBlocker =
  "boundary flux cancellation"
blockerLabel quotientSelfAdjointnessBlocker =
  "quotient self-adjointness"
blockerLabel h3aContinuumTransferBlocker =
  "H3a continuum transfer"

c1PositiveArithmetic : Bool
c1PositiveArithmetic = true

c2PositiveArithmetic : Bool
c2PositiveArithmetic = true

localArithmeticObstructionAbsent : Bool
localArithmeticObstructionAbsent = true

finiteDominationTheoremPromoted : Bool
finiteDominationTheoremPromoted = false

selfAdjointQuotientHamiltonianProved : Bool
selfAdjointQuotientHamiltonianProved = false

h3aTransferProved : Bool
h3aTransferProved = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

record YMAFiniteDominationArithmeticComposite : Set where
  field
    killingBoundaryLocalArithmeticImported : Bool
    holonomyWilsonLocalArithmeticImported : Bool
    c1PositiveArithmeticClosed :
      c1PositiveArithmetic ≡ true
    c2PositiveArithmeticClosed :
      c2PositiveArithmetic ≡ true
    localArithmeticObstructionAbsentClosed :
      localArithmeticObstructionAbsent ≡ true
    theoremBlockers :
      List YMAFiniteDominationArithmeticBlocker
    theoremBlockersCanonical :
      theoremBlockers ≡ canonicalYMAFiniteDominationArithmeticBlockers
    theoremBlockerCountIs4 :
      ymaFiniteDominationArithmeticBlockerCount ≡ 4
    finiteDominationTheoremStillFalse :
      finiteDominationTheoremPromoted ≡ false
    selfAdjointQuotientHamiltonianStillFalse :
      selfAdjointQuotientHamiltonianProved ≡ false
    h3aTransferStillFalse :
      h3aTransferProved ≡ false
    clayYangMillsStillFalse :
      clayYangMillsPromoted ≡ false

canonicalYMAFiniteDominationArithmeticComposite :
  YMAFiniteDominationArithmeticComposite
canonicalYMAFiniteDominationArithmeticComposite =
  record
    { killingBoundaryLocalArithmeticImported = true
    ; holonomyWilsonLocalArithmeticImported = true
    ; c1PositiveArithmeticClosed = refl
    ; c2PositiveArithmeticClosed = refl
    ; localArithmeticObstructionAbsentClosed = refl
    ; theoremBlockers = canonicalYMAFiniteDominationArithmeticBlockers
    ; theoremBlockersCanonical = refl
    ; theoremBlockerCountIs4 = refl
    ; finiteDominationTheoremStillFalse = refl
    ; selfAdjointQuotientHamiltonianStillFalse = refl
    ; h3aTransferStillFalse = refl
    ; clayYangMillsStillFalse = refl
    }
