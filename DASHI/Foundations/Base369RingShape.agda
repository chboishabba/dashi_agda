module DASHI.Foundations.Base369RingShape where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Small builtin-only algebra surface for Base369 finite modular carriers.
--
-- This module is intentionally parametric: TriTruth, HexTruth, NonaryTruth,
-- or any later Base369 carrier can supply its own constructors, finite
-- representatives, and modular operations without expanding the ring laws
-- into thousands of handwritten cases at every use site.

record FiniteCarrierShape
  {ℓc ℓr : Level}
  (Carrier : Set ℓc) :
  Set (lsuc (ℓc ⊔ ℓr)) where
  field
    Representative :
      Set ℓr

    representativeCount :
      Nat

    representativeIndex :
      Representative →
      Nat

    fromRepresentative :
      Representative →
      Carrier

    toRepresentative :
      Carrier →
      Representative

    representativeValid? :
      Representative →
      Bool

    representativeValid :
      (r : Representative) →
      representativeValid? r ≡ true

    from-to-representative :
      (x : Carrier) →
      fromRepresentative (toRepresentative x) ≡ x

    to-from-representative :
      (r : Representative) →
      toRepresentative (fromRepresentative r) ≡ r

open FiniteCarrierShape public

record ModularRingOperationShape
  {ℓ : Level}
  (Carrier : Set ℓ) :
  Set ℓ where
  field
    zero :
      Carrier

    one :
      Carrier

    _+_ :
      Carrier →
      Carrier →
      Carrier

    _*_ :
      Carrier →
      Carrier →
      Carrier

    -_ :
      Carrier →
      Carrier

    _==_ :
      Carrier →
      Carrier →
      Bool

    nonzero? :
      Carrier →
      Bool

open ModularRingOperationShape public

record CommutativeRingLawShape
  {ℓ : Level}
  {Carrier : Set ℓ}
  (Ops : ModularRingOperationShape Carrier) :
  Set ℓ where
  open ModularRingOperationShape Ops
    renaming
      ( zero to ringZero
      ; one to ringOne
      ; _+_ to add
      ; _*_ to mul
      ; -_ to neg
      )

  field
    addComm :
      (x y : Carrier) →
      add x y ≡ add y x

    addAssoc :
      (x y z : Carrier) →
      add (add x y) z ≡ add x (add y z)

    addZero :
      (x : Carrier) →
      add ringZero x ≡ x

    addInv :
      (x : Carrier) →
      add (neg x) x ≡ ringZero

    mulComm :
      (x y : Carrier) →
      mul x y ≡ mul y x

    mulAssoc :
      (x y z : Carrier) →
      mul (mul x y) z ≡ mul x (mul y z)

    mulZeroL :
      (x : Carrier) →
      mul ringZero x ≡ ringZero

    mulZeroR :
      (x : Carrier) →
      mul x ringZero ≡ ringZero

    mulOneL :
      (x : Carrier) →
      mul ringOne x ≡ x

    mulOneR :
      (x : Carrier) →
      mul x ringOne ≡ x

    distribL :
      (x y z : Carrier) →
      mul x (add y z) ≡ add (mul x y) (mul x z)

    distribR :
      (x y z : Carrier) →
      mul (add x y) z ≡ add (mul x z) (mul y z)

open CommutativeRingLawShape public

record RingWitness
  {ℓc ℓr : Level}
  (Carrier : Set ℓc) :
  Set (lsuc (ℓc ⊔ ℓr)) where
  field
    finiteCarrier :
      FiniteCarrierShape {ℓc} {ℓr} Carrier

    operations :
      ModularRingOperationShape Carrier

    laws :
      CommutativeRingLawShape operations

open RingWitness public

record FieldWitness
  {ℓc ℓr : Level}
  {Carrier : Set ℓc}
  (Ring : RingWitness {ℓc} {ℓr} Carrier) :
  Set (ℓc ⊔ ℓr) where
  open RingWitness Ring
    renaming
      ( finiteCarrier to ringFiniteCarrier
      ; operations to ringOperations
      ; laws to ringLaws
      )
  open ModularRingOperationShape ringOperations
    renaming
      ( one to ringOne
      ; _*_ to mul
      ; nonzero? to isNonzero?
      )
  open FiniteCarrierShape ringFiniteCarrier
    renaming
      ( Representative to Rep
      ; fromRepresentative to fromRep
      )

  field
    oneNonzero :
      isNonzero? ringOne ≡ true

    inverseRepresentative :
      (r : Rep) →
      isNonzero? (fromRep r) ≡ true →
      Rep

    inverseNonzero :
      (r : Rep) →
      (nz : isNonzero? (fromRep r) ≡ true) →
      isNonzero? (fromRep (inverseRepresentative r nz)) ≡ true

    inverseLeft :
      (r : Rep) →
      (nz : isNonzero? (fromRep r) ≡ true) →
      mul
      (fromRep (inverseRepresentative r nz))
      (fromRep r)
      ≡
      ringOne

    inverseRight :
      (r : Rep) →
      (nz : isNonzero? (fromRep r) ≡ true) →
      mul
      (fromRep r)
      (fromRep (inverseRepresentative r nz))
      ≡
      ringOne

open FieldWitness public

record Base369ModularRingShape
  {ℓc ℓr : Level} :
  Set (lsuc (ℓc ⊔ ℓr)) where
  field
    Carrier :
      Set ℓc

    ringWitness :
      RingWitness {ℓc} {ℓr} Carrier

    fieldWitness? :
      Bool

    fieldWitness :
      fieldWitness? ≡ true →
      FieldWitness ringWitness

open Base369ModularRingShape public
