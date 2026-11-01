module DASHI.Physics.Closure.CanonicalConstraintClosureWitness where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.Constraints.Bracket using (LieLike)
open import DASHI.Physics.Constraints.Closure using (ClosureLaw)
open import DASHI.Physics.Constraints.ConcreteInstance as CI
open import DASHI.Physics.Closure.ConstraintClosureFromCanonicalPathTheorem as CCFCPT

record CanonicalConstraintClosureWitness : Setω where
  field
    crcpCloses : LieLike._[_,]_ CI.L CI.CR CI.CP ≡ CI.CC
    cpccCloses : LieLike._[_,]_ CI.L CI.CP CI.CC ≡ CI.CR
    crccCloses : LieLike._[_,]_ CI.L CI.CR CI.CC ≡ CI.CP
    closureWitness : ClosureLaw CI.CS CI.L

canonicalConstraintClosureWitness : CanonicalConstraintClosureWitness
canonicalConstraintClosureWitness =
  record
    { crcpCloses = refl
    ; cpccCloses = refl
    ; crccCloses = refl
    ; closureWitness = CCFCPT.canonicalPathInducedConstraintClosure
    }
