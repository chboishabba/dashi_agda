module DASHI.Physics.Closure.CanonicalConstraintClosureTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintClosureWitness as CCCW
open import DASHI.Physics.Constraints.Bracket using (LieLike)
open import DASHI.Physics.Constraints.ConcreteInstance as CI

record CanonicalConstraintClosureTheorem : Setω where
  field
    crcp↦cc : LieLike._[_,]_ CI.L CI.CR CI.CP ≡ CI.CC
    cpcc↦cr : LieLike._[_,]_ CI.L CI.CP CI.CC ≡ CI.CR
    crcc↦cp : LieLike._[_,]_ CI.L CI.CR CI.CC ≡ CI.CP

canonicalConstraintClosureTheorem : CanonicalConstraintClosureTheorem
canonicalConstraintClosureTheorem =
  record
    { crcp↦cc = CCCW.CanonicalConstraintClosureWitness.crcpCloses
        CCCW.canonicalConstraintClosureWitness
    ; cpcc↦cr = CCCW.CanonicalConstraintClosureWitness.cpccCloses
        CCCW.canonicalConstraintClosureWitness
    ; crcc↦cp = CCCW.CanonicalConstraintClosureWitness.crccCloses
        CCCW.canonicalConstraintClosureWitness
    }
