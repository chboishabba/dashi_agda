module DASHI.Algebra.DeltaHeckeEigenMotif where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_+_)

open import MonsterOntos using
  (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71)
open import DASHI.Algebra.PhysicsSignature using (Sig15; sig15)
open import DASHI.Algebra.PhysicsSignature as PS

-- Flow compatibility is evaluated on a transition, not an absolute state.
record DeltaHeckeLens (X : Set) : Set₁ where
  field
    CompatΔ : SSP → X → X → Bool

open DeltaHeckeLens public

scanΔ : ∀ {X} → DeltaHeckeLens X → X → X → Sig15
scanΔ L before after = sig15
  (CompatΔ L p2 before after)  (CompatΔ L p3 before after)
  (CompatΔ L p5 before after)  (CompatΔ L p7 before after)
  (CompatΔ L p11 before after) (CompatΔ L p13 before after)
  (CompatΔ L p17 before after) (CompatΔ L p19 before after)
  (CompatΔ L p23 before after) (CompatΔ L p29 before after)
  (CompatΔ L p31 before after) (CompatΔ L p41 before after)
  (CompatΔ L p47 before after) (CompatΔ L p59 before after)
  (CompatΔ L p71 before after)

bit : Bool → Nat
bit false = zero
bit true  = suc zero

record Eigen3 : Set where
  constructor eigen3
  field
    earth spoke hub : Nat

open Eigen3 public

-- A fixed, auditable partition of the 15 prime lanes.  It is deliberately
-- structural: no lexical or hash prior participates in the eigen readout.
eigenOf : Sig15 → Eigen3
eigenOf s = eigen3
  (bit (PS.Sig15.b2 s) + bit (PS.Sig15.b3 s) + bit (PS.Sig15.b5 s) +
   bit (PS.Sig15.b7 s) + bit (PS.Sig15.b11 s))
  (bit (PS.Sig15.b13 s) + bit (PS.Sig15.b17 s) + bit (PS.Sig15.b19 s) +
   bit (PS.Sig15.b23 s) + bit (PS.Sig15.b29 s))
  (bit (PS.Sig15.b31 s) + bit (PS.Sig15.b41 s) + bit (PS.Sig15.b47 s) +
   bit (PS.Sig15.b59 s) + bit (PS.Sig15.b71 s))

eigenMass : Eigen3 → Nat
eigenMass e = earth e + spoke e + hub e

data Motif : Set where
  M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 : Motif

-- Sparse flow support is treated conservatively; broad support is admitted.
-- M10 remains an explicit overflow constructor for a parent-voxel classifier.
classifyMotif : Eigen3 → Motif
classifyMotif e with eigenMass e
... | zero = M9
... | suc zero = M8
... | suc (suc zero) = M7
... | suc (suc (suc zero)) = M6
... | suc (suc (suc (suc zero))) = M5
... | suc (suc (suc (suc (suc zero)))) = M4
... | suc (suc (suc (suc (suc (suc zero))))) = M3
... | suc (suc (suc (suc (suc (suc (suc zero)))))) = M2
... | suc (suc (suc (suc (suc (suc (suc (suc zero))))))) = M1
... | suc (suc (suc (suc (suc (suc (suc (suc (suc n)))))))) = M1

record DeltaHeckeResult : Set where
  constructor deltaHeckeResult
  field
    signature : Sig15
    eigen     : Eigen3
    motif     : Motif

runDeltaHecke : ∀ {X} → DeltaHeckeLens X → X → X → DeltaHeckeResult
runDeltaHecke L before after =
  let s = scanΔ L before after
      e = eigenOf s
  in deltaHeckeResult s e (classifyMotif e)
