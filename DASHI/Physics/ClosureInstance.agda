module DASHI.Physics.ClosureInstance where

open import DASHI.Physics.ClosureGlue as Glue
open import DASHI.Physics.TOperator
open import DASHI.Geometry.RealFiniteSpeed.Core
open import DASHI.Geometry.RealIsotropy.Core
open import Contraction
open import Ultrametric as UMetric
open import DASHI.Combinatorics.Entropy using (Involution)

-- Bundle real (non-toy) closure data.
record RealClosureInstance : Set₁ where
  field
    S   : Set
    U   : UMetric.Ultrametric S
    op  : TOperator S
    sc  : StrictContraction U (TOperator.T op)
    inv : Involution S
    iso : RealIsotropy U (TOperator.T op)
    fs  : RealFiniteSpeed (TOperator.T op)

-- Convert real closure instance into the common ClosureAxioms.
toClosureAxioms : RealClosureInstance → Glue.ClosureAxioms
toClosureAxioms inst =
  record
    { S   = RealClosureInstance.S inst
    ; U   = RealClosureInstance.U inst
    ; T   = TOperator.T (RealClosureInstance.op inst)
    ; sc  = RealClosureInstance.sc inst
    ; inv = RealClosureInstance.inv inst
    ; iso = RealIsotropy.iso (RealClosureInstance.iso inst)
    ; fs  = record
        { local = RealFiniteSpeed.local (RealClosureInstance.fs inst)
        ; preservesLocality = RealFiniteSpeed.preservesLocality (RealClosureInstance.fs inst)
        }
    }

