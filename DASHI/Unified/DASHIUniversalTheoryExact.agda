module DASHI.Unified.DASHIUniversalTheoryExact where

open import Agda.Primitive using (Level; Setω; lsuc)
open import Agda.Builtin.String using (String)

import DASHI.Interop.PNFHyperfabric369 as Hyperfabric

record DASHIUniversalTheory {ℓ : Level} : Set (lsuc ℓ) where
  field
    State : Set ℓ
    Refinement369 : Set ℓ
    OrientationC3 : Set ℓ
    Symmetry : Set ℓ
    Dynamics : Set ℓ
    Action : Set ℓ
    Observer : Set ℓ
    Scale : Set ℓ
    CausalStructure : Set ℓ

    refinementOf : State → Refinement369
    orientationOf : State → OrientationC3
    evolve : Dynamics → State → State
    actionOf : State → Action
    observe : Observer → State → State
    scaleOf : State → Scale
    causalOf : State → CausalStructure

    hyperfabric369 : Hyperfabric.PNFHyperfabric369Surface
    interpretation : String

open DASHIUniversalTheory public

record UniversalTheorySocket : Setω where
  field
    Theory : Set₁
    candidate369Surface : Hyperfabric.PNFHyperfabric369Surface
    reading : String

canonicalUniversalTheorySocket : UniversalTheorySocket
canonicalUniversalTheorySocket =
  record
    { Theory = DASHIUniversalTheory
    ; candidate369Surface = Hyperfabric.canonicalPNFHyperfabric369Surface
    ; reading =
        "DASHI is encoded as one candidate physical theory. The existing PNF/369 hyperfabric is consumed as the candidate universal refinement/orientation substrate; state, dynamics, action, observer, scale and causal structure remain theorem-facing carriers whose physical identifications are paid by sector realization maps rather than by cardinality or naming."
    }
