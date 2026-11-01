module DASHI.Physics.UnifiedClosure where

import DASHI.Physics.ClosureGlue as Glue
open import DASHI.Physics.ClosureBuilder as CB
open import DASHI.Physics.ContractionQuadraticBridge as CQ
open import DASHI.Physics.SignatureClassificationBridge as SC
open import DASHI.Physics.CliffordEvenLiftBridge as CE

closure : (stk : CB.RealStack) → Glue.ClosureAxioms
closure = CB.buildClosure

record PhysicsUnification (stk : CB.RealStack) : Set₂ where
  field
    cq   : CQ.Contraction⇒Quadratic (CB.U stk) (CB.T stk)
    sym  : SC.SymmetryPackage (CB.U stk) (CB.T stk)
    qs   : SC.Quadratic⇒Signature
    q2cl : CE.Quadratic⇒Clifford
    wl   : CE.WaveLift⇒Even
