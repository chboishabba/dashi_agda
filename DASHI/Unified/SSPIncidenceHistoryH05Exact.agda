module DASHI.Unified.SSPIncidenceHistoryH05Exact where

-- Source-written attachment to the EXISTING H05 owner.
-- Griess/Sah source wheel; Singer difference offsets; Conway FRACTRAN.
-- JMD SSP/path provenance remains in the upstream incidence checker.
-- Exact finite external checker: check_ssp_incidence_h05_20261125.py.
-- NO kernel acceptance claimed. New periodic EV5 program, not FractranCOL.step.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_; _++_)
import Data.Vec as V
import DASHI.Combinatorics.FractranCOL as FC
import DASHI.Core.GovernedIndexedResidualCubeExact as Q
import DASHI.Core.GovernedDiagramCore as Diagram

data Wheel : Set where
  w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : Wheel

next prev : Wheel → Wheel
next w0 = w1
next w1 = w2
next w2 = w3
next w3 = w4
next w4 = w5
next w5 = w6
next w6 = w7
next w7 = w8
next w8 = w9
next w9 = w10
next w10 = w11
next w11 = w12
next w12 = w0
prev w0 = w12
prev w1 = w0
prev w2 = w1
prev w3 = w2
prev w4 = w3
prev w5 = w4
prev w6 = w5
prev w7 = w6
prev w8 = w7
prev w9 = w8
prev w10 = w9
prev w11 = w10
prev w12 = w11

position : Wheel → Nat
position w0 = 0
position w1 = 1
position w2 = 2
position w3 = 3
position w4 = 4
position w5 = 5
position w6 = 6
position w7 = 7
position w8 = 8
position w9 = 9
position w10 = 10
position w11 = 11
position w12 = 12

complement : Wheel → Nat
complement w0 = 12
complement w1 = 11
complement w2 = 10
complement w3 = 9
complement w4 = 8
complement w5 = 7
complement w6 = 6
complement w7 = 5
complement w8 = 4
complement w9 = 3
complement w10 = 2
complement w11 = 1
complement w12 = 0

data Spoke : Set where
  d0 d6 d10 d11 : Spoke

offset : Spoke → Nat
offset d0 = 0
offset d6 = 6
offset d10 = 10
offset d11 = 11

other : Bool → Bool
other false = true
other true = false

iterate : Nat → (Wheel → Wheel) → Wheel → Wheel
iterate zero f w = w
iterate (suc k) f w = f (iterate k f w)

-- false = primal; true = dual. Opposite directions are not conflated.
out : Bool → Wheel → Spoke → Wheel
out false i d = iterate (offset d) prev i
out true i d = iterate (offset d) next i

data Source : Set where
  origin : Source
  route : Bool → Wheel → Spoke → Spoke → Source

transport : Source → Source
transport origin = origin
transport (route b i d e) = route b (next i) d e

Geometry : Set
Geometry = Maybe (Wheel × (Wheel × Wheel))

geometry : Source → Geometry
geometry origin = nothing
geometry (route b i d e) =
  just (i , (out b i d , out (other b) (out b i d) e))

data Command : Set where
  forward backward primalToDual dualToPrimal : Command

repeat : Nat → Command → List Command
repeat zero c = []
repeat (suc n) c = c ∷ repeat n c

-- Selected shortest wheel macro, separately from geometric out.
macro : Bool → Spoke → List Command
macro false d0 = primalToDual ∷ []
macro false d6 = repeat 6 backward ++ (primalToDual ∷ [])
macro false d10 = repeat 3 forward ++ (primalToDual ∷ [])
macro false d11 = repeat 2 forward ++ (primalToDual ∷ [])
macro true d0 = dualToPrimal ∷ []
macro true d6 = repeat 6 forward ++ (dualToPrimal ∷ [])
macro true d10 = repeat 3 backward ++ (dualToPrimal ∷ [])
macro true d11 = repeat 2 backward ++ (dualToPrimal ∷ [])

commands : Source → List Command
commands origin = []
commands (route b i d e) = macro b d ++ macro (other b) e

-- Reuse actual EV5 alphabet [2,3,5,7,11].
ev : Nat → Nat → Nat → Nat → Nat → FC.EV5
ev a b c d e = a V.∷ b V.∷ c V.∷ d V.∷ e V.∷ V.[]

initial : Source → FC.EV5
initial origin = ev 0 0 0 0 0
initial (route false i d e) = ev (position i) (complement i) 1 0 0
initial (route true i d e) = ev (position i) (complement i) 0 1 0

-- Exact first-enabled semantics on the valid 12-exponent wheel subset.
-- Outside the subset this is deliberately not a generic FRACTRAN evaluator.
step : Command → FC.EV5 → Maybe FC.EV5
step forward (a V.∷ suc b V.∷ c V.∷ d V.∷ e V.∷ V.[]) =
  just (ev (suc a) b c d e)
step forward (12 V.∷ zero V.∷ c V.∷ d V.∷ e V.∷ V.[]) =
  just (ev 0 12 c d e)
step forward _ = nothing
step backward (suc a V.∷ b V.∷ c V.∷ d V.∷ e V.∷ V.[]) =
  just (ev a (suc b) c d e)
step backward (zero V.∷ 12 V.∷ c V.∷ d V.∷ e V.∷ V.[]) =
  just (ev 12 0 c d e)
step backward _ = nothing
step primalToDual (a V.∷ b V.∷ suc c V.∷ d V.∷ e V.∷ V.[]) =
  just (ev a b c (suc d) e)
step primalToDual _ = nothing
step dualToPrimal (a V.∷ b V.∷ c V.∷ suc d V.∷ e V.∷ V.[]) =
  just (ev a b (suc c) d e)
step dualToPrimal _ = nothing

prepend : FC.EV5 → Maybe (List FC.EV5) → Maybe (List FC.EV5)
prepend v nothing = nothing
prepend v (just vs) = just (v ∷ vs)

runTrace : List Command → FC.EV5 → Maybe (List FC.EV5)
runTrace [] v = just (v ∷ [])
runTrace (c ∷ cs) v with step c v
... | nothing = nothing
... | just w = prepend v (runTrace cs w)

Arithmetic : Set
Arithmetic = List Command × Maybe (List FC.EV5)

arithmetic : Source → Arithmetic
arithmetic s = commands s , runTrace (commands s) (initial s)

-- Independent metadata, not a synonym for a wheel coordinate.
K : Set
K = Q.Index Nat Nat Nat Nat Nat

Raw Geo Arith Both : Set
Raw = K × Source
Geo = Raw × Geometry
Arith = Raw × Arithmetic
Both = Raw × (Geometry × Arithmetic)

toGeo : Raw → Geo
toGeo (k , s) = (k , s) , geometry s

toArith : Raw → Arith
toArith (k , s) = (k , s) , arithmetic s

finishGeo : Geo → Both
finishGeo ((k , s) , g) = (k , s) , (g , arithmetic s)

finishArith : Arith → Both
finishArith ((k , s) , a) = (k , s) , (geometry s , a)

moveRaw : Raw → Raw
moveRaw (k , s) = k , transport s

moveGeo : Geo → Geo
moveGeo (raw , _) = toGeo (moveRaw raw)

moveArith : Arith → Arith
moveArith (raw , _) = toArith (moveRaw raw)

moveBoth : Both → Both
moveBoth (raw , _) = finishGeo (toGeo (moveRaw raw))

-- Nonidentity z re-evaluates the actual state-dependent execution.
nativeCube : Q.Cube
nativeCube = record
  { A = Raw ; B = Geo ; C = Arith ; D = Both
  ; E = Raw ; F = Geo ; H = Arith ; I = Both
  ; x00 = toGeo ; x10 = finishArith
  ; x01 = toGeo ; x11 = finishArith
  ; y00 = toArith ; y10 = finishGeo
  ; y01 = toArith ; y11 = finishGeo
  ; z00 = moveRaw ; z10 = moveGeo
  ; z01 = moveArith ; z11 = moveBoth
  }

-- Retained source history, not an assertion that residual proves equality.
nativeFaces : Q.Faces nativeCube
nativeFaces = record
  { Rxy0 = λ _ → Source ; Rxz0 = λ _ → Source ; Ryz0 = λ _ → Source
  ; Rxy1 = λ _ → Source ; Rxz1 = λ _ → Source ; Ryz1 = λ _ → Source
  }

nativeExactFaces : Q.ExactFaces nativeCube nativeFaces
nativeExactFaces = record
  { pxy0 = Diagram.commutingSquareWitness (λ { (k , s) → refl })
  ; pxz0 = Diagram.commutingSquareWitness (λ { (k , s) → refl })
  ; pyz0 = Diagram.commutingSquareWitness (λ { (k , s) → refl })
  ; pxy1 = Diagram.commutingSquareWitness (λ { (k , s) → refl })
  ; pxz1 = Diagram.commutingSquareWitness (λ { ((k , s) , a) → refl })
  ; pyz1 = Diagram.commutingSquareWitness (λ { ((k , s) , g) → refl })
  }

nativeResidualFaces : Q.ResidualFaces nativeCube nativeFaces
nativeResidualFaces = record
  { rxy0 = Diagram.residualSquareWitness (λ { (k , s) → s })
  ; rxz0 = Diagram.residualSquareWitness (λ { (k , s) → s })
  ; ryz0 = Diagram.residualSquareWitness (λ { (k , s) → s })
  ; rxy1 = Diagram.residualSquareWitness (λ { (k , s) → s })
  ; rxz1 = Diagram.residualSquareWitness (λ { ((k , s) , a) → s })
  ; ryz1 = Diagram.residualSquareWitness (λ { ((k , s) , g) → s })
  }

nativeIndexed : Q.IndexedCube K
nativeIndexed = record
  { cubeAt = λ _ → nativeCube
  ; facesAt = λ _ → nativeFaces
  ; residualAt = λ _ → nativeResidualFaces
  }

sixPathAgreement : (s : Raw) → Q.xyz nativeCube s ≡ Q.zyx nativeCube s
sixPathAgreement = Q.xyz-zyx nativeExactFaces

recover : Both → Raw
recover (raw , _) = raw

recoverAfterJoin : (s : Raw) → recover (finishGeo (toGeo s)) ≡ s
recoverAfterJoin (k , s) = refl

recoverAfterMove : (s : Raw) → recover (moveBoth (finishGeo (toGeo s))) ≡ moveRaw s
recoverAfterMove (k , s) = refl

exampleMove : transport (route false w0 d6 d10) ≡ route false w1 d6 d10
exampleMove = refl

-- Local checker separately evaluates geometry/execution agreement, actual
-- first-enabled fractions, conditional 2-bit residual and signed SSP deltas.
-- This Agda chart retains full source + trace, not the minimal codec theorem.
-- No kernel receipt, generic FRACTRAN compilation, analytic J, Monster group
-- action, physical interpretation, H07 closure or ESD modifications.
