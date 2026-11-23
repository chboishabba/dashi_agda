module DASHI.Codec.IndexedCubeHyperfibreExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import DASHI.Algebra.Trit using (Trit)
import DASHI.Codec.TriadicMaskSignFactorization as M
import DASHI.Codec.IndexedCubeMaskSignExact as C
import DASHI.Codec.IndexedCubeMaskSignInstanceExact as I
import DASHI.Core.GovernedIndexedResidualCubeExact as Q
import DASHI.Biology.SelfIndexingHyperfabricTetrationExact as H
import DASHI.Reasoning.HistoryTimeIndexedConsumerFibreExact as HT

-- The history/time/version owner remains independent of the codec.
BaseIndex : (s : HT.HistoryTimeConsumerFibreSurface) → Set → Set → Set
BaseIndex s Depth Frob =
  Q.Index (HT.History s) (HT.Time s) Depth Frob (HT.ConsumerVersion s)

VersionAligned : {s : HT.HistoryTimeConsumerFibreSurface}
  {Depth Frob : Set} → BaseIndex s Depth Frob → Set
VersionAligned {s} k =
  Q.Index.version k ≡ HT.consumerVersionAt s
    (Q.Index.history k) (Q.Index.time k)

-- Typed vertices of the existing literal cube.
data Vertex : Set where
  a b c d e f h i : Vertex

State : Vertex → Set
State a = Q.A I.codecCube
State b = Q.B I.codecCube
State c = Q.C I.codecCube
State d = Q.D I.codecCube
State e = Q.E I.codecCube
State f = Q.F I.codecCube
State h = Q.H I.codecCube
State i = Q.I I.codecCube

data Edge : Vertex → Vertex → Set where
  ab : Edge a b
  cd : Edge c d
  ef : Edge e f
  hi : Edge h i
  ac : Edge a c
  bd : Edge b d
  eh : Edge e h
  fi : Edge f i
  ae : Edge a e
  bf : Edge b f
  ch : Edge c h
  di : Edge d i

move : ∀ {u v} → Edge u v → State u → State v
move ab = Q.x00 I.codecCube
move cd = Q.x10 I.codecCube
move ef = Q.x01 I.codecCube
move hi = Q.x11 I.codecCube
move ac = Q.y00 I.codecCube
move bd = Q.y10 I.codecCube
move eh = Q.y01 I.codecCube
move fi = Q.y11 I.codecCube
move ae = Q.z00 I.codecCube
move bf = Q.z10 I.codecCube
move ch = Q.z01 I.codecCube
move di = Q.z11 I.codecCube

data Path : Vertex → Vertex → Set where
  done : ∀ {u} → Path u u
  next : ∀ {u v w} → Edge u v → Path v w → Path u w

walk : ∀ {u v} → Path u v → State u → State v
walk done x = x
walk (next edge rest) x = walk rest (move edge x)

-- Residual is the actual final triple, not merely a defect flag.
Residual : Vertex → Set
Residual a = M.Triple Trit
Residual b = M.Triple Trit
Residual c = M.Triple Trit
Residual d = M.Triple Trit
Residual e = M.Triple M.FactorizedTrit
Residual f = M.Triple M.FactorizedTrit
Residual h = M.Triple M.FactorizedTrit
Residual i = M.Triple M.FactorizedTrit

suffixAt : (v : Vertex) → State v → Residual v
suffixAt a = C.residualBlock
suffixAt b = C.suffix
suffixAt c = C.residualBlock
suffixAt d = C.suffix
suffixAt e = C.residualBlock
suffixAt f = C.suffix
suffixAt h = C.residualBlock
suffixAt i = C.suffix

resolution : Vertex → H.FabricResolution
resolution a = H.resolution9
resolution b = H.resolution6
resolution c = H.resolution9
resolution d = H.resolution6
resolution e = H.resolution9
resolution f = H.resolution6
resolution h = H.resolution9
resolution i = H.resolution6

codecHyperfibre : H.Hyperfibre State
codecHyperfibre = H.hyperfibre Residual Path walk
  (λ {source} {target} p x → suffixAt target (walk p x)) resolution

xyzPath : Path a i
xyzPath = next ab (next bd (next di done))

zyxPath : Path a i
zyxPath = next ae (next eh (next hi done))

walkAgrees : (x : State a) → walk xyzPath x ≡ walk zyxPath x
walkAgrees = I.allPathsExample

residualAgrees : (x : State a) →
  suffixAt i (walk xyzPath x) ≡ suffixAt i (walk zyxPath x)
residualAgrees x = Q.cong (suffixAt i) (walkAgrees x)

reopenTerminal : (x : State a) →
  C.decode (C.join (walk xyzPath x)) ≡ C.rotate x
reopenTerminal = I.terminalReopen

-- Each index has the same certified local diagram here.
-- Cross-index time evolution/refinement is deliberately not inferred.
indexedLocalFibre : {s : HT.HistoryTimeConsumerFibreSurface}
  {Depth Frob : Set} → (k : BaseIndex s Depth Frob) →
  VersionAligned k → H.Hyperfibre State
indexedLocalFibre k aligned = codecHyperfibre
