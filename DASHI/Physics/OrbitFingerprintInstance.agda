module DASHI.Physics.OrbitFingerprintInstance where

open import Agda.Builtin.Nat using (Nat)
open import Data.Vec using (Vec)
open import Data.Product using (proj₁; proj₂)

open import DASHI.Physics.IndefiniteMaskQuadratic using (Sign)
open import DASHI.Physics.SignatureFromMask as SFM
open import DASHI.Physics.DimensionBoundAssumptions as DBA
open import DASHI.Physics.OrbitFingerprintAssumptions as OFA

------------------------------------------------------------------------
-- Lift a shell orbit profile into an orbit fingerprint indexed by signature.

fingerprintFromShell :
  ∀ {m : Nat} (σ : Vec Sign m) (sp : DBA.ShellOrbitProfile m) →
  OFA.OrbitFingerprint m (proj₁ (SFM.signature σ)) (proj₂ (SFM.signature σ))
fingerprintFromShell σ sp =
  record
    { orbitCount = DBA.ShellOrbitProfile.orbitCount sp
    ; top1 = DBA.ShellOrbitProfile.top1 sp
    ; top2 = DBA.ShellOrbitProfile.top2 sp
    ; top3 = DBA.ShellOrbitProfile.top3 sp
    }
