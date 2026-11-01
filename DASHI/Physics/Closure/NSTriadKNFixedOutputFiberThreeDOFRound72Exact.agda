module DASHI.Physics.Closure.NSTriadKNFixedOutputFiberThreeDOFRound72Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND72 CONTRIBUTION
--
-- Round71 showed that raw atom cardinality enters the finite-Cauchy
-- concentration lower bound.  The first physical improvement is exact and
-- purely geometric: on one literal output fibre k, a resonant incidence
--
--      p + q = k
--
-- has only ONE free Z^3 input.  Once p and k are fixed, q is fixed.  Thus the
-- relevant geometric code lives in the single cutoff cube, not its Cartesian
-- square.  This is the formal "three lattice degrees of freedom, not six"
-- statement used by the Round72 complexity audit.
--
-- The same module records an exact cubic cutoff majorant.  For N>=1,
--
--   |[-N,N]^3 ∩ Z^3| <= (3N)^3.
--
-- This is only a BASELINE.  Polynomial-in-frequency cardinality is still
-- exponential in shell number j when N=2^j and therefore does not by itself
-- close the Round70 funding contradiction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Integer.Base using (ℤ; _-_)
open import Data.Product.Base using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNOfficialInfinityNormTriangle as Infinity

filterOutputMemberInSource :
  ∀ {output items τ} →
  τ Cube.∈ Output.filterOutput output items →
  τ Cube.∈ items
filterOutputMemberInSource {items = []} ()
filterOutputMemberInSource {output} {items = head ∷ tail} {τ} member
  with Output.modeEqual (Physical.k head) output | member
... | true | Cube.here equality = Cube.here equality
... | true | Cube.there rest = Cube.there (filterOutputMemberInSource rest)
... | false | member = Cube.there (filterOutputMemberInSource member)

physicalOutputFiberMemberInEnumeration :
  ∀ {N output τ} →
  τ Cube.∈ Output.physicalOutputFiber N output →
  τ Cube.∈ Physical.physicalTriadEnumeration N
physicalOutputFiberMemberInEnumeration = filterOutputMemberInSource

fixedOutputInputCutoff :
  ∀ {N output τ} →
  τ Cube.∈ Output.physicalOutputFiber N output →
  (Physical.p τ Cube.∈ Cube.cutoffModes N)
  × (Physical.q τ Cube.∈ Cube.cutoffModes N)
fixedOutputInputCutoff member =
  let bounded = Physical.physicalTriadEnumerationCutoffSound
        (physicalOutputFiberMemberInEnumeration member)
  in Physical.pBounded bounded , Physical.qBounded bounded

qCoordinateFromPK :
  (τ : Physical.PhysicalTriadIncidence) →
  (coordinate : Z3.FourierMode → ℤ) →
  coordinate (Physical.q τ)
  ≡ coordinate (Physical.k τ) - coordinate (Physical.p τ)
qCoordinateFromPK τ coordinate =
  trans
    (sym (Infinity.sumMinusLeft
      (coordinate (Physical.p τ))
      (coordinate (Physical.q τ))))
    (cong
      (λ total → total - coordinate (Physical.p τ))
      (cong coordinate (Physical.resonance τ)))

qDeterminedByPAndOutput :
  (left right : Physical.PhysicalTriadIncidence) →
  Physical.p left ≡ Physical.p right →
  Physical.k left ≡ Physical.k right →
  Physical.q left ≡ Physical.q right
qDeterminedByPAndOutput left right pExact kExact =
  Output.modeExt
    (trans
      (qCoordinateFromPK left Z3.kx)
      (trans
        (cong₂ _-_
          (cong Z3.kx kExact)
          (cong Z3.kx pExact))
        (sym (qCoordinateFromPK right Z3.kx))))
    (trans
      (qCoordinateFromPK left Z3.ky)
      (trans
        (cong₂ _-_
          (cong Z3.ky kExact)
          (cong Z3.ky pExact))
        (sym (qCoordinateFromPK right Z3.ky))))
    (trans
      (qCoordinateFromPK left Z3.kz)
      (trans
        (cong₂ _-_
          (cong Z3.kz kExact)
          (cong Z3.kz pExact))
        (sym (qCoordinateFromPK right Z3.kz))))

fixedOutputPDeterminesQ :
  ∀ {N output left right} →
  left Cube.∈ Output.physicalOutputFiber N output →
  right Cube.∈ Output.physicalOutputFiber N output →
  Physical.p left ≡ Physical.p right →
  Physical.q left ≡ Physical.q right
fixedOutputPDeterminesQ leftMember rightMember pExact =
  qDeterminedByPAndOutput _ _ pExact
    (trans
      (Output.physicalOutputFiberSound leftMember)
      (sym (Output.physicalOutputFiberSound rightMember)))

record FixedOutputThreeDOFCode
    (N : Nat) (output : Z3.FourierMode)
    (τ : Physical.PhysicalTriadIncidence) : Set where
  field
    member : τ Cube.∈ Output.physicalOutputFiber N output
    code : Z3.FourierMode
    codeIsP : code ≡ Physical.p τ
    codeInSingleCutoffCube : code Cube.∈ Cube.cutoffModes N

open FixedOutputThreeDOFCode public

fixedOutputThreeDOFCode :
  ∀ {N output τ} →
  τ Cube.∈ Output.physicalOutputFiber N output →
  FixedOutputThreeDOFCode N output τ
fixedOutputThreeDOFCode {τ = τ} member = record
  { member = member
  ; code = Physical.p τ
  ; codeIsP = refl
  ; codeInSingleCutoffCube = proj₁ (fixedOutputInputCutoff member)
  }

cubeMajorant : Nat → Nat
cubeMajorant N = (3 * N) * ((3 * N) * (3 * N))

cutoffCubeCardinalityCubicBound :
  ∀ N → 1 Cube.≤ᴺ N →
  Cube.cutoffCubeCardinality N Cube.≤ᴺ cubeMajorant N
cutoffCubeCardinalityCubicBound N positive =
  let
    oneD = Cube.intervalCardinalityBound N positive
    square = Cube.≤ᴺ-*-mono oneD oneD
    cube = Cube.≤ᴺ-*-mono oneD square
  in cube

round72FixedOutputHasThreeLatticeDOF : Bool
round72FixedOutputHasThreeLatticeDOF = true

round72CrudeFixedOutputComplexityIsCubicInCutoff : Bool
round72CrudeFixedOutputComplexityIsCubicInCutoff = true

round72SurfaceAreaO2jClaimUsed : Bool
round72SurfaceAreaO2jClaimUsed = false

round72FixedOutputHasThreeLatticeDOFIsTrue :
  round72FixedOutputHasThreeLatticeDOF ≡ true
round72FixedOutputHasThreeLatticeDOFIsTrue = refl

round72SurfaceAreaO2jClaimUsedIsFalse :
  round72SurfaceAreaO2jClaimUsed ≡ false
round72SurfaceAreaO2jClaimUsedIsFalse = refl
