module DASHI.Physics.Closure.NSTriadKNPhysicalTriadicSubfibreComplexityByClassRound72Exact where

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
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND72 CONTRIBUTION
--
-- Do not assign one generic cardinality to all four triadic classes.
-- For a literal LH incidence the low leg is p; for HL it is q.  The ceil-log
-- shell convention gives
--
--      ||low||_infinity <= 2^(shellIndex low),
--
-- so the low leg lies in the exact cutoff cube of radius 2^ell.  At fixed
-- output, that low leg determines the other input by resonance.  Hence LH/HL
-- effective raw complexity is coded by ONE dyadic low-leg cube, not by the
-- high/output shell cube.
--
-- Combining this with the exact cutoff-cube cardinality theorem gives the
-- fully constructed cubic majorant (3*2^ell)^3.  HH/CC deliberately remain
-- unresolved by the low-leg argument: those classes need dominant-hat/Gram/
-- energy structure rather than a fictitious low coordinate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (ℤ; +_; -[1+_]; _-_; ∣_∣)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as Nat
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNOfficialInfinityNormTriangle as Infinity
import DASHI.Physics.Closure.NSTriadKNCeilLogShellBounds as Bounds
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicConsequencesClosed as Dyadic
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support
import DASHI.Physics.Closure.NSTriadKNFixedOutputFiberThreeDOFRound72Exact as ThreeDOF

integerMagnitudeIsAbs : ∀ z → Cube.integerMagnitude z ≡ ∣ z ∣
integerMagnitudeIsAbs (+ n) = refl
integerMagnitudeIsAbs (-[1+ n ]) = refl

standardLeToCubeLe : ∀ {m n} → m ≤ n → m Cube.≤ᴺ n
standardLeToCubeLe z≤n = Cube.z≤n
standardLeToCubeLe (s≤s proof) = Cube.s≤s (standardLeToCubeLe proof)

infinityNormBoundGivesCutoff :
  ∀ {N mode} →
  Infinity.infinityNorm mode ≤ N →
  Cube.InCutoffCube N mode
infinityNormBoundGivesCutoff {N} {mode} normBound =
  Cube.cutoff-membership
    (Cube.intervalComplete
      (standardLeToCubeLe
        (subst
          (λ magnitude → magnitude ≤ N)
          (sym (integerMagnitudeIsAbs (Z3.kx mode)))
          (Nat.≤-trans
            (Infinity.xMagnitude≤InfinityNorm mode) normBound))))
    (Cube.intervalComplete
      (standardLeToCubeLe
        (subst
          (λ magnitude → magnitude ≤ N)
          (sym (integerMagnitudeIsAbs (Z3.ky mode)))
          (Nat.≤-trans
            (Infinity.yMagnitude≤InfinityNorm mode) normBound))))
    (Cube.intervalComplete
      (standardLeToCubeLe
        (subst
          (λ magnitude → magnitude ≤ N)
          (sym (integerMagnitudeIsAbs (Z3.kz mode)))
          (Nat.≤-trans
            (Infinity.zMagnitude≤InfinityNorm mode) normBound))))

modeInOwnDyadicShellCube :
  ∀ mode →
  mode Cube.∈ Cube.cutoffModes (Shell.pow2 (Shell.shellIndex mode))
modeInOwnDyadicShellCube mode =
  Cube.cutoffModeEnumerationComplete
    (Shell.pow2 (Shell.shellIndex mode)) mode
    (infinityNormBoundGivesCutoff
      (Bounds.ceilLogShellUpperMagnitude (Infinity.infinityNorm mode)))

pCoordinateFromQK :
  (τ : Physical.PhysicalTriadIncidence) →
  (coordinate : Z3.FourierMode → ℤ) →
  coordinate (Physical.p τ)
  ≡ coordinate (Physical.k τ) - coordinate (Physical.q τ)
pCoordinateFromQK τ coordinate =
  trans
    (sym (Infinity.sumMinusLeft
      (coordinate (Physical.q τ))
      (coordinate (Physical.p τ))))
    (cong
      (λ total → total - coordinate (Physical.q τ))
      (trans
        (cong coordinate
          (Infinity.addModeCommutative (Physical.q τ) (Physical.p τ)))
        (cong coordinate (Physical.resonance τ))))

pDeterminedByQAndOutput :
  (left right : Physical.PhysicalTriadIncidence) →
  Physical.q left ≡ Physical.q right →
  Physical.k left ≡ Physical.k right →
  Physical.p left ≡ Physical.p right
pDeterminedByQAndOutput left right qExact kExact =
  Output.modeExt
    (trans
      (pCoordinateFromQK left Z3.kx)
      (trans
        (cong₂ _-_ (cong Z3.kx kExact) (cong Z3.kx qExact))
        (sym (pCoordinateFromQK right Z3.kx))))
    (trans
      (pCoordinateFromQK left Z3.ky)
      (trans
        (cong₂ _-_ (cong Z3.ky kExact) (cong Z3.ky qExact))
        (sym (pCoordinateFromQK right Z3.ky))))
    (trans
      (pCoordinateFromQK left Z3.kz)
      (trans
        (cong₂ _-_ (cong Z3.kz kExact) (cong Z3.kz qExact))
        (sym (pCoordinateFromQK right Z3.kz))))

record LHFixedOutputLowLegCode
    (N : Nat) (output : Z3.FourierMode)
    (classified : Support.ClassifiedPhysicalTriad) : Set where
  field
    classIsLH : Support.sourceClass classified ≡ Support.LH
    fibreMember :
      Support.incidence classified Cube.∈ Output.physicalOutputFiber N output
    lowLeg : Z3.FourierMode
    lowLegIsP : lowLeg ≡ Physical.p (Support.incidence classified)
    lowLegInOwnDyadicCube :
      lowLeg Cube.∈ Cube.cutoffModes (Shell.pow2 (Shell.shellIndex lowLeg))

open LHFixedOutputLowLegCode public

lhFixedOutputLowLegCode :
  ∀ {N output classified} →
  Support.sourceClass classified ≡ Support.LH →
  Support.incidence classified Cube.∈ Output.physicalOutputFiber N output →
  LHFixedOutputLowLegCode N output classified
lhFixedOutputLowLegCode {classified = classified} classProof member = record
  { classIsLH = classProof
  ; fibreMember = member
  ; lowLeg = Physical.p (Support.incidence classified)
  ; lowLegIsP = refl
  ; lowLegInOwnDyadicCube =
      modeInOwnDyadicShellCube (Physical.p (Support.incidence classified))
  }

record HLFixedOutputLowLegCode
    (N : Nat) (output : Z3.FourierMode)
    (classified : Support.ClassifiedPhysicalTriad) : Set where
  field
    classIsHL : Support.sourceClass classified ≡ Support.HL
    fibreMember :
      Support.incidence classified Cube.∈ Output.physicalOutputFiber N output
    lowLeg : Z3.FourierMode
    lowLegIsQ : lowLeg ≡ Physical.q (Support.incidence classified)
    lowLegInOwnDyadicCube :
      lowLeg Cube.∈ Cube.cutoffModes (Shell.pow2 (Shell.shellIndex lowLeg))

open HLFixedOutputLowLegCode public

hlFixedOutputLowLegCode :
  ∀ {N output classified} →
  Support.sourceClass classified ≡ Support.HL →
  Support.incidence classified Cube.∈ Output.physicalOutputFiber N output →
  HLFixedOutputLowLegCode N output classified
hlFixedOutputLowLegCode {classified = classified} classProof member = record
  { classIsHL = classProof
  ; fibreMember = member
  ; lowLeg = Physical.q (Support.incidence classified)
  ; lowLegIsQ = refl
  ; lowLegInOwnDyadicCube =
      modeInOwnDyadicShellCube (Physical.q (Support.incidence classified))
  }

fixedOutputLHPLegDeterminesTriadGeometry :
  ∀ {N output left right} →
  Support.incidence left Cube.∈ Output.physicalOutputFiber N output →
  Support.incidence right Cube.∈ Output.physicalOutputFiber N output →
  Physical.p (Support.incidence left) ≡ Physical.p (Support.incidence right) →
  Physical.q (Support.incidence left) ≡ Physical.q (Support.incidence right)
fixedOutputLHPLegDeterminesTriadGeometry = ThreeDOF.fixedOutputPDeterminesQ

fixedOutputHLQLegDeterminesTriadGeometry :
  ∀ {N output left right} →
  Support.incidence left Cube.∈ Output.physicalOutputFiber N output →
  Support.incidence right Cube.∈ Output.physicalOutputFiber N output →
  Physical.q (Support.incidence left) ≡ Physical.q (Support.incidence right) →
  Physical.p (Support.incidence left) ≡ Physical.p (Support.incidence right)
fixedOutputHLQLegDeterminesTriadGeometry leftMember rightMember qExact =
  pDeterminedByQAndOutput _ _ qExact
    (trans
      (Output.physicalOutputFiberSound leftMember)
      (sym (Output.physicalOutputFiberSound rightMember)))

oneCubeLePow2 : ∀ ell → 1 Cube.≤ᴺ Shell.pow2 ell
oneCubeLePow2 zero = Cube.≤ᴺ-refl 1
oneCubeLePow2 (suc ell) =
  let
    old = Shell.pow2 ell
    oldPositive = oneCubeLePow2 ell
    oldBelowDouble : old Cube.≤ᴺ old + old
    oldBelowDouble =
      Cube.≤ᴺ-+-right old (Cube.≤ᴺ-refl old)
    oneBelowDouble : 1 Cube.≤ᴺ old + old
    oneBelowDouble = Cube.≤ᴺ-trans oldPositive oldBelowDouble
  in
  Cube.≤ᴺ-substRight (Dyadic.doublePow2 ell) oneBelowDouble

lowLegCubeMajorant : Nat → Nat
lowLegCubeMajorant ell = ThreeDOF.cubeMajorant (Shell.pow2 ell)

lowLegComplexityCubicBound :
  ∀ ell →
  Cube.cutoffCubeCardinality (Shell.pow2 ell)
    Cube.≤ᴺ lowLegCubeMajorant ell
lowLegComplexityCubicBound ell =
  ThreeDOF.cutoffCubeCardinalityCubicBound
    (Shell.pow2 ell) (oneCubeLePow2 ell)

round72LHComplexityUsesLowLegShell : Bool
round72LHComplexityUsesLowLegShell = true

round72HLComplexityUsesLowLegShell : Bool
round72HLComplexityUsesLowLegShell = true

round72LowLegCubicCardinalityMajorantConstructed : Bool
round72LowLegCubicCardinalityMajorantConstructed = true

round72HHRawCountingClosedByLowLegArgument : Bool
round72HHRawCountingClosedByLowLegArgument = false

round72CCRawCountingClosedByLowLegArgument : Bool
round72CCRawCountingClosedByLowLegArgument = false

round72LHComplexityUsesLowLegShellIsTrue :
  round72LHComplexityUsesLowLegShell ≡ true
round72LHComplexityUsesLowLegShellIsTrue = refl

round72LowLegCubicCardinalityMajorantConstructedIsTrue :
  round72LowLegCubicCardinalityMajorantConstructed ≡ true
round72LowLegCubicCardinalityMajorantConstructedIsTrue = refl

round72HHRawCountingClosedByLowLegArgumentIsFalse :
  round72HHRawCountingClosedByLowLegArgument ≡ false
round72HHRawCountingClosedByLowLegArgumentIsFalse = refl
