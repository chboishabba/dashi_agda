module DASHI.Physics.Closure.NSTriadKNR104GlobalLayerCakePhysicalPacketWeldExact where

------------------------------------------------------------------------
-- STRICT B-PHASE S2b1b2b1 / GLOBAL RECURSIVE-PREFIX R104 PACKET WELD
--
-- S2b1b2b0 closes the LOCAL statement at one genuine shell jump:
-- the R104 structural tail is the canonical drop-suffix of the current
-- recursive list.  The remaining bookkeeping problem is global: after the
-- recursion has traversed an arbitrary prefix, that current drop-suffix must
-- still be the upper-shell suffix of the ORIGINAL sorted nonzero support.
--
-- This file carries that prefix explicitly.  It proves every traversed prefix
-- remains at or below the current shell, hence lies strictly below the next
-- threshold at a genuine shell jump.  The existing prefix-erasure theorem then
-- transports the local R104 tail back to the canonical original support, where
-- S2b1b2a identifies it with R98 normalized physical boundary flux.
--
-- Equal-shell interfaces are inactive: their dyadic weight increment is zero,
-- so no physical packet theorem is required there.  Consequently the whole
-- R104 Abel layer-cake on the canonical sorted carrier is exactly a physical
-- upper-shell boundary-flux layer-cake.
--
-- No quantitative bound, absolute-value majorant, Schur estimate, or R406
-- estimate is introduced.  S2b2 remains the next nonlinear theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_; _<_)
open import Data.Nat.Properties using (_≤?_)
import Data.Nat.Properties as NatP
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as R34
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as S0
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalProductionBandTransferExact as S2b0
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalProductionRadialOrderExact as Radial
import DASHI.Physics.Closure.NSTriadKNLiteralUpperShellPacketSelectorExact as Upper
import DASHI.Physics.Closure.NSTriadKNLiteralUpperShellCanonicalSuffixExact as Canonical
import DASHI.Physics.Closure.NSTriadKNR104StrictShellJumpTailExact as StrictTail
import DASHI.Physics.Closure.NSTriadKNUpperShellPrefixErasureExact as Prefix
import DASHI.Physics.Closure.NSTriadKNCriticalProductionPacketLayerCakeRound104Exact as LayerCake
import DASHI.Physics.Closure.NSTriadKNPacketBoundaryFluxNormalizationRound98Exact as Norm

F : C3.RealField _
F = Rational.rationalRealField

canonicalSortedModes :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Z3.FourierMode
canonicalSortedModes system =
  Radial.sortByShell (R34.nonzeroCutoffModes (Audit.cutoff system))

------------------------------------------------------------------------
-- Prefix bookkeeping.
------------------------------------------------------------------------

data AllAtOrBelow (bound : Nat) : List Z3.FourierMode → Set where
  atOrBelow[] : AllAtOrBelow bound []
  atOrBelow∷ : ∀ {mode rest} →
    Shell.shellIndex mode ≤ bound →
    AllAtOrBelow bound rest →
    AllAtOrBelow bound (mode ∷ rest)

snoc : ∀ {A : Set} → List A → A → List A
snoc [] x = x ∷ []
snoc (y ∷ ys) x = y ∷ snoc ys x

appendSnoc :
  ∀ {A : Set} →
  (prefix : List A) →
  (x : A) →
  (suffix : List A) →
  Prefix.append (snoc prefix x) suffix
  ≡ Prefix.append prefix (x ∷ suffix)
appendSnoc [] x suffix = refl
appendSnoc (y ∷ ys) x suffix =
  cong (y ∷_) (appendSnoc ys x suffix)

snocPreservesAtOrBelow :
  ∀ {oldBound newBound} →
  (prefix : List Z3.FourierMode) →
  (mode : Z3.FourierMode) →
  AllAtOrBelow oldBound prefix →
  oldBound ≤ newBound →
  Shell.shellIndex mode ≤ newBound →
  AllAtOrBelow newBound (snoc prefix mode)
snocPreservesAtOrBelow [] mode atOrBelow[] old≤new mode≤new =
  atOrBelow∷ mode≤new atOrBelow[]
snocPreservesAtOrBelow (head ∷ rest) mode
    (atOrBelow∷ head≤old rest≤old) old≤new mode≤new =
  atOrBelow∷
    (NatP.≤-trans head≤old old≤new)
    (snocPreservesAtOrBelow rest mode rest≤old old≤new mode≤new)

atOrBelowStrictlyBelow :
  ∀ {bound threshold} →
  (prefix : List Z3.FourierMode) →
  AllAtOrBelow bound prefix →
  bound < threshold →
  Prefix.AllBelow threshold prefix
atOrBelowStrictlyBelow [] atOrBelow[] jump = Prefix.allBelow[]
atOrBelowStrictlyBelow (mode ∷ rest)
    (atOrBelow∷ mode≤bound rest≤bound) jump =
  Prefix.allBelow∷
    (NatP.≤-<-trans mode≤bound jump)
    (atOrBelowStrictlyBelow rest rest≤bound jump)

------------------------------------------------------------------------
-- Physical layer-cake: only genuine shell jumps carry packet flux.
------------------------------------------------------------------------

physicalUpperShellLayerCake :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Z3.FourierMode → ℚ
physicalUpperShellLayerCake system [] = 0ℚ
physicalUpperShellLayerCake system (mode ∷ []) = 0ℚ
physicalUpperShellLayerCake {E} {I} system (left ∷ right ∷ rest)
  with Shell.shellIndex right ≤? Shell.shellIndex left
... | yes right≤left = physicalUpperShellLayerCake system (right ∷ rest)
... | no notRight≤Left =
  LayerCake.sub
      (S0.dyadicCriticalWeight right)
      (S0.dyadicCriticalWeight left)
    * Norm.normalizedBoundaryTransfer
        E I (Upper.upperShellPacket (Shell.shellIndex right))
        (Audit.velocity system) (Audit.cutoff system)
    + physicalUpperShellLayerCake system (right ∷ rest)

dyadicWeightSameShell :
  (left right : Z3.FourierMode) →
  Shell.shellIndex left ≡ Shell.shellIndex right →
  S0.dyadicCriticalWeight left ≡ S0.dyadicCriticalWeight right
dyadicWeightSameShell left right shellsEqual =
  cong (λ shell → S0.natAsRational (Shell.pow2 shell)) shellsEqual

------------------------------------------------------------------------
-- Recursive-prefix weld to the ORIGINAL canonical sorted support.
------------------------------------------------------------------------

layerCakeWeldFromPrefix :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  Reality.RealityCondition (Audit.velocity system) →
  Reality.DivergenceFreeCondition E (Audit.velocity system) →
  (prefix : List Z3.FourierMode) →
  (head : Z3.FourierMode) →
  (rest : List Z3.FourierMode) →
  AllAtOrBelow (Shell.shellIndex head) prefix →
  Prefix.append prefix (head ∷ rest) ≡ canonicalSortedModes system →
  Radial.ShellOrdered (head ∷ rest) →
  LayerCake.radialLayerCake
      (S2b0.literalBandTransfers system (head ∷ rest))
  ≡ physicalUpperShellLayerCake system (head ∷ rest)
layerCakeWeldFromPrefix
    system reality divergenceFree prefix head []
    prefixBound decomposition Radial.ordered1 = refl
layerCakeWeldFromPrefix
    {E} {I} system reality divergenceFree prefix left (right ∷ rest)
    prefixBound decomposition
    (Radial.ordered∷ left≤right tailOrdered)
  with Shell.shellIndex right ≤? Shell.shellIndex left in comparison
... | yes right≤left =
  let
    shellsEqual : Shell.shellIndex left ≡ Shell.shellIndex right
    shellsEqual = NatP.≤-antisym left≤right right≤left

    weightsEqual :
      S0.dyadicCriticalWeight left ≡ S0.dyadicCriticalWeight right
    weightsEqual = dyadicWeightSameShell left right shellsEqual

    nextPrefixBound :
      AllAtOrBelow (Shell.shellIndex right) (snoc prefix left)
    nextPrefixBound =
      snocPreservesAtOrBelow
        prefix left prefixBound left≤right left≤right

    nextDecomposition :
      Prefix.append (snoc prefix left) (right ∷ rest)
      ≡ canonicalSortedModes system
    nextDecomposition =
      trans (appendSnoc prefix left (right ∷ rest)) decomposition

    tailWeld =
      layerCakeWeldFromPrefix
        system reality divergenceFree
        (snoc prefix left) right rest
        nextPrefixBound nextDecomposition tailOrdered
  in
  rewrite weightsEqual | tailWeld =
    solve
      ( S0.dyadicCriticalWeight right
      ∷ LayerCake.totalTransfer
          (S2b0.literalBandTransfers system (right ∷ rest))
      ∷ physicalUpperShellLayerCake system (right ∷ rest)
      ∷ [] )
... | no notRight≤Left =
  let
    strictJump : Shell.shellIndex left < Shell.shellIndex right
    strictJump = NatP.≰⇒> notRight≤Left

    prefixBelow : Prefix.AllBelow (Shell.shellIndex right) prefix
    prefixBelow = atOrBelowStrictlyBelow prefix prefixBound strictJump

    currentDropToOriginal :
      Canonical.dropBelowShell
        (Shell.shellIndex right) (left ∷ right ∷ rest)
      ≡ Canonical.dropBelowShell
        (Shell.shellIndex right) (canonicalSortedModes system)
    currentDropToOriginal =
      trans
        (sym
          (Prefix.upperShellDropBelowPrefixErasure
            (Shell.shellIndex right)
            prefix (left ∷ right ∷ rest) prefixBelow))
        (cong
          (Canonical.dropBelowShell (Shell.shellIndex right))
          decomposition)

    tailIsPhysicalBoundary :
      LayerCake.totalTransfer
        (S2b0.literalBandTransfers system (right ∷ rest))
      ≡ Norm.normalizedBoundaryTransfer
          E I (Upper.upperShellPacket (Shell.shellIndex right))
          (Audit.velocity system) (Audit.cutoff system)
    tailIsPhysicalBoundary =
      trans
        (StrictTail.r104TailAtStrictShellJumpIsCanonicalSuffix
          system left right rest strictJump)
        (trans
          (cong (Canonical.rawProjectedPairing system) currentDropToOriginal)
          (Canonical.canonicalUpperShellSuffixIsNormalizedBoundaryFlux
            system (Shell.shellIndex right) reality divergenceFree))

    nextPrefixBound :
      AllAtOrBelow (Shell.shellIndex right) (snoc prefix left)
    nextPrefixBound =
      snocPreservesAtOrBelow
        prefix left prefixBound left≤right left≤right

    nextDecomposition :
      Prefix.append (snoc prefix left) (right ∷ rest)
      ≡ canonicalSortedModes system
    nextDecomposition =
      trans (appendSnoc prefix left (right ∷ rest)) decomposition

    tailWeld =
      layerCakeWeldFromPrefix
        system reality divergenceFree
        (snoc prefix left) right rest
        nextPrefixBound nextDecomposition tailOrdered
  in
  rewrite tailIsPhysicalBoundary | tailWeld = refl

------------------------------------------------------------------------
-- Canonical closed representation theorem.
------------------------------------------------------------------------

canonicalR104LayerCakeIsPhysicalUpperShellLayerCake :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  Reality.RealityCondition (Audit.velocity system) →
  Reality.DivergenceFreeCondition E (Audit.velocity system) →
  LayerCake.radialLayerCake
      (S2b0.literalBandTransfers system (canonicalSortedModes system))
  ≡ physicalUpperShellLayerCake system (canonicalSortedModes system)
canonicalR104LayerCakeIsPhysicalUpperShellLayerCake
    system reality divergenceFree
  with canonicalSortedModes system
     | Radial.sortByShellOrdered
         (R34.nonzeroCutoffModes (Audit.cutoff system))
... | [] | Radial.ordered[] = refl
... | head ∷ rest | ordered =
  layerCakeWeldFromPrefix
    system reality divergenceFree
    [] head rest atOrBelow[] refl ordered

------------------------------------------------------------------------
-- Status / remaining nonlinear seam.
------------------------------------------------------------------------

globalRecursivePrefixPhysicalPacketWeldClosed : Bool
globalRecursivePrefixPhysicalPacketWeldClosed = true

globalR104LayerCakePhysicalPacketWeldClosed : Bool
globalR104LayerCakePhysicalPacketWeldClosed = true

s2QuantitativePacketFluxEstimateClosed : Bool
s2QuantitativePacketFluxEstimateClosed = false

globalRecursivePrefixPhysicalPacketWeldClosedIsTrue :
  globalRecursivePrefixPhysicalPacketWeldClosed ≡ true
globalRecursivePrefixPhysicalPacketWeldClosedIsTrue = refl

globalR104LayerCakePhysicalPacketWeldClosedIsTrue :
  globalR104LayerCakePhysicalPacketWeldClosed ≡ true
globalR104LayerCakePhysicalPacketWeldClosedIsTrue = refl

s2QuantitativePacketFluxEstimateClosedIsFalse :
  s2QuantitativePacketFluxEstimateClosed ≡ false
s2QuantitativePacketFluxEstimateClosedIsFalse = refl
