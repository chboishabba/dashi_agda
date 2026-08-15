module DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- Venue/year: Annales scientifiques de l'Ecole Normale Superieure 14 (1981).
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Venue/year: Grundlehren der mathematischen Wissenschaften 343, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Terence Tao.
-- Title: "Lecture Notes 6 for 247B: Paradifferential calculus,
-- fractional chain and Leibnitz rules".
-- Venue/year: UCLA Math 247B lecture notes, 2007.
-- DOI: none.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Venue/year: Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Construct the literal finite periodic Fourier support interface needed by
-- the localized-regularity lane.  Exact shell and low-pass projectors act
-- directly on the repository Z^3 Fourier carrier.  Because differentiation
-- and curl are mode-local multipliers, both projectors commute definitionally
-- with them.  Resonant triad contributions are classified through the exact
-- three-leg dyadic geometry and Tao/Bony frozen-leg map.
--
-- This file proves support and classification identities.  It does not claim
-- smooth-multiplier norm estimates, time integration, or the continuation
-- theorem required for a full analytic Littlewood-Paley criterion.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.Maybe.Base using (Maybe; just; nothing)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNExactDyadicShellGeometry as Geometry
import DASHI.Physics.Closure.NSTriadKNTaoFrozenLegParaproductProgram as Tao

private
  mapOptional :
    ∀ {a b} {A : Set a} {B : Set b} →
    (A → B) → Maybe A → Maybe B
  mapOptional f nothing = nothing
  mapOptional f (just value) = just (f value)

------------------------------------------------------------------------
-- Literal periodic hard-shell Fourier PDE carrier.
------------------------------------------------------------------------

record PeriodicHardShellFourierPDE {r : Level} : Set (lsuc r) where
  field
    realField : C3.RealField r

    shellOwner : Z3.FourierMode → Nat
    shellSelect : Nat → Z3.FourierMode → Bool
    lowSelect : Nat → Z3.FourierMode → Bool

    ownerSelected :
      (mode : Z3.FourierMode) →
      shellSelect (shellOwner mode) mode ≡ true

    ownerIncludedInOwnLowPass :
      (mode : Z3.FourierMode) →
      lowSelect (shellOwner mode) mode ≡ true

    derivativeMultiplier :
      Z3.FourierMode → C3.Complex realField

    curlMultiplier :
      Z3.FourierMode →
      C3.Complex3 realField →
      C3.Complex3 realField

open PeriodicHardShellFourierPDE public

FourierField :
  ∀ {r} → PeriodicHardShellFourierPDE {r} → Set r
FourierField model =
  Z3.FourierMode → Maybe (C3.Complex3 (realField model))

shellProjector :
  ∀ {r} (model : PeriodicHardShellFourierPDE {r}) →
  Nat → FourierField model → FourierField model
shellProjector model shell carrier mode
  with shellSelect model shell mode
... | true = carrier mode
... | false = nothing

lowProjector :
  ∀ {r} (model : PeriodicHardShellFourierPDE {r}) →
  Nat → FourierField model → FourierField model
lowProjector model cutoff carrier mode
  with lowSelect model cutoff mode
... | true = carrier mode
... | false = nothing

fourierDerivative :
  ∀ {r} (model : PeriodicHardShellFourierPDE {r}) →
  FourierField model → FourierField model
fourierDerivative model carrier mode =
  mapOptional
    (C3.complex3Scale (derivativeMultiplier model mode))
    (carrier mode)

fourierCurl :
  ∀ {r} (model : PeriodicHardShellFourierPDE {r}) →
  FourierField model → FourierField model
fourierCurl model carrier mode =
  mapOptional (curlMultiplier model mode) (carrier mode)

shellProjectorCommutesWithDerivative :
  ∀ {r} (model : PeriodicHardShellFourierPDE {r}) →
  (shell : Nat) →
  (carrier : FourierField model) →
  (mode : Z3.FourierMode) →
  fourierDerivative model (shellProjector model shell carrier) mode
    ≡
  shellProjector model shell (fourierDerivative model carrier) mode
shellProjectorCommutesWithDerivative model shell carrier mode
  with shellSelect model shell mode
... | true = refl
... | false = refl

shellProjectorCommutesWithCurl :
  ∀ {r} (model : PeriodicHardShellFourierPDE {r}) →
  (shell : Nat) →
  (carrier : FourierField model) →
  (mode : Z3.FourierMode) →
  fourierCurl model (shellProjector model shell carrier) mode
    ≡
  shellProjector model shell (fourierCurl model carrier) mode
shellProjectorCommutesWithCurl model shell carrier mode
  with shellSelect model shell mode
... | true = refl
... | false = refl

lowProjectorCommutesWithDerivative :
  ∀ {r} (model : PeriodicHardShellFourierPDE {r}) →
  (cutoff : Nat) →
  (carrier : FourierField model) →
  (mode : Z3.FourierMode) →
  fourierDerivative model (lowProjector model cutoff carrier) mode
    ≡
  lowProjector model cutoff (fourierDerivative model carrier) mode
lowProjectorCommutesWithDerivative model cutoff carrier mode
  with lowSelect model cutoff mode
... | true = refl
... | false = refl

lowProjectorCommutesWithCurl :
  ∀ {r} (model : PeriodicHardShellFourierPDE {r}) →
  (cutoff : Nat) →
  (carrier : FourierField model) →
  (mode : Z3.FourierMode) →
  fourierCurl model (lowProjector model cutoff carrier) mode
    ≡
  lowProjector model cutoff (fourierCurl model carrier) mode
lowProjectorCommutesWithCurl model cutoff carrier mode
  with lowSelect model cutoff mode
... | true = refl
... | false = refl

ownedShellReconstructsMode :
  ∀ {r} (model : PeriodicHardShellFourierPDE {r}) →
  (carrier : FourierField model) →
  (mode : Z3.FourierMode) →
  shellProjector model (shellOwner model mode) carrier mode
    ≡ carrier mode
ownedShellReconstructsMode model carrier mode
  rewrite ownerSelected model mode = refl

ownedLowPassReconstructsMode :
  ∀ {r} (model : PeriodicHardShellFourierPDE {r}) →
  (carrier : FourierField model) →
  (mode : Z3.FourierMode) →
  lowProjector model (shellOwner model mode) carrier mode
    ≡ carrier mode
ownedLowPassReconstructsMode model carrier mode
  rewrite ownerIncludedInOwnLowPass model mode = refl

------------------------------------------------------------------------
-- Literal resonant interaction carrier and Bony/Tao classification.
------------------------------------------------------------------------

record PeriodicTriadInteraction
    {r : Level}
    (model : PeriodicHardShellFourierPDE {r}) : Set r where
  constructor interaction
  field
    leftMode : Z3.FourierMode
    rightMode : Z3.FourierMode
    outputMode : Z3.FourierMode

    resonance :
      Z3.Resonance leftMode rightMode outputMode

    coefficient :
      C3.Complex3 (realField model)

open PeriodicTriadInteraction public

geometryTagToAbsoluteClass :
  Geometry.GeometryTag → Tao.AbsoluteTrichotomy
geometryTagToAbsoluteClass Geometry.leftLowTag = Tao.leftLow
geometryTagToAbsoluteClass Geometry.rightLowTag = Tao.rightLow
geometryTagToAbsoluteClass Geometry.outputLowTag = Tao.outputLow
geometryTagToAbsoluteClass Geometry.comparableTag = Tao.comparable
geometryTagToAbsoluteClass Geometry.transitionTag = Tao.transition
geometryTagToAbsoluteClass Geometry.residualTag = Tao.residual

interactionAbsoluteClass :
  ∀ {r}
    {model : PeriodicHardShellFourierPDE {r}} →
  Geometry.CanonicalGeometryPartition →
  PeriodicTriadInteraction model →
  Tao.AbsoluteTrichotomy
interactionAbsoluteClass {model = model} partition triad =
  geometryTagToAbsoluteClass
    (Geometry.CanonicalGeometryPartition.classify partition
      (shellOwner model (leftMode triad))
      (shellOwner model (rightMode triad))
      (shellOwner model (outputMode triad)))

interactionRelativeClass :
  ∀ {r}
    {model : PeriodicHardShellFourierPDE {r}} →
  Geometry.CanonicalGeometryPartition →
  Tao.FrozenLeg →
  PeriodicTriadInteraction model →
  Tao.RelativeParaproductClass
interactionRelativeClass partition frozen triad =
  Tao.classUnderFreeze frozen
    (interactionAbsoluteClass partition triad)

data ClassifiedPeriodicInteraction
    {r : Level}
    {model : PeriodicHardShellFourierPDE {r}} : Set r where
  lowHighPiece :
    PeriodicTriadInteraction model → ClassifiedPeriodicInteraction
  highLowPiece :
    PeriodicTriadInteraction model → ClassifiedPeriodicInteraction
  highHighToLowPiece :
    PeriodicTriadInteraction model → ClassifiedPeriodicInteraction
  nearPiece :
    PeriodicTriadInteraction model → ClassifiedPeriodicInteraction
  transitionPiece :
    PeriodicTriadInteraction model → ClassifiedPeriodicInteraction
  residualPiece :
    PeriodicTriadInteraction model → ClassifiedPeriodicInteraction

decomposeInteraction :
  ∀ {r}
    {model : PeriodicHardShellFourierPDE {r}} →
  Geometry.CanonicalGeometryPartition →
  Tao.FrozenLeg →
  PeriodicTriadInteraction model →
  ClassifiedPeriodicInteraction {model = model}
decomposeInteraction partition frozen triad
  with interactionRelativeClass partition frozen triad
... | Tao.lowHigh = lowHighPiece triad
... | Tao.highLow = highLowPiece triad
... | Tao.highHighToLow = highHighToLowPiece triad
... | Tao.nearClass = nearPiece triad
... | Tao.transitionClass = transitionPiece triad
... | Tao.residualClass = residualPiece triad

eraseInteraction :
  ∀ {r}
    {model : PeriodicHardShellFourierPDE {r}} →
  ClassifiedPeriodicInteraction {model = model} →
  PeriodicTriadInteraction model
eraseInteraction (lowHighPiece triad) = triad
eraseInteraction (highLowPiece triad) = triad
eraseInteraction (highHighToLowPiece triad) = triad
eraseInteraction (nearPiece triad) = triad
eraseInteraction (transitionPiece triad) = triad
eraseInteraction (residualPiece triad) = triad

eraseDecomposeInteraction :
  ∀ {r}
    {model : PeriodicHardShellFourierPDE {r}} →
  (partition : Geometry.CanonicalGeometryPartition) →
  (frozen : Tao.FrozenLeg) →
  (triad : PeriodicTriadInteraction model) →
  eraseInteraction (decomposeInteraction partition frozen triad)
    ≡ triad
eraseDecomposeInteraction partition frozen triad
  with interactionRelativeClass partition frozen triad
... | Tao.lowHigh = refl
... | Tao.highLow = refl
... | Tao.highHighToLow = refl
... | Tao.nearClass = refl
... | Tao.transitionClass = refl
... | Tao.residualClass = refl

decomposeInteractions :
  ∀ {r}
    {model : PeriodicHardShellFourierPDE {r}} →
  Geometry.CanonicalGeometryPartition →
  Tao.FrozenLeg →
  List (PeriodicTriadInteraction model) →
  List (ClassifiedPeriodicInteraction {model = model})
decomposeInteractions partition frozen =
  map (decomposeInteraction partition frozen)

eraseInteractions :
  ∀ {r}
    {model : PeriodicHardShellFourierPDE {r}} →
  List (ClassifiedPeriodicInteraction {model = model}) →
  List (PeriodicTriadInteraction model)
eraseInteractions = map eraseInteraction

eraseDecomposedInteractions :
  ∀ {r}
    {model : PeriodicHardShellFourierPDE {r}} →
  (partition : Geometry.CanonicalGeometryPartition) →
  (frozen : Tao.FrozenLeg) →
  (triads : List (PeriodicTriadInteraction model)) →
  eraseInteractions (decomposeInteractions partition frozen triads)
    ≡ triads
eraseDecomposedInteractions partition frozen [] = refl
eraseDecomposedInteractions partition frozen (triad ∷ triads)
  rewrite eraseDecomposeInteraction partition frozen triad
        | eraseDecomposedInteractions partition frozen triads = refl

------------------------------------------------------------------------
-- Honest implementation ledger.
------------------------------------------------------------------------

periodicHardShellProjectorConstructed : Bool
periodicHardShellProjectorConstructed = true

periodicHardLowPassProjectorConstructed : Bool
periodicHardLowPassProjectorConstructed = true

ownedShellPointwiseReconstructionClosed : Bool
ownedShellPointwiseReconstructionClosed = true

ownedLowPassPointwiseReconstructionClosed : Bool
ownedLowPassPointwiseReconstructionClosed = true

derivativeProjectorCommutationClosed : Bool
derivativeProjectorCommutationClosed = true

curlProjectorCommutationClosed : Bool
curlProjectorCommutationClosed = true

literalResonantTriadCarrierConstructed : Bool
literalResonantTriadCarrierConstructed = true

bonyTaoInteractionClassificationClosed : Bool
bonyTaoInteractionClassificationClosed = true

finiteInteractionRecompositionClosed : Bool
finiteInteractionRecompositionClosed = true

smoothProjectorNormComparisonClosed : Bool
smoothProjectorNormComparisonClosed = false

localizedContinuationNormEstimateClosed : Bool
localizedContinuationNormEstimateClosed = false

periodicHardShellProjectorConstructedIsTrue :
  periodicHardShellProjectorConstructed ≡ true
periodicHardShellProjectorConstructedIsTrue = refl

periodicHardLowPassProjectorConstructedIsTrue :
  periodicHardLowPassProjectorConstructed ≡ true
periodicHardLowPassProjectorConstructedIsTrue = refl

ownedShellPointwiseReconstructionClosedIsTrue :
  ownedShellPointwiseReconstructionClosed ≡ true
ownedShellPointwiseReconstructionClosedIsTrue = refl

ownedLowPassPointwiseReconstructionClosedIsTrue :
  ownedLowPassPointwiseReconstructionClosed ≡ true
ownedLowPassPointwiseReconstructionClosedIsTrue = refl

derivativeProjectorCommutationClosedIsTrue :
  derivativeProjectorCommutationClosed ≡ true
derivativeProjectorCommutationClosedIsTrue = refl

curlProjectorCommutationClosedIsTrue :
  curlProjectorCommutationClosed ≡ true
curlProjectorCommutationClosedIsTrue = refl

bonyTaoInteractionClassificationClosedIsTrue :
  bonyTaoInteractionClassificationClosed ≡ true
bonyTaoInteractionClassificationClosedIsTrue = refl

finiteInteractionRecompositionClosedIsTrue :
  finiteInteractionRecompositionClosed ≡ true
finiteInteractionRecompositionClosedIsTrue = refl

smoothProjectorNormComparisonClosedIsFalse :
  smoothProjectorNormComparisonClosed ≡ false
smoothProjectorNormComparisonClosedIsFalse = refl

localizedContinuationNormEstimateClosedIsFalse :
  localizedContinuationNormEstimateClosed ≡ false
localizedContinuationNormEstimateClosedIsFalse = refl
