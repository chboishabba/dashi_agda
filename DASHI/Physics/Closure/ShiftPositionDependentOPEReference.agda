module DASHI.Physics.Closure.ShiftPositionDependentOPEReference where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.FixedPointAnalyticRGTargets as Targets
open import DASHI.Physics.Closure.ShiftFiniteLocalOPECrossing as FiniteOPE
open import DASHI.Physics.Closure.ShiftFiniteScalingFusionWard as Finite
open import DASHI.Physics.Closure.ShiftFiniteTangentSemigroup as Tangent

------------------------------------------------------------------------
-- Explicit position-dependent OPE reference.
--
-- The coefficient is the exact finite fusion-selection coefficient multiplied
-- by a non-constant symmetric kernel on three insertion positions.  Exchange
-- locality follows from fusion commutativity and kernel symmetry.  Channel
-- crossing follows from the already-proved fusion associativity.
--
-- Position dependence is genuine but finite/discrete; this is not a singular
-- analytic OPE on a continuum domain.

data Position : Set where
  left : Position
  centre : Position
  right : Position

positionWeight : Position → Position → Nat
positionWeight left left = suc (suc zero)
positionWeight centre centre = suc (suc zero)
positionWeight right right = suc (suc zero)
positionWeight left centre = suc zero
positionWeight centre left = suc zero
positionWeight centre right = suc zero
positionWeight right centre = suc zero
positionWeight left right = suc zero
positionWeight right left = suc zero

positionWeightSymmetric :
  (x y : Position) →
  positionWeight x y ≡ positionWeight y x
positionWeightSymmetric left left = refl
positionWeightSymmetric left centre = refl
positionWeightSymmetric left right = refl
positionWeightSymmetric centre left = refl
positionWeightSymmetric centre centre = refl
positionWeightSymmetric centre right = refl
positionWeightSymmetric right left = refl
positionWeightSymmetric right centre = refl
positionWeightSymmetric right right = refl

selectionFromResult :
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation →
  Nat
selectionFromResult Tangent.startPerturbation Tangent.startPerturbation = suc zero
selectionFromResult Tangent.startPerturbation Tangent.nextPerturbation = zero
selectionFromResult Tangent.startPerturbation Tangent.zeroPerturbation = zero
selectionFromResult Tangent.nextPerturbation Tangent.startPerturbation = zero
selectionFromResult Tangent.nextPerturbation Tangent.nextPerturbation = suc zero
selectionFromResult Tangent.nextPerturbation Tangent.zeroPerturbation = zero
selectionFromResult Tangent.zeroPerturbation Tangent.startPerturbation = zero
selectionFromResult Tangent.zeroPerturbation Tangent.nextPerturbation = zero
selectionFromResult Tangent.zeroPerturbation Tangent.zeroPerturbation = suc zero

positionCoefficient :
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation →
  Position → Position → Nat
positionCoefficient p q r x y =
  positionWeight x y
    *
  selectionFromResult (Finite._⊗p_ p q) r

positionProduct :
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation →
  Position → Position →
  Tangent.ShiftFinitePerturbation
positionProduct p q x y = Finite._⊗p_ p q

coefficientExchange :
  (p q r : Tangent.ShiftFinitePerturbation) →
  (x y : Position) →
  positionCoefficient p q r x y
    ≡
  positionCoefficient q p r y x
coefficientExchange p q r x y
  rewrite FiniteOPE.fusionCommutative p q
        | positionWeightSymmetric x y
  = refl

productExchange :
  (p q : Tangent.ShiftFinitePerturbation) →
  (x y : Position) →
  positionProduct p q x y ≡ positionProduct q p y x
productExchange p q x y = FiniteOPE.fusionCommutative p q

channelLeft :
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation
channelLeft p q r = Finite._⊗p_ (Finite._⊗p_ p q) r

channelRight :
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation
channelRight p q r = Finite._⊗p_ p (Finite._⊗p_ q r)

channelCrossing :
  (p q r : Tangent.ShiftFinitePerturbation) →
  channelLeft p q r ≡ channelRight p q r
channelCrossing = Finite.fusionAssociative

positionChannelCoefficient :
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation →
  Position → Position → Position → Nat
positionChannelCoefficient p q r output x y z =
  (positionWeight x y + positionWeight y z)
    *
  selectionFromResult (channelLeft p q r) output

positionChannelCrossing :
  (p q r output : Tangent.ShiftFinitePerturbation) →
  (x y z : Position) →
  positionChannelCoefficient p q r output x y z
    ≡
  (positionWeight x y + positionWeight y z)
    *
  selectionFromResult (channelRight p q r) output
positionChannelCrossing p q r output x y z
  rewrite channelCrossing p q r
  = refl

correlation2 :
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation →
  Position → Position → Nat
correlation2 p q x y =
  positionWeight x y
    *
  (Finite.finiteScalingDimension p * Finite.finiteScalingDimension q)

correlation4 :
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation →
  Position → Position → Position → Position → Nat
correlation4 p q r s x y z w =
  (positionWeight x y + positionWeight z w)
    *
  Finite.finiteScalingDimension
    (Finite._⊗p_ (Finite._⊗p_ (Finite._⊗p_ p q) r) s)

Locality : Set
Locality =
  (p q r : Tangent.ShiftFinitePerturbation) →
  (x y : Position) →
  positionCoefficient p q r x y ≡ positionCoefficient q p r y x

OPEConverges : Set
OPEConverges =
  (p q : Tangent.ShiftFinitePerturbation) →
  (x y : Position) →
  positionProduct p q x y ≡ Finite._⊗p_ p q

CrossingSymmetry : Set
CrossingSymmetry =
  (p q r : Tangent.ShiftFinitePerturbation) →
  channelLeft p q r ≡ channelRight p q r

AssociativityInCommonDomain : Set
AssociativityInCommonDomain = CrossingSymmetry

localityWitness : Locality
localityWitness = coefficientExchange

opeConvergesWitness : OPEConverges
opeConvergesWitness p q x y = refl

crossingWitness : CrossingSymmetry
crossingWitness = channelCrossing

shiftPositionDependentLocalOPE :
  Targets.LocalOPECrossing
    Nat Position Tangent.ShiftFinitePerturbation
shiftPositionDependentLocalOPE =
  record
    { coefficient = positionCoefficient
    ; product = positionProduct
    ; correlation2 = correlation2
    ; correlation4 = correlation4
    ; Locality = Locality
    ; OPEConverges = OPEConverges
    ; CrossingSymmetry = CrossingSymmetry
    ; AssociativityInCommonDomain = AssociativityInCommonDomain
    }

record ShiftPositionDependentOPEReference : Setω where
  field
    localOPETarget :
      Targets.LocalOPECrossing
        Nat Position Tangent.ShiftFinitePerturbation
    locality : Locality
    finiteConvergence : OPEConverges
    crossing : CrossingSymmetry
    commonDomainAssociativity : AssociativityInCommonDomain
    coefficientDependsOnPosition :
      positionCoefficient
        Tangent.zeroPerturbation
        Tangent.zeroPerturbation
        Tangent.zeroPerturbation
        left left
      ≡ suc (suc zero)
    coefficientAtSeparatedPositions :
      positionCoefficient
        Tangent.zeroPerturbation
        Tangent.zeroPerturbation
        Tangent.zeroPerturbation
        left right
      ≡ suc zero
    nonClaimBoundary : List String

open ShiftPositionDependentOPEReference public

canonicalShiftPositionDependentOPEReference :
  ShiftPositionDependentOPEReference
canonicalShiftPositionDependentOPEReference =
  record
    { localOPETarget = shiftPositionDependentLocalOPE
    ; locality = localityWitness
    ; finiteConvergence = opeConvergesWitness
    ; crossing = crossingWitness
    ; commonDomainAssociativity = crossingWitness
    ; coefficientDependsOnPosition = refl
    ; coefficientAtSeparatedPositions = refl
    ; nonClaimBoundary =
        "ShiftPositionDependentOPEReference has an explicit non-constant coefficient kernel on three insertion positions"
        ∷ "exchange locality is inherited from finite fusion commutativity and position-kernel symmetry"
        ∷ "crossing is inherited from exact fusion associativity"
        ∷ "the OPE is finite and everywhere defined; convergence is finite normalization, not analytic series convergence"
        ∷ "No singular kernel, complex position plane, conformal block, reflection positivity, or continuum QFT reconstruction is claimed"
        ∷ []
    }
