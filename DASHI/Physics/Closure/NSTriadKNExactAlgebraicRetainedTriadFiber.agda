module DASHI.Physics.Closure.NSTriadKNExactAlgebraicRetainedTriadFiber where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Primitive using (Setω)
open import Data.Fin as F using (Fin)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNPairIncidenceKernelFormula as KernelFormula
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNConcreteActualRetainedFiber as RetainedFiber
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm

------------------------------------------------------------------------
-- Exact scalar socket.
--
-- The physical note is real-valued, whereas the existing kernel target is a
-- Nat-valued fail-closed boundary.  This socket records the operations and
-- laws needed by the exact formulas without choosing a concrete real model.
------------------------------------------------------------------------

record ExactScalarOperations : Set₁ where
  field
    Carrier : Set

    zero one : Carrier
    _+_ : Carrier → Carrier → Carrier
    _*_ : Carrier → Carrier → Carrier

    third : Carrier → Carrier
    maxZero : Carrier → Carrier
    maxPositive : Carrier → Carrier
    maxNegative : Carrier → Carrier
    absolute : Carrier → Carrier
    sqrt : Carrier → Carrier
    natToScalar : Nat → Carrier

    Nonnegative : Carrier → Set
    WithinMinusOneOne : Carrier → Set
    Nonzero : Carrier → Set

    absoluteSplit :
      (x : Carrier) →
      absolute x ≡ maxPositive x + maxNegative x

    leftMultiplicationDistributesOverAddition :
      (a b c : Carrier) →
      a * (b + c) ≡ (a * b) + (a * c)

open ExactScalarOperations public

------------------------------------------------------------------------
-- Finite carriers and the finite mode/triad carrier.
------------------------------------------------------------------------

record FiniteCarrier : Set₁ where
  constructor mkFiniteCarrier
  field
    Carrier : Set
    cardinality : Nat
    decode : F.Fin cardinality → Carrier
    encode : Carrier → F.Fin cardinality
    decodeEncode :
      (x : Carrier) → decode (encode x) ≡ x
    encodeDecode :
      (i : F.Fin cardinality) → encode (decode i) ≡ i

open FiniteCarrier public

record TriadData (Mode Scalar : Set) : Set where
  constructor mkTriadData
  field
    i j k : Mode
    gamma : Scalar

open TriadData public

record FiniteTriadModeSurface (S : ExactScalarOperations) : Setω where
  constructor mkFiniteTriadModeSurface
  field
    modeCarrier : FiniteCarrier
    triadCarrier : FiniteCarrier
    triadData :
      FiniteCarrier.Carrier triadCarrier →
      TriadData
        (FiniteCarrier.Carrier modeCarrier)
        (ExactScalarOperations.Carrier S)
    triadCoherenceBound :
      (τ : FiniteCarrier.Carrier triadCarrier) →
      WithinMinusOneOne S (gamma (triadData τ))

open FiniteTriadModeSurface public

ModeOf :
  {S : ExactScalarOperations} →
  FiniteTriadModeSurface S → Set
ModeOf surface = FiniteCarrier.Carrier (modeCarrier surface)

TriadOf :
  {S : ExactScalarOperations} →
  (surface : FiniteTriadModeSurface S) → Set
TriadOf surface = FiniteCarrier.Carrier (triadCarrier surface)

------------------------------------------------------------------------
-- The three unordered pair slots of a triad.
------------------------------------------------------------------------

data PairSlot : Set where
  firstPair secondPair thirdPair : PairSlot

record PairEdge (Mode : Set) : Set where
  constructor mkPairEdge
  field
    left right : Mode

open PairEdge public

pairEdges :
  {Mode Scalar : Set} →
  TriadData Mode Scalar →
  PairSlot → PairEdge Mode
pairEdges τ firstPair = mkPairEdge (i τ) (j τ)
pairEdges τ secondPair = mkPairEdge (i τ) (k τ)
pairEdges τ thirdPair = mkPairEdge (j τ) (k τ)

pairSlotCount : Nat
pairSlotCount = suc (suc (suc Agda.Builtin.Nat.zero))

pairSlotsAreExactlyThree :
  pairSlotCount ≡ suc (suc (suc Agda.Builtin.Nat.zero))
pairSlotsAreExactlyThree = refl

------------------------------------------------------------------------
-- Admissible profile and exact triad weights.
------------------------------------------------------------------------

record AdmissibleAmplitudeProfile
    {S : ExactScalarOperations}
    (surface : FiniteTriadModeSurface S) : Setω where
  constructor mkAdmissibleAmplitudeProfile
  field
    probability : ModeOf surface → Carrier S
    amplitude : ModeOf surface → Carrier S

    amplitudeFormula :
      (m : ModeOf surface) →
      amplitude m ≡ sqrt S (maxZero S (probability m))

    amplitudeNonnegative :
      (m : ModeOf surface) →
      Nonnegative S (amplitude m)

open AdmissibleAmplitudeProfile public

triadRawWeight :
  {S : ExactScalarOperations} →
  {surface : FiniteTriadModeSurface S} →
  AdmissibleAmplitudeProfile surface →
  TriadOf surface → Carrier S
triadRawWeight {S = S} {surface = surface} profile τ =
  ExactScalarOperations._*_ S
  (amplitude profile (i (triadData surface τ)))
  (ExactScalarOperations._*_ S
   (amplitude profile (j (triadData surface τ)))
   (amplitude profile (k (triadData surface τ))))

triadPairWeight :
  {S : ExactScalarOperations} →
  {surface : FiniteTriadModeSurface S} →
  AdmissibleAmplitudeProfile surface →
  TriadOf surface → Carrier S
triadPairWeight {S = S} profile τ =
  third S (triadRawWeight profile τ)

pairEdgeWeight :
  {S : ExactScalarOperations} →
  {surface : FiniteTriadModeSurface S} →
  AdmissibleAmplitudeProfile surface →
  TriadOf surface → PairSlot → Carrier S
pairEdgeWeight profile τ _ = triadPairWeight profile τ

pairEdgeWeightIsEqualSplit :
  {S : ExactScalarOperations} →
  {surface : FiniteTriadModeSurface S} →
  (profile : AdmissibleAmplitudeProfile surface) →
  (τ : TriadOf surface) →
  (p : PairSlot) →
  pairEdgeWeight profile τ p ≡ third S (triadRawWeight profile τ)
pairEdgeWeightIsEqualSplit profile τ p = refl

triadNegativeWeight :
  {S : ExactScalarOperations} →
  {surface : FiniteTriadModeSurface S} →
  AdmissibleAmplitudeProfile surface →
  TriadOf surface → Carrier S
triadNegativeWeight {S = S} {surface = surface} profile τ =
  ExactScalarOperations._*_ S
  (triadPairWeight profile τ)
  (maxNegative S (gamma (triadData surface τ)))

triadPositiveWeight :
  {S : ExactScalarOperations} →
  {surface : FiniteTriadModeSurface S} →
  AdmissibleAmplitudeProfile surface →
  TriadOf surface → Carrier S
triadPositiveWeight {S = S} {surface = surface} profile τ =
  ExactScalarOperations._*_ S
  (triadPairWeight profile τ)
  (maxPositive S (gamma (triadData surface τ)))

triadAbsoluteWeight :
  {S : ExactScalarOperations} →
  {surface : FiniteTriadModeSurface S} →
  AdmissibleAmplitudeProfile surface →
  TriadOf surface → Carrier S
triadAbsoluteWeight {S = S} {surface = surface} profile τ =
  ExactScalarOperations._*_ S
  (triadPairWeight profile τ)
  (absolute S (gamma (triadData surface τ)))

pairEdgeNegativeWeight :
  {S : ExactScalarOperations} →
  {surface : FiniteTriadModeSurface S} →
  AdmissibleAmplitudeProfile surface →
  TriadOf surface → PairSlot → Carrier S
pairEdgeNegativeWeight profile τ _ = triadNegativeWeight profile τ

pairEdgePositiveWeight :
  {S : ExactScalarOperations} →
  {surface : FiniteTriadModeSurface S} →
  AdmissibleAmplitudeProfile surface →
  TriadOf surface → PairSlot → Carrier S
pairEdgePositiveWeight profile τ _ = triadPositiveWeight profile τ

pairEdgeAbsoluteWeight :
  {S : ExactScalarOperations} →
  {surface : FiniteTriadModeSurface S} →
  AdmissibleAmplitudeProfile surface →
  TriadOf surface → PairSlot → Carrier S
pairEdgeAbsoluteWeight profile τ _ = triadAbsoluteWeight profile τ

triadRawWeightFormula :
  {S : ExactScalarOperations} →
  {surface : FiniteTriadModeSurface S} →
  (profile : AdmissibleAmplitudeProfile surface) →
  (τ : TriadOf surface) →
  triadRawWeight profile τ ≡
  ExactScalarOperations._*_ S
  (amplitude profile (i (triadData surface τ)))
  (ExactScalarOperations._*_ S
   (amplitude profile (j (triadData surface τ)))
   (amplitude profile (k (triadData surface τ))))
triadRawWeightFormula {S = S} {surface = surface} profile τ = refl

triadPairWeightFormula :
  {S : ExactScalarOperations} →
  {surface : FiniteTriadModeSurface S} →
  (profile : AdmissibleAmplitudeProfile surface) →
  (τ : TriadOf surface) →
  triadPairWeight profile τ ≡ third S (triadRawWeight profile τ)
triadPairWeightFormula {S = S} {surface = surface} profile τ = refl

triadNegativeWeightFormula :
  {S : ExactScalarOperations} →
  {surface : FiniteTriadModeSurface S} →
  (profile : AdmissibleAmplitudeProfile surface) →
  (τ : TriadOf surface) →
  triadNegativeWeight profile τ ≡
  ExactScalarOperations._*_ S
  (triadPairWeight profile τ)
  (maxNegative S (gamma (triadData surface τ)))
triadNegativeWeightFormula {S = S} {surface = surface} profile τ = refl

triadPositiveWeightFormula :
  {S : ExactScalarOperations} →
  {surface : FiniteTriadModeSurface S} →
  (profile : AdmissibleAmplitudeProfile surface) →
  (τ : TriadOf surface) →
  triadPositiveWeight profile τ ≡
  ExactScalarOperations._*_ S
  (triadPairWeight profile τ)
  (maxPositive S (gamma (triadData surface τ)))
triadPositiveWeightFormula {S = S} {surface = surface} profile τ = refl

triadAbsoluteWeightFormula :
  {S : ExactScalarOperations} →
  {surface : FiniteTriadModeSurface S} →
  (profile : AdmissibleAmplitudeProfile surface) →
  (τ : TriadOf surface) →
  triadAbsoluteWeight profile τ ≡
  ExactScalarOperations._*_ S
  (triadPairWeight profile τ)
  (absolute S (gamma (triadData surface τ)))
triadAbsoluteWeightFormula {S = S} {surface = surface} profile τ = refl

triadAbsoluteWeightSplitsBySign :
  {S : ExactScalarOperations} →
  {surface : FiniteTriadModeSurface S} →
  (profile : AdmissibleAmplitudeProfile surface) →
  (τ : TriadOf surface) →
  triadAbsoluteWeight profile τ ≡
  ExactScalarOperations._+_ S
    (triadPositiveWeight profile τ)
    (triadNegativeWeight profile τ)
triadAbsoluteWeightSplitsBySign {S = S} {surface = surface} profile τ =
  trans
    (cong
      (λ x → ExactScalarOperations._*_ S (triadPairWeight profile τ) x)
      (absoluteSplit S (gamma (triadData surface τ))))
    (leftMultiplicationDistributesOverAddition S
      (triadPairWeight profile τ)
      (maxPositive S (gamma (triadData surface τ)))
      (maxNegative S (gamma (triadData surface τ))))

------------------------------------------------------------------------
-- Nonempty absolute support is an explicit admissibility premise.
------------------------------------------------------------------------

record AbsoluteCarrierPremise
    {S : ExactScalarOperations}
    {surface : FiniteTriadModeSurface S}
    (profile : AdmissibleAmplitudeProfile surface) : Setω where
  constructor mkAbsoluteCarrierPremise
  field
    nonzeroAbsoluteTriad :
      Σ (TriadOf surface)
        (λ τ → Nonzero S (triadAbsoluteWeight profile τ))

open AbsoluteCarrierPremise public

------------------------------------------------------------------------
-- Exact finite retained-triad fibers.
------------------------------------------------------------------------

infix 4 _∈_

data _∈_ {A : Set} (x : A) : List A → Set where
  here : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

weightedListSum :
  {S : ExactScalarOperations} →
  {A : Set} →
  (A → Carrier S) → List A → Carrier S
weightedListSum {S = S} weight [] = zero S
weightedListSum {S = S} weight (x ∷ xs) =
  ExactScalarOperations._+_ S
    (weight x)
    (weightedListSum {S = S} weight xs)

record ExactRetainedTriadFiberInterface
    {S : ExactScalarOperations}
    (surface : FiniteTriadModeSurface S)
    (profile : AdmissibleAmplitudeProfile surface)
    (SourceIndex TargetIndex : FiniteCarrier)
    (sourceIndex :
      TriadOf surface → FiniteCarrier.Carrier SourceIndex)
    (targetIndex :
      TriadOf surface → FiniteCarrier.Carrier TargetIndex)
    (retainedPositiveSector : TriadOf surface → Set) : Setω where
  constructor mkExactRetainedTriadFiberInterface
  field
    fiber :
      FiniteCarrier.Carrier SourceIndex →
      FiniteCarrier.Carrier TargetIndex → List (TriadOf surface)

    fiberSourceAgreement :
      {f : FiniteCarrier.Carrier SourceIndex} →
      {t : FiniteCarrier.Carrier TargetIndex} →
      (τ : TriadOf surface) →
      τ ∈ fiber f t →
      sourceIndex τ ≡ f

    fiberTargetAgreement :
      {f : FiniteCarrier.Carrier SourceIndex} →
      {t : FiniteCarrier.Carrier TargetIndex} →
      (τ : TriadOf surface) →
      τ ∈ fiber f t →
      targetIndex τ ≡ t

    fiberRetainedAgreement :
      {f : FiniteCarrier.Carrier SourceIndex} →
      {t : FiniteCarrier.Carrier TargetIndex} →
      (τ : TriadOf surface) →
      τ ∈ fiber f t →
      retainedPositiveSector τ

    triadToFiber :
      {f : FiniteCarrier.Carrier SourceIndex} →
      {t : FiniteCarrier.Carrier TargetIndex} →
      (τ : TriadOf surface) →
      sourceIndex τ ≡ f →
      targetIndex τ ≡ t →
      retainedPositiveSector τ →
      τ ∈ fiber f t

    triadWeight : TriadOf surface → Carrier S

    triadWeightFormula :
      (τ : TriadOf surface) →
      triadWeight τ ≡ triadAbsoluteWeight profile τ

    fiberAggregate :
      FiniteCarrier.Carrier SourceIndex →
      FiniteCarrier.Carrier TargetIndex → Carrier S

    fiberAggregateIsFiniteWeightedSum :
      (f : FiniteCarrier.Carrier SourceIndex) →
      (t : FiniteCarrier.Carrier TargetIndex) →
      fiberAggregate f t ≡
      weightedListSum {S = S} triadWeight (fiber f t)

open ExactRetainedTriadFiberInterface public

------------------------------------------------------------------------
-- Conditional bridge to the existing Nat-valued physical target.
--
-- The bridge is a target record, not a constructor.  In particular, the
-- Nat-to-scalar weight translation, the physical triad map, and the kernel
-- equality must be supplied by the missing source data.
------------------------------------------------------------------------

record ActualPairIncidenceKernelFormulaBridge
    {S : ExactScalarOperations}
    (surface : FiniteTriadModeSurface S)
    (profile : AdmissibleAmplitudeProfile surface)
    {residueNormModel : ResidueNorm.ResidueNormModel}
    {shellIndex : Nat}
    (relationData :
      Relation.ActualPairIncidenceRelationData
        residueNormModel shellIndex)
    (physicalFormula :
      KernelFormula.ActualPairIncidenceKernelFormulaTarget
        residueNormModel shellIndex)
    (SourceIndex TargetIndex : FiniteCarrier)
    (sourceIndex :
      TriadOf surface → FiniteCarrier.Carrier SourceIndex)
    (targetIndex :
      TriadOf surface → FiniteCarrier.Carrier TargetIndex)
    (retainedPositiveSector : TriadOf surface → Set)
    (fiberInterface :
      ExactRetainedTriadFiberInterface
        surface
        profile
        SourceIndex
        TargetIndex
        sourceIndex
        targetIndex
        retainedPositiveSector) : Setω where
  constructor mkActualPairIncidenceKernelFormulaBridge
  field
    retainedFiberInterface :
      RetainedFiber.ConcreteActualRetainedFiberInterface
        relationData physicalFormula

    sourceProjection :
      KernelFormula.ActualPairIncidenceKernelFormulaTarget.FiniteIndex
        physicalFormula →
      FiniteCarrier.Carrier SourceIndex

    targetProjection :
      KernelFormula.ActualPairIncidenceKernelFormulaTarget.TailIndex
        physicalFormula →
      FiniteCarrier.Carrier TargetIndex

    physicalTriadToExactTriad :
      KernelFormula.ActualPairIncidenceKernelFormulaTarget.TriadIncidence
        physicalFormula →
      TriadOf surface

    physicalTriadWeightAgreement :
      (r : KernelFormula.ActualPairIncidenceKernelFormulaTarget.TriadIncidence
        physicalFormula) →
      natToScalar S
        (KernelFormula.ActualPairIncidenceKernelFormulaTarget.triadWeight
          physicalFormula r)
        ≡
      triadWeight fiberInterface (physicalTriadToExactTriad r)

    physicalKernelAgreesWithExactFiberAggregate :
      (f : KernelFormula.ActualPairIncidenceKernelFormulaTarget.FiniteIndex
        physicalFormula) →
      (t : KernelFormula.ActualPairIncidenceKernelFormulaTarget.TailIndex
        physicalFormula) →
      natToScalar S
        (KernelFormula.ActualPairIncidenceKernelFormulaTarget.actualKernel
          physicalFormula f t)
        ≡
      fiberAggregate fiberInterface
        (sourceProjection f)
        (targetProjection t)

------------------------------------------------------------------------
-- Exact scalar kernel formula obtained by composing the physical bridge
-- with the retained-fiber finite weighted-sum law.
--
-- This is a genuine transport theorem: it consumes an explicit physical
-- bridge and does not construct one.  Keeping the composition here prevents
-- downstream Schur proofs from repeating the Nat-to-scalar and fiber-sum
-- rewrites independently.
------------------------------------------------------------------------

actualKernelAgreesWithExactWeightedFiber :
  {S : ExactScalarOperations} ->
  (surface : FiniteTriadModeSurface S) ->
  (profile : AdmissibleAmplitudeProfile surface) ->
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  (relationData :
    Relation.ActualPairIncidenceRelationData
      residueNormModel shellIndex) ->
  (physicalFormula :
    KernelFormula.ActualPairIncidenceKernelFormulaTarget
      residueNormModel shellIndex) ->
  (SourceIndex TargetIndex : FiniteCarrier) ->
  (sourceIndex :
    TriadOf surface -> FiniteCarrier.Carrier SourceIndex) ->
  (targetIndex :
    TriadOf surface -> FiniteCarrier.Carrier TargetIndex) ->
  (retainedPositiveSector : TriadOf surface -> Set) ->
  (fiberInterface :
    ExactRetainedTriadFiberInterface
      surface
      profile
      SourceIndex
      TargetIndex
      sourceIndex
      targetIndex
      retainedPositiveSector) ->
  (bridge :
    ActualPairIncidenceKernelFormulaBridge
      surface
      profile
      relationData
      physicalFormula
      SourceIndex
      TargetIndex
      sourceIndex
      targetIndex
      retainedPositiveSector
      fiberInterface) ->
  (f : KernelFormula.ActualPairIncidenceKernelFormulaTarget.FiniteIndex
    physicalFormula) ->
  (t : KernelFormula.ActualPairIncidenceKernelFormulaTarget.TailIndex
    physicalFormula) ->
  natToScalar S
    (KernelFormula.ActualPairIncidenceKernelFormulaTarget.actualKernel
      physicalFormula f t)
    ≡
  weightedListSum {S = S}
    (ExactRetainedTriadFiberInterface.triadWeight
      fiberInterface)
    (ExactRetainedTriadFiberInterface.fiber
      fiberInterface
      (ActualPairIncidenceKernelFormulaBridge.sourceProjection bridge f)
      (ActualPairIncidenceKernelFormulaBridge.targetProjection bridge t))
actualKernelAgreesWithExactWeightedFiber
  surface profile relationData physicalFormula
  SourceIndex TargetIndex sourceIndex targetIndex retainedPositiveSector
  fiberInterface bridge f t =
  trans
    (ActualPairIncidenceKernelFormulaBridge.physicalKernelAgreesWithExactFiberAggregate
      bridge f t)
    (ExactRetainedTriadFiberInterface.fiberAggregateIsFiniteWeightedSum
      fiberInterface
      (ActualPairIncidenceKernelFormulaBridge.sourceProjection bridge f)
      (ActualPairIncidenceKernelFormulaBridge.targetProjection bridge t))

------------------------------------------------------------------------
-- Open status: no physical fiber, bridge, or inhabitant is fabricated here.
------------------------------------------------------------------------

exactPhysicalRetainedTriadFiberInterfaceClosed : Bool
exactPhysicalRetainedTriadFiberInterfaceClosed = false

exactPhysicalRetainedTriadFiberInterfaceClosedIsFalse :
  exactPhysicalRetainedTriadFiberInterfaceClosed ≡ false
exactPhysicalRetainedTriadFiberInterfaceClosedIsFalse = refl
