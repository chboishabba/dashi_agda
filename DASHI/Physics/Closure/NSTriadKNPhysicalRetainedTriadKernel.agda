module DASHI.Physics.Closure.NSTriadKNPhysicalRetainedTriadKernel where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSTriadKNExactAlgebraicRetainedTriadFiber as Exact

------------------------------------------------------------------------
-- Physical absolute retained-triad kernel.
--
-- This is deliberately scalar-valued.  The legacy concrete relation is a
-- Nat-valued diagonal count proxy, whereas the matrix-free NS construction
-- weights every retained triad by its amplitude and coherence.  This module
-- gives the latter object a direct name, but does not fabricate the finite
-- mode data, retained-sector fiber, or its physical identification.
------------------------------------------------------------------------

data NoRepeatedElements {A : Set} : List A → Set where
  [] : NoRepeatedElements []
  _∷_ : {x : A} {xs : List A} →
    (Exact._∈_ x xs → ⊥) →
    NoRepeatedElements xs →
    NoRepeatedElements (x ∷ xs)

------------------------------------------------------------------------
-- A physical datum owns the actual finite retained fiber.  Its weight is
-- fixed by the exact amplitude/coherence formula already defined in Exact:
--
--   (a_i a_j a_k / 3) · |gamma_tau|.
--
-- Positive and negative channels remain available in Exact; this particular
-- object is the absolute kernel used by the Gram/base-form side of Stage 3.
------------------------------------------------------------------------

record PhysicalAbsoluteRetainedTriadData
    {S : Exact.ExactScalarOperations}
    (surface : Exact.FiniteTriadModeSurface S)
    (profile : Exact.AdmissibleAmplitudeProfile surface)
    (SourceIndex TargetIndex : Exact.FiniteCarrier)
    (sourceIndex :
      Exact.TriadOf surface → Exact.FiniteCarrier.Carrier SourceIndex)
    (targetIndex :
      Exact.TriadOf surface → Exact.FiniteCarrier.Carrier TargetIndex)
    (retainedPositiveSector : Exact.TriadOf surface → Set) : Setω where
  constructor mkPhysicalAbsoluteRetainedTriadData
  field
    fiberInterface :
      Exact.ExactRetainedTriadFiberInterface
        surface profile SourceIndex TargetIndex
        sourceIndex targetIndex retainedPositiveSector

    fiberHasNoSpuriousMultiplicity :
      (f : Exact.FiniteCarrier.Carrier SourceIndex) →
      (t : Exact.FiniteCarrier.Carrier TargetIndex) →
      NoRepeatedElements
        (Exact.ExactRetainedTriadFiberInterface.fiber fiberInterface f t)

open PhysicalAbsoluteRetainedTriadData public

physicalRetainedTriadFiber :
  {S : Exact.ExactScalarOperations} →
  {surface : Exact.FiniteTriadModeSurface S} →
  {profile : Exact.AdmissibleAmplitudeProfile surface} →
  {SourceIndex TargetIndex : Exact.FiniteCarrier} →
  {sourceIndex :
    Exact.TriadOf surface → Exact.FiniteCarrier.Carrier SourceIndex} →
  {targetIndex :
    Exact.TriadOf surface → Exact.FiniteCarrier.Carrier TargetIndex} →
  {retainedPositiveSector : Exact.TriadOf surface → Set} →
  (physicalData : PhysicalAbsoluteRetainedTriadData
    surface profile SourceIndex TargetIndex
    sourceIndex targetIndex retainedPositiveSector) →
  Exact.FiniteCarrier.Carrier SourceIndex →
  Exact.FiniteCarrier.Carrier TargetIndex →
  List (Exact.TriadOf surface)
physicalRetainedTriadFiber physicalData f t =
  Exact.ExactRetainedTriadFiberInterface.fiber
    (fiberInterface physicalData) f t

------------------------------------------------------------------------
-- Fiber audit lemmas: soundness, completeness, finiteness, and exact
-- multiplicity are projections of the physical datum, not new assumptions.
------------------------------------------------------------------------

retainedTriadFiberSound :
  {S : Exact.ExactScalarOperations} →
  {surface : Exact.FiniteTriadModeSurface S} →
  {profile : Exact.AdmissibleAmplitudeProfile surface} →
  {SourceIndex TargetIndex : Exact.FiniteCarrier} →
  {sourceIndex : Exact.TriadOf surface → Exact.FiniteCarrier.Carrier SourceIndex} →
  {targetIndex : Exact.TriadOf surface → Exact.FiniteCarrier.Carrier TargetIndex} →
  {retainedPositiveSector : Exact.TriadOf surface → Set} →
  (physicalData : PhysicalAbsoluteRetainedTriadData surface profile SourceIndex TargetIndex sourceIndex targetIndex retainedPositiveSector) →
  {f : Exact.FiniteCarrier.Carrier SourceIndex} →
  {t : Exact.FiniteCarrier.Carrier TargetIndex} →
  (τ : Exact.TriadOf surface) →
  Exact._∈_ τ (physicalRetainedTriadFiber physicalData f t) →
  sourceIndex τ ≡ f × targetIndex τ ≡ t × retainedPositiveSector τ
retainedTriadFiberSound physicalData τ τ∈fiber =
  Exact.ExactRetainedTriadFiberInterface.fiberSourceAgreement
    (fiberInterface physicalData) τ τ∈fiber ,
  (Exact.ExactRetainedTriadFiberInterface.fiberTargetAgreement
    (fiberInterface physicalData) τ τ∈fiber ,
   Exact.ExactRetainedTriadFiberInterface.fiberRetainedAgreement
    (fiberInterface physicalData) τ τ∈fiber)

retainedTriadFiberComplete :
  {S : Exact.ExactScalarOperations} →
  {surface : Exact.FiniteTriadModeSurface S} →
  {profile : Exact.AdmissibleAmplitudeProfile surface} →
  {SourceIndex TargetIndex : Exact.FiniteCarrier} →
  {sourceIndex : Exact.TriadOf surface → Exact.FiniteCarrier.Carrier SourceIndex} →
  {targetIndex : Exact.TriadOf surface → Exact.FiniteCarrier.Carrier TargetIndex} →
  {retainedPositiveSector : Exact.TriadOf surface → Set} →
  (physicalData : PhysicalAbsoluteRetainedTriadData surface profile SourceIndex TargetIndex sourceIndex targetIndex retainedPositiveSector) →
  {f : Exact.FiniteCarrier.Carrier SourceIndex} →
  {t : Exact.FiniteCarrier.Carrier TargetIndex} →
  (τ : Exact.TriadOf surface) →
  sourceIndex τ ≡ f → targetIndex τ ≡ t → retainedPositiveSector τ →
  Exact._∈_ τ (physicalRetainedTriadFiber physicalData f t)
retainedTriadFiberComplete physicalData τ source≡ target≡ retained =
  Exact.ExactRetainedTriadFiberInterface.triadToFiber
    (fiberInterface physicalData) τ source≡ target≡ retained

retainedTriadFiberFinite :
  {S : Exact.ExactScalarOperations} →
  {surface : Exact.FiniteTriadModeSurface S} →
  {profile : Exact.AdmissibleAmplitudeProfile surface} →
  {SourceIndex TargetIndex : Exact.FiniteCarrier} →
  {sourceIndex : Exact.TriadOf surface → Exact.FiniteCarrier.Carrier SourceIndex} →
  {targetIndex : Exact.TriadOf surface → Exact.FiniteCarrier.Carrier TargetIndex} →
  {retainedPositiveSector : Exact.TriadOf surface → Set} →
  (physicalData : PhysicalAbsoluteRetainedTriadData surface profile SourceIndex TargetIndex sourceIndex targetIndex retainedPositiveSector) →
  (f : Exact.FiniteCarrier.Carrier SourceIndex) →
  (t : Exact.FiniteCarrier.Carrier TargetIndex) →
  List (Exact.TriadOf surface)
retainedTriadFiberFinite = physicalRetainedTriadFiber

retainedTriadFiberNoSpuriousMultiplicity :
  {S : Exact.ExactScalarOperations} →
  {surface : Exact.FiniteTriadModeSurface S} →
  {profile : Exact.AdmissibleAmplitudeProfile surface} →
  {SourceIndex TargetIndex : Exact.FiniteCarrier} →
  {sourceIndex : Exact.TriadOf surface → Exact.FiniteCarrier.Carrier SourceIndex} →
  {targetIndex : Exact.TriadOf surface → Exact.FiniteCarrier.Carrier TargetIndex} →
  {retainedPositiveSector : Exact.TriadOf surface → Set} →
  (physicalData : PhysicalAbsoluteRetainedTriadData surface profile SourceIndex TargetIndex sourceIndex targetIndex retainedPositiveSector) →
  (f : Exact.FiniteCarrier.Carrier SourceIndex) →
  (t : Exact.FiniteCarrier.Carrier TargetIndex) →
  NoRepeatedElements (physicalRetainedTriadFiber physicalData f t)
retainedTriadFiberNoSpuriousMultiplicity physicalData =
  fiberHasNoSpuriousMultiplicity physicalData

------------------------------------------------------------------------
-- The actual scalar kernel is defined from the physical weighted fiber;
-- consequently the central formula is a theorem, not a receipt.  It remains
-- conditional on a physical datum, whose construction is the live work.
------------------------------------------------------------------------

physicalAbsolutePairIncidenceKernel :
  {S : Exact.ExactScalarOperations} →
  {surface : Exact.FiniteTriadModeSurface S} →
  {profile : Exact.AdmissibleAmplitudeProfile surface} →
  {SourceIndex TargetIndex : Exact.FiniteCarrier} →
  {sourceIndex : Exact.TriadOf surface → Exact.FiniteCarrier.Carrier SourceIndex} →
  {targetIndex : Exact.TriadOf surface → Exact.FiniteCarrier.Carrier TargetIndex} →
  {retainedPositiveSector : Exact.TriadOf surface → Set} →
  (physicalData : PhysicalAbsoluteRetainedTriadData surface profile SourceIndex TargetIndex sourceIndex targetIndex retainedPositiveSector) →
  Exact.FiniteCarrier.Carrier SourceIndex →
  Exact.FiniteCarrier.Carrier TargetIndex →
  Exact.ExactScalarOperations.Carrier S
physicalAbsolutePairIncidenceKernel {S = S} physicalData f t =
  Exact.weightedListSum {S = S}
    (Exact.ExactRetainedTriadFiberInterface.triadWeight (fiberInterface physicalData))
    (physicalRetainedTriadFiber physicalData f t)

physicalKernelEqualsWeightedFiberFold :
  {S : Exact.ExactScalarOperations} →
  {surface : Exact.FiniteTriadModeSurface S} →
  {profile : Exact.AdmissibleAmplitudeProfile surface} →
  {SourceIndex TargetIndex : Exact.FiniteCarrier} →
  {sourceIndex : Exact.TriadOf surface → Exact.FiniteCarrier.Carrier SourceIndex} →
  {targetIndex : Exact.TriadOf surface → Exact.FiniteCarrier.Carrier TargetIndex} →
  {retainedPositiveSector : Exact.TriadOf surface → Set} →
  (physicalData : PhysicalAbsoluteRetainedTriadData surface profile SourceIndex TargetIndex sourceIndex targetIndex retainedPositiveSector) →
  (f : Exact.FiniteCarrier.Carrier SourceIndex) →
  (t : Exact.FiniteCarrier.Carrier TargetIndex) →
  physicalAbsolutePairIncidenceKernel physicalData f t ≡
  Exact.weightedListSum {S = S}
    (Exact.ExactRetainedTriadFiberInterface.triadWeight (fiberInterface physicalData))
    (physicalRetainedTriadFiber physicalData f t)
physicalKernelEqualsWeightedFiberFold {S = S} physicalData f t = refl

physicalFiberWeightIsAbsoluteTriadWeight :
  {S : Exact.ExactScalarOperations} →
  {surface : Exact.FiniteTriadModeSurface S} →
  {profile : Exact.AdmissibleAmplitudeProfile surface} →
  {SourceIndex TargetIndex : Exact.FiniteCarrier} →
  {sourceIndex : Exact.TriadOf surface → Exact.FiniteCarrier.Carrier SourceIndex} →
  {targetIndex : Exact.TriadOf surface → Exact.FiniteCarrier.Carrier TargetIndex} →
  {retainedPositiveSector : Exact.TriadOf surface → Set} →
  (physicalData : PhysicalAbsoluteRetainedTriadData surface profile SourceIndex TargetIndex sourceIndex targetIndex retainedPositiveSector) →
  (τ : Exact.TriadOf surface) →
  Exact.ExactRetainedTriadFiberInterface.triadWeight (fiberInterface physicalData) τ ≡
  Exact.triadAbsoluteWeight profile τ
physicalFiberWeightIsAbsoluteTriadWeight physicalData τ =
  Exact.ExactRetainedTriadFiberInterface.triadWeightFormula
    (fiberInterface physicalData) τ

------------------------------------------------------------------------
-- No canonical physical datum is supplied.  The diagnostic Nat count kernel
-- cannot inhabit this type without concrete scalar weights and fiber proofs.
------------------------------------------------------------------------

physicalRetainedTriadKernelClosed : Bool
physicalRetainedTriadKernelClosed = false

physicalRetainedTriadKernelClosedIsFalse :
  physicalRetainedTriadKernelClosed ≡ false
physicalRetainedTriadKernelClosedIsFalse = refl
