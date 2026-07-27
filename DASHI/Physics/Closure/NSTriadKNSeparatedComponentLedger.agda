module DASHI.Physics.Closure.NSTriadKNSeparatedComponentLedger where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Terence Tao; Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin;
-- Raphael Danchin; Pierre Germain; Loukas Grafakos; Rodolfo H. Torres;
-- DASHI repository contributors.
-- Title: "Componentwise frozen-leg shell ledger with explicit direct and
-- swapped first-adjoint pieces".
-- Venue/year: UCLA Math 247B lecture notes, 2007; Annales scientifiques de
-- l'Ecole Normale Superieure 14 (1981); Springer Grundlehren 343 (2011);
-- Journal of Differential Equations 226 (2006); Advances in Mathematics 165
-- (2002); DASHI formal development, 2026.
-- DOI: Tao lecture notes have no DOI; 10.24033/asens.1404;
-- 10.1007/978-3-642-16830-7; 10.1016/j.jde.2005.10.007;
-- 10.1006/aima.2001.2028; repository-original component table has no DOI.
-- Uses: one absolute left/right/output-low geometry, frozen-leg rotation, and
-- the literal split T*1_ordered = T*1_direct + T*1_swapped.
-- Relationship: maps every separated component to a small reusable analytic
-- archetype.  It does not claim that each archetype estimate or its uniform
-- constant has already been proved.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNExactDyadicShellGeometry as Geometry

open Geometry using
  (FrozenView; outputView; firstAdjointView; secondAdjointView;
   OrderedPiece; unsplitPiece; directPiece; swappedPiece;
   GeometryTag; leftLowTag; rightLowTag; outputLowTag;
   comparableTag; transitionTag; residualTag)

data DerivativeOwner : Set where
  derivativeLeft derivativeRight derivativeOutput
  derivativeOnLow derivativeOnHigh mixedDerivativeOwner : DerivativeOwner

data AnalyticArchetype : Set where
  lowBernsteinDerivativeHigh
  lowBernsteinDerivativeLow
  highHighFirstAdjointConvolution
  outputRelocationGain
  secondAdjointFrozenLowDerivative
  finiteOverlapMajorant : AnalyticArchetype

record ShellComponent : Set where
  constructor component
  field
    view : FrozenView
    piece : OrderedPiece
    geometry : GeometryTag

open ShellComponent public

componentDerivativeOwner : ShellComponent → DerivativeOwner
componentDerivativeOwner (component outputView unsplitPiece leftLowTag) =
  derivativeOnHigh
componentDerivativeOwner (component outputView unsplitPiece rightLowTag) =
  derivativeOnLow
componentDerivativeOwner (component outputView unsplitPiece outputLowTag) =
  derivativeOnHigh
componentDerivativeOwner (component outputView unsplitPiece comparableTag) =
  derivativeRight
componentDerivativeOwner (component outputView unsplitPiece transitionTag) =
  derivativeRight
componentDerivativeOwner (component outputView unsplitPiece residualTag) =
  derivativeRight

componentDerivativeOwner (component firstAdjointView directPiece leftLowTag) =
  derivativeOnHigh
componentDerivativeOwner (component firstAdjointView directPiece rightLowTag) =
  derivativeOnLow
componentDerivativeOwner (component firstAdjointView directPiece outputLowTag) =
  derivativeOnHigh
componentDerivativeOwner (component firstAdjointView directPiece comparableTag) =
  derivativeRight
componentDerivativeOwner (component firstAdjointView directPiece transitionTag) =
  derivativeRight
componentDerivativeOwner (component firstAdjointView directPiece residualTag) =
  derivativeRight

componentDerivativeOwner (component firstAdjointView swappedPiece leftLowTag) =
  derivativeOnHigh
componentDerivativeOwner (component firstAdjointView swappedPiece rightLowTag) =
  derivativeOnLow
componentDerivativeOwner (component firstAdjointView swappedPiece outputLowTag) =
  derivativeOnHigh
componentDerivativeOwner (component firstAdjointView swappedPiece comparableTag) =
  mixedDerivativeOwner
componentDerivativeOwner (component firstAdjointView swappedPiece transitionTag) =
  mixedDerivativeOwner
componentDerivativeOwner (component firstAdjointView swappedPiece residualTag) =
  mixedDerivativeOwner

componentDerivativeOwner (component secondAdjointView unsplitPiece leftLowTag) =
  derivativeOnHigh
componentDerivativeOwner (component secondAdjointView unsplitPiece rightLowTag) =
  derivativeOnLow
componentDerivativeOwner (component secondAdjointView unsplitPiece outputLowTag) =
  derivativeOnHigh
componentDerivativeOwner (component secondAdjointView unsplitPiece comparableTag) =
  derivativeOutput
componentDerivativeOwner (component secondAdjointView unsplitPiece transitionTag) =
  derivativeOutput
componentDerivativeOwner (component secondAdjointView unsplitPiece residualTag) =
  derivativeOutput

-- Invalid view/piece combinations are deliberately routed to a finite-overlap
-- majorant rather than silently identified with a physical component.
componentDerivativeOwner (component outputView directPiece geometry) =
  mixedDerivativeOwner
componentDerivativeOwner (component outputView swappedPiece geometry) =
  mixedDerivativeOwner
componentDerivativeOwner (component firstAdjointView unsplitPiece geometry) =
  mixedDerivativeOwner
componentDerivativeOwner (component secondAdjointView directPiece geometry) =
  mixedDerivativeOwner
componentDerivativeOwner (component secondAdjointView swappedPiece geometry) =
  mixedDerivativeOwner

componentArchetype : ShellComponent → AnalyticArchetype
componentArchetype (component outputView unsplitPiece leftLowTag) =
  lowBernsteinDerivativeHigh
componentArchetype (component outputView unsplitPiece rightLowTag) =
  lowBernsteinDerivativeLow
componentArchetype (component outputView unsplitPiece outputLowTag) =
  outputRelocationGain

componentArchetype (component firstAdjointView directPiece leftLowTag) =
  highHighFirstAdjointConvolution
componentArchetype (component firstAdjointView directPiece rightLowTag) =
  lowBernsteinDerivativeLow
componentArchetype (component firstAdjointView directPiece outputLowTag) =
  lowBernsteinDerivativeHigh

componentArchetype (component firstAdjointView swappedPiece leftLowTag) =
  highHighFirstAdjointConvolution
componentArchetype (component firstAdjointView swappedPiece rightLowTag) =
  lowBernsteinDerivativeLow
componentArchetype (component firstAdjointView swappedPiece outputLowTag) =
  lowBernsteinDerivativeHigh

componentArchetype (component secondAdjointView unsplitPiece leftLowTag) =
  lowBernsteinDerivativeHigh
componentArchetype (component secondAdjointView unsplitPiece rightLowTag) =
  secondAdjointFrozenLowDerivative
componentArchetype (component secondAdjointView unsplitPiece outputLowTag) =
  lowBernsteinDerivativeHigh

componentArchetype (component view piece comparableTag) = finiteOverlapMajorant
componentArchetype (component view piece transitionTag) = finiteOverlapMajorant
componentArchetype (component view piece residualTag) = finiteOverlapMajorant
componentArchetype (component outputView directPiece geometry) = finiteOverlapMajorant
componentArchetype (component outputView swappedPiece geometry) = finiteOverlapMajorant
componentArchetype (component firstAdjointView unsplitPiece geometry) =
  finiteOverlapMajorant
componentArchetype (component secondAdjointView directPiece geometry) =
  finiteOverlapMajorant
componentArchetype (component secondAdjointView swappedPiece geometry) =
  finiteOverlapMajorant

record ArchetypeEstimatePackage : Set₁ where
  field
    lowHighDerivativeEstimate : Set
    lowLowDerivativeEstimate : Set
    highHighFirstAdjointEstimate : Set
    outputRelocationEstimate : Set
    secondFrozenLowDerivativeEstimate : Set
    finiteOverlapEstimate : Set

    everyEstimateUniformInCutoff : Set
    directAndSwappedConstantsTrackedSeparately : Set

open ArchetypeEstimatePackage public

exactComponentTableDefined : Bool
exactComponentTableDefined = true

exactComponentTableDefinedIsTrue : exactComponentTableDefined ≡ true
exactComponentTableDefinedIsTrue = refl

allSeparatedComponentArchetypesMapped : Bool
allSeparatedComponentArchetypesMapped = true

allSeparatedComponentArchetypesMappedIsTrue :
  allSeparatedComponentArchetypesMapped ≡ true
allSeparatedComponentArchetypesMappedIsTrue = refl

allSeparatedComponentEstimatesClosed : Bool
allSeparatedComponentEstimatesClosed = false

allSeparatedComponentEstimatesClosedIsFalse :
  allSeparatedComponentEstimatesClosed ≡ false
allSeparatedComponentEstimatesClosedIsFalse = refl
