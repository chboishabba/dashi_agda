module DASHI.Foundations.Base369CalculationFibreClosureExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- The nine-sheet is an ordered relational operator.  Running it produces a
-- result fibre carrying origin, proposal, path, completion and open ends.  A
-- vanishing point is relative to a closure operator: further progress requires
-- new information, a new relation, gluing edge, braid, scale or paradigm.
-- The 9+1, 9+2 and 9+3 counts are encoded as minimum interface carriers for
-- orientation, distinction and a complete new ternary axis.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Fin.Base using (Fin)

open import DASHI.Foundations.SSPTritCarrier using (SSPTrit)
import DASHI.Foundations.Base369InteractionAppraisalCubeExact as Cube

record RelationalSheetOperator : Set₁ where
  constructor relationalSheetOperator
  field
    calculate : SSPTrit → SSPTrit → SSPTrit

open RelationalSheetOperator public

record ProvenanceBearingResult
  (operator : RelationalSheetOperator) : Set₁ where
  constructor provenanceBearingResult
  field
    Origin : Set
    Proposal : Set
    Path : Set
    OpenEnd : Set
    origin : Origin
    proposal : Proposal
    inputA : SSPTrit
    inputB : SSPTrit
    path : Path
    output : SSPTrit
    outputExact : output ≡ calculate operator inputA inputB
    openEnds : List OpenEnd

open ProvenanceBearingResult public

record WeavingOperation : Set₁ where
  constructor weavingOperation
  field
    Hyperfabric : Set
    Fibre : Set
    weave : Hyperfabric → Fibre → Hyperfabric

open WeavingOperation public

record GluingOperation : Set₁ where
  constructor gluingOperation
  field
    OpenBoundary : Set
    Connection : Set
    glue : OpenBoundary → OpenBoundary → Connection

open GluingOperation public

------------------------------------------------------------------------
-- Observer-relative closure and vanishing point.
------------------------------------------------------------------------

record ClosureSystem : Set₁ where
  constructor closureSystem
  field
    State : Set
    close : State → State
    idempotent : (state : State) → close (close state) ≡ close state

open ClosureSystem public

record VanishingPoint (system : ClosureSystem) : Set where
  constructor vanishingPoint
  field
    state : State system
    fixed : close system state ≡ state

open VanishingPoint public

record ClosureExtension (system : ClosureSystem) : Set₁ where
  constructor closureExtension
  field
    ExtendedState : Set
    extendedClose : ExtendedState → ExtendedState
    newInformation : Set
    topologyChanged : Set

open ClosureExtension public

------------------------------------------------------------------------
-- Interface thresholds over a completed nine-sheet.
------------------------------------------------------------------------

record OrientedTen : Set where
  constructor orientedTen
  field
    closedSheet : Fin 9
    externalWitness : Fin 1

record DistinguishedEleven : Set where
  constructor distinguishedEleven
  field
    closedSheet : Fin 9
    source : Fin 1
    target : Fin 1

record TernaryExtensionTwelve : Set where
  constructor ternaryExtensionTwelve
  field
    closedSheet : Fin 9
    newAxis : SSPTrit

orientationInterfaceCount : Fin 10 → Fin 10
orientationInterfaceCount x = x

distinctionInterfaceCount : Fin 11 → Fin 11
distinctionInterfaceCount x = x

ternaryExtensionInterfaceCount : Fin 12 → Fin 12
ternaryExtensionInterfaceCount x = x

------------------------------------------------------------------------
-- Ninety and ninety-nine remain interface/address counts.
------------------------------------------------------------------------

record TenByNineSurface : Set where
  constructor tenByNineSurface
  field
    fineBlock : Fin 10
    orderedRelation : Fin 9

record NinetyNineUnintegratedSheet : Set where
  constructor ninetyNineUnintegratedSheet
  field
    establishedSurface : TenByNineSurface
    newUnintegratedSheet : Fin 9

-- Completion closes open boundaries; it does not require every formal cell to
-- be inhabited.  This distinction is represented by an explicit closure
-- witness rather than by cardinal saturation.
record BoundaryComplete (OpenEnd : Set) : Set₁ where
  constructor boundaryComplete
  field
    remainingOpenEnds : List OpenEnd
    closureWitness : Set

open BoundaryComplete public
