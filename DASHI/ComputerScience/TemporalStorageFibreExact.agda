module DASHI.ComputerScience.TemporalStorageFibreExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- TIME-INDEXED STORAGE FIBRE
--
-- A machine representation is not treated as a flat word.  At each time there
-- is a storage fibre over addresses, together with one or more heads selecting
-- which cell is presently observed/acted upon.  Binary cells, balanced-trit
-- cells, registers, Jacquard crossings, gates, and later physical material
-- states can instantiate the same carrier.
------------------------------------------------------------------------

record TemporalStorageFibre : Set₁ where
  constructor temporalStorageFibre
  field
    Time : Set
    Address : Set
    Cell : Set
    storageAt : Time → Address → Cell
    readHead : Time → Address

open TemporalStorageFibre public

readAtHead : (fibre : TemporalStorageFibre) → Time fibre → Cell fibre
readAtHead fibre t = storageAt fibre t (readHead fibre t)

record TemporalStorageTrace (fibre : TemporalStorageFibre) : Set₁ where
  constructor temporalStorageTrace
  field
    traceTime : List (Time fibre)
    traceAddress : List (Address fibre)
    traceCell : List (Cell fibre)

open TemporalStorageTrace public

record TemporalRegisterFibre : Set₁ where
  constructor temporalRegisterFibre
  field
    Time : Set
    Register : Set
    Value : Set
    registerAt : Time → Register → Value
    activeRegister : Time → Register

open TemporalRegisterFibre public

readActiveRegister :
  (fibre : TemporalRegisterFibre) →
  TemporalRegisterFibre.Time fibre →
  TemporalRegisterFibre.Value fibre
readActiveRegister fibre t =
  TemporalRegisterFibre.registerAt fibre t
    (TemporalRegisterFibre.activeRegister fibre t)

------------------------------------------------------------------------
-- A representation layer is itself a fibre over a semantic cell value.
------------------------------------------------------------------------

record CellRepresentationFibre (Semantic : Set) : Set₁ where
  constructor cellRepresentationFibre
  field
    PhysicalCell : Set
    encodeCell : Semantic → PhysicalCell
    decodeCell : PhysicalCell → Semantic
    decodeEncodeExact : (value : Semantic) → decodeCell (encodeCell value) ≡ value

open CellRepresentationFibre public

mapStorageRepresentation :
  {Semantic : Set} →
  (representation : CellRepresentationFibre Semantic) →
  (fibre : TemporalStorageFibre) →
  Cell fibre ≡ Semantic →
  Time fibre → Address fibre → PhysicalCell representation
mapStorageRepresentation representation fibre refl t address =
  encodeCell representation (storageAt fibre t address)

record TemporalStorageBoundary : Set where
  constructor temporalStorageBoundary
  field
    representationIsFibreIndexed : Bool
    timeIsExplicitCoordinate : Bool
    headPathIsExplicitCoordinate : Bool
    flatWordAloneDeterminesExecutionHistory : Bool
    physicalMaterialAlreadyClaimed : Bool

canonicalTemporalStorageBoundary : TemporalStorageBoundary
canonicalTemporalStorageBoundary =
  temporalStorageBoundary true true true false false
