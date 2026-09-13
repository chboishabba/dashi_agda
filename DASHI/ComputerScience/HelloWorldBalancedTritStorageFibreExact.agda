module DASHI.ComputerScience.HelloWorldBalancedTritStorageFibreExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.TemporalStorageFibreExact as Storage
import DASHI.ComputerScience.HelloWorldTemporalStorageHyperfibreExact as HelloStorage
import DASHI.Codec.BalancedTritBitFibre as Balanced
import DASHI.Algebra.Trit as Trit

------------------------------------------------------------------------
-- HELLO WORLD BALANCED-TRIT CELL FIBRE
--
-- The serialized trit storage is not flattened into binary.  Each temporal
-- storage cell is lifted into the repo's canonical zero/signed trit fibre.
-- The optional bit view remains merely a presentation of that fibre.
------------------------------------------------------------------------

balancedTritCellRepresentation :
  Storage.CellRepresentationFibre Trit.Trit
balancedTritCellRepresentation =
  Storage.cellRepresentationFibre
    Balanced.TritFibre
    Balanced.encodeFibre
    Balanced.decodeFibre
    Balanced.decode-encode

balancedTritStorageAt : Nat → Nat → Balanced.TritFibre
balancedTritStorageAt t address =
  Storage.encodeCell balancedTritCellRepresentation
    (Storage.storageAt HelloStorage.helloTritStorage t address)

balancedTritReadHead : Nat → Balanced.TritFibre
balancedTritReadHead t =
  balancedTritStorageAt t
    (Storage.readHead HelloStorage.helloTritStorage t)

decodeBalancedHeadExact :
  (t : Nat) →
  Storage.decodeCell balancedTritCellRepresentation (balancedTritReadHead t)
  ≡ Storage.readAtHead HelloStorage.helloTritStorage t
decodeBalancedHeadExact t =
  Storage.decodeEncodeExact balancedTritCellRepresentation
    (Storage.readAtHead HelloStorage.helloTritStorage t)

balancedHead0 : balancedTritReadHead 0 ≡ Balanced.signedFibre Balanced.negativeSign
balancedHead0 = refl

balancedHead1 : balancedTritReadHead 1 ≡ Balanced.zeroFibre
balancedHead1 = refl

balancedHead2 : balancedTritReadHead 2 ≡ Balanced.signedFibre Balanced.positiveSign
balancedHead2 = refl

balancedHead0DecodesToNegative :
  Balanced.decodeFibre (balancedTritReadHead 0) ≡ Trit.neg
balancedHead0DecodesToNegative = refl

balancedHead1DecodesToZero :
  Balanced.decodeFibre (balancedTritReadHead 1) ≡ Trit.zer
balancedHead1DecodesToZero = refl

balancedHead2DecodesToPositive :
  Balanced.decodeFibre (balancedTritReadHead 2) ≡ Trit.pos
balancedHead2DecodesToPositive = refl

------------------------------------------------------------------------
-- Optional support/sign projection.  This is useful for a later binary
-- realization fibre but is explicitly downstream of the balanced-trit cell.
------------------------------------------------------------------------

balancedHeadBitView : Nat → Balanced.BitStreamView
balancedHeadBitView t =
  Balanced.bitStreamView
    (Storage.readAtHead HelloStorage.helloTritStorage t)

record HelloWorldBalancedTritStorageBoundary : Set where
  constructor helloWorldBalancedTritStorageBoundary
  field
    balancedTritIsPrimitiveCellFibreHere : Bool
    bitViewIsDownstreamPresentation : Bool
    temporalHeadPreservesExactTritReadback : Bool
    binaryAndTernaryAreDefinitionallyIdentical : Bool

canonicalHelloWorldBalancedTritStorageBoundary :
  HelloWorldBalancedTritStorageBoundary
canonicalHelloWorldBalancedTritStorageBoundary =
  helloWorldBalancedTritStorageBoundary true true true false
