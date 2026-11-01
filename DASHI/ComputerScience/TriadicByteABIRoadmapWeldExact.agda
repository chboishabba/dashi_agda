module DASHI.ComputerScience.TriadicByteABIRoadmapWeldExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Codec.TriadicPAdicCodec as PAdic
import DASHI.ComputerScience.TriadicScalarCompactCodecReferenceExact as Ref
import DASHI.ComputerScience.TriadicFin27Byte256ABIExact as ABI

------------------------------------------------------------------------
-- ROADMAP WELD: THREE-TRIT REFERENCE ABI ↔ EXISTING FIVE-TRIT BYTE CONTRACT
------------------------------------------------------------------------
--
-- The new three-trit reference now has a bounded finite byte-sized carrier.
-- The older p-adic codec already anticipated the same machine boundary via
-- Pack5Contract.  This owner records the shared frontier without pretending
-- that the five-trit executable decoder or any host/device u8 binding is paid.
------------------------------------------------------------------------

record ByteABIRoadmap : Set where
  constructor byte-abi-roadmap
  field
    threeTritReferenceBijectionPaid : Bool
    threeTritFin27IndexPaid : Bool
    threeTritFin256EmbeddingPaid : Bool
    threeTritMachineU8BindingPaid : Bool
    fiveTritBase3CodeExists : Bool
    fiveTritCardinalityFitsByteMathematically : Bool
    fiveTritConcretePack5InstancePaid : Bool
    rustScalarOraclePaid : Bool
    swarRuntimePaid : Bool
    cudaRuntimePaid : Bool
    rocmRuntimePaid : Bool
    crossBackendEquivalencePaid : Bool
    benchmarkPaid : Bool
open ByteABIRoadmap public

currentByteABIRoadmap : ByteABIRoadmap
currentByteABIRoadmap = byte-abi-roadmap
  true true true false
  true true false
  false false false false false false

-- Existing Pack5Contract is retained as the owner of the five-trit executable
-- byte obligation; this weld does not redefine it.
Pack5Obligation : Set₁
Pack5Obligation = PAdic.Pack5Contract

ThreeTritReference : Set
ThreeTritReference = Ref.Encoded3

ThreeTritByteCarrier : Set
ThreeTritByteCarrier = ABI.Byte256

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data Fin256ImpliesRustU8 : Set where
data ThreeTritABIPaysFiveTritDecoder : Set where
data CardinalityFitsByteImpliesPack5Implementation : Set where
data FormalABIImpliesCUDAKernel : Set where

fin256DoesNotCreateRustU8 : Fin256ImpliesRustU8 → ⊥
fin256DoesNotCreateRustU8 ()

threeTritDoesNotPayFiveTrit : ThreeTritABIPaysFiveTritDecoder → ⊥
threeTritDoesNotPayFiveTrit ()

fitDoesNotCreatePack5 : CardinalityFitsByteImpliesPack5Implementation → ⊥
fitDoesNotCreatePack5 ()

formalABIDoesNotCreateCUDA : FormalABIImpliesCUDAKernel → ⊥
formalABIDoesNotCreateCUDA ()
