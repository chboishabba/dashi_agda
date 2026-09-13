module DASHI.ComputerScience.TriadicFin27Byte256ABIExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin; zero; suc; inject+)

import DASHI.ComputerScience.TriadicScalarCompactCodecReferenceExact as Ref

------------------------------------------------------------------------
-- BOUNDED NUMERIC ABI FOR THE 27-STATE REFERENCE CODEC
--
-- Fin 27 is the canonical dense index of the complete Encoded3 carrier.
-- Fin 256 is a byte-sized finite carrier.  The first 27 byte values are
-- assigned to codec states; values 27..255 remain reserved/invalid here.
--
-- This pays a bounded numeric ABI.  It is still not a claim that an Agda
-- Fin value is already a Rust u8, CUDA uint8_t, device register, or measured
-- machine representation.
------------------------------------------------------------------------

State27 : Set
State27 = Fin 27

Byte256 : Set
Byte256 = Fin 256

------------------------------------------------------------------------
-- Dense index of all 27 well-formed compact states.
------------------------------------------------------------------------

stateCode : Ref.Encoded3 → State27
stateCode Ref.enc000 = zero
stateCode (Ref.enc001 Ref.MaskSign.negative) = suc zero
stateCode (Ref.enc001 Ref.MaskSign.positive) = suc (suc zero)
stateCode (Ref.enc010 Ref.MaskSign.negative) = suc (suc (suc zero))
stateCode (Ref.enc010 Ref.MaskSign.positive) = suc (suc (suc (suc zero)))
stateCode (Ref.enc011 Ref.MaskSign.negative Ref.MaskSign.negative) = suc (suc (suc (suc (suc zero))))
stateCode (Ref.enc011 Ref.MaskSign.negative Ref.MaskSign.positive) = suc (suc (suc (suc (suc (suc zero)))))
stateCode (Ref.enc011 Ref.MaskSign.positive Ref.MaskSign.negative) = suc (suc (suc (suc (suc (suc (suc zero))))))
stateCode (Ref.enc011 Ref.MaskSign.positive Ref.MaskSign.positive) = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
stateCode (Ref.enc100 Ref.MaskSign.negative) = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
stateCode (Ref.enc100 Ref.MaskSign.positive) = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
stateCode (Ref.enc101 Ref.MaskSign.negative Ref.MaskSign.negative) = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
stateCode (Ref.enc101 Ref.MaskSign.negative Ref.MaskSign.positive) = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
stateCode (Ref.enc101 Ref.MaskSign.positive Ref.MaskSign.negative) = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))
stateCode (Ref.enc101 Ref.MaskSign.positive Ref.MaskSign.positive) = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))
stateCode (Ref.enc110 Ref.MaskSign.negative Ref.MaskSign.negative) = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))
stateCode (Ref.enc110 Ref.MaskSign.negative Ref.MaskSign.positive) = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))
stateCode (Ref.enc110 Ref.MaskSign.positive Ref.MaskSign.negative) = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))
stateCode (Ref.enc110 Ref.MaskSign.positive Ref.MaskSign.positive) = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))
stateCode (Ref.enc111 Ref.MaskSign.negative Ref.MaskSign.negative Ref.MaskSign.negative) = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))
stateCode (Ref.enc111 Ref.MaskSign.negative Ref.MaskSign.negative Ref.MaskSign.positive) = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))
stateCode (Ref.enc111 Ref.MaskSign.negative Ref.MaskSign.positive Ref.MaskSign.negative) = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))
stateCode (Ref.enc111 Ref.MaskSign.negative Ref.MaskSign.positive Ref.MaskSign.positive) = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))
stateCode (Ref.enc111 Ref.MaskSign.positive Ref.MaskSign.negative Ref.MaskSign.negative) = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))
stateCode (Ref.enc111 Ref.MaskSign.positive Ref.MaskSign.negative Ref.MaskSign.positive) = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))
stateCode (Ref.enc111 Ref.MaskSign.positive Ref.MaskSign.positive Ref.MaskSign.negative) = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))
stateCode (Ref.enc111 Ref.MaskSign.positive Ref.MaskSign.positive Ref.MaskSign.positive) = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))

------------------------------------------------------------------------
-- Decode the dense finite state index.
------------------------------------------------------------------------

stateDecode : State27 → Ref.Encoded3
stateDecode zero = Ref.enc000
stateDecode (suc zero) = Ref.enc001 Ref.MaskSign.negative
stateDecode (suc (suc zero)) = Ref.enc001 Ref.MaskSign.positive
stateDecode (suc (suc (suc zero))) = Ref.enc010 Ref.MaskSign.negative
stateDecode (suc (suc (suc (suc zero)))) = Ref.enc010 Ref.MaskSign.positive
stateDecode (suc (suc (suc (suc (suc zero))))) = Ref.enc011 Ref.MaskSign.negative Ref.MaskSign.negative
stateDecode (suc (suc (suc (suc (suc (suc zero)))))) = Ref.enc011 Ref.MaskSign.negative Ref.MaskSign.positive
stateDecode (suc (suc (suc (suc (suc (suc (suc zero))))))) = Ref.enc011 Ref.MaskSign.positive Ref.MaskSign.negative
stateDecode (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = Ref.enc011 Ref.MaskSign.positive Ref.MaskSign.positive
stateDecode (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = Ref.enc100 Ref.MaskSign.negative
stateDecode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) = Ref.enc100 Ref.MaskSign.positive
stateDecode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) = Ref.enc101 Ref.MaskSign.negative Ref.MaskSign.negative
stateDecode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) = Ref.enc101 Ref.MaskSign.negative Ref.MaskSign.positive
stateDecode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))) = Ref.enc101 Ref.MaskSign.positive Ref.MaskSign.negative
stateDecode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))) = Ref.enc101 Ref.MaskSign.positive Ref.MaskSign.positive
stateDecode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))) = Ref.enc110 Ref.MaskSign.negative Ref.MaskSign.negative
stateDecode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))) = Ref.enc110 Ref.MaskSign.negative Ref.MaskSign.positive
stateDecode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))) = Ref.enc110 Ref.MaskSign.positive Ref.MaskSign.negative
stateDecode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))) = Ref.enc110 Ref.MaskSign.positive Ref.MaskSign.positive
stateDecode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))) = Ref.enc111 Ref.MaskSign.negative Ref.MaskSign.negative Ref.MaskSign.negative
stateDecode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))) = Ref.enc111 Ref.MaskSign.negative Ref.MaskSign.negative Ref.MaskSign.positive
stateDecode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))) = Ref.enc111 Ref.MaskSign.negative Ref.MaskSign.positive Ref.MaskSign.negative
stateDecode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))) = Ref.enc111 Ref.MaskSign.negative Ref.MaskSign.positive Ref.MaskSign.positive
stateDecode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))) = Ref.enc111 Ref.MaskSign.positive Ref.MaskSign.negative Ref.MaskSign.negative
stateDecode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))) = Ref.enc111 Ref.MaskSign.positive Ref.MaskSign.negative Ref.MaskSign.positive
stateDecode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))) = Ref.enc111 Ref.MaskSign.positive Ref.MaskSign.positive Ref.MaskSign.negative
stateDecode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))) = Ref.enc111 Ref.MaskSign.positive Ref.MaskSign.positive Ref.MaskSign.positive

stateDecode-stateCode : (e : Ref.Encoded3) → stateDecode (stateCode e) ≡ e
stateDecode-stateCode Ref.enc000 = refl
stateDecode-stateCode (Ref.enc001 Ref.MaskSign.negative) = refl
stateDecode-stateCode (Ref.enc001 Ref.MaskSign.positive) = refl
stateDecode-stateCode (Ref.enc010 Ref.MaskSign.negative) = refl
stateDecode-stateCode (Ref.enc010 Ref.MaskSign.positive) = refl
stateDecode-stateCode (Ref.enc011 Ref.MaskSign.negative Ref.MaskSign.negative) = refl
stateDecode-stateCode (Ref.enc011 Ref.MaskSign.negative Ref.MaskSign.positive) = refl
stateDecode-stateCode (Ref.enc011 Ref.MaskSign.positive Ref.MaskSign.negative) = refl
stateDecode-stateCode (Ref.enc011 Ref.MaskSign.positive Ref.MaskSign.positive) = refl
stateDecode-stateCode (Ref.enc100 Ref.MaskSign.negative) = refl
stateDecode-stateCode (Ref.enc100 Ref.MaskSign.positive) = refl
stateDecode-stateCode (Ref.enc101 Ref.MaskSign.negative Ref.MaskSign.negative) = refl
stateDecode-stateCode (Ref.enc101 Ref.MaskSign.negative Ref.MaskSign.positive) = refl
stateDecode-stateCode (Ref.enc101 Ref.MaskSign.positive Ref.MaskSign.negative) = refl
stateDecode-stateCode (Ref.enc101 Ref.MaskSign.positive Ref.MaskSign.positive) = refl
stateDecode-stateCode (Ref.enc110 Ref.MaskSign.negative Ref.MaskSign.negative) = refl
stateDecode-stateCode (Ref.enc110 Ref.MaskSign.negative Ref.MaskSign.positive) = refl
stateDecode-stateCode (Ref.enc110 Ref.MaskSign.positive Ref.MaskSign.negative) = refl
stateDecode-stateCode (Ref.enc110 Ref.MaskSign.positive Ref.MaskSign.positive) = refl
stateDecode-stateCode (Ref.enc111 Ref.MaskSign.negative Ref.MaskSign.negative Ref.MaskSign.negative) = refl
stateDecode-stateCode (Ref.enc111 Ref.MaskSign.negative Ref.MaskSign.negative Ref.MaskSign.positive) = refl
stateDecode-stateCode (Ref.enc111 Ref.MaskSign.negative Ref.MaskSign.positive Ref.MaskSign.negative) = refl
stateDecode-stateCode (Ref.enc111 Ref.MaskSign.negative Ref.MaskSign.positive Ref.MaskSign.positive) = refl
stateDecode-stateCode (Ref.enc111 Ref.MaskSign.positive Ref.MaskSign.negative Ref.MaskSign.negative) = refl
stateDecode-stateCode (Ref.enc111 Ref.MaskSign.positive Ref.MaskSign.negative Ref.MaskSign.positive) = refl
stateDecode-stateCode (Ref.enc111 Ref.MaskSign.positive Ref.MaskSign.positive Ref.MaskSign.negative) = refl
stateDecode-stateCode (Ref.enc111 Ref.MaskSign.positive Ref.MaskSign.positive Ref.MaskSign.positive) = refl

------------------------------------------------------------------------
-- Byte-sized embedding.  The 229 upper values are intentionally reserved.
------------------------------------------------------------------------

stateToByte : State27 → Byte256
stateToByte = inject+ 229

encodeByte3 : Ref.Encoded3 → Byte256
encodeByte3 = stateToByte ∘ stateCode

record TriadicByteABIBoundary : Set where
  constructor triadic-byte-abi-boundary
  field
    finite27StateIndexPaid : Bool
    byteSizedFiniteCarrierPaid : Bool
    injectiveLow27AssignmentPaid : Bool
    referenceEncodeToBytePaid : Bool
    reservedByteRegionRetained : Bool
    totalByteDecoderPaid : Bool
    rustU8BindingPaid : Bool
    cudaUint8BindingPaid : Bool
    rocmUint8BindingPaid : Bool
    machineEndiannessRelevantHere : Bool
    measuredRuntimePaid : Bool
open TriadicByteABIBoundary public

canonicalTriadicByteABIBoundary : TriadicByteABIBoundary
canonicalTriadicByteABIBoundary = triadic-byte-abi-boundary
  true true true true true false false false false false false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data Fin256ImpliesMachineByte : Set where
data Low27EmbeddingImpliesTotalByteDecoder : Set where
data BoundedABIImpliesRustImplementation : Set where
data SameNumericByteImpliesSameDeviceRepresentation : Set where

fin256DoesNotCreateMachineByte : Fin256ImpliesMachineByte → ⊥
fin256DoesNotCreateMachineByte ()

embeddingDoesNotCreateTotalDecoder : Low27EmbeddingImpliesTotalByteDecoder → ⊥
embeddingDoesNotCreateTotalDecoder ()

abiDoesNotCreateRust : BoundedABIImpliesRustImplementation → ⊥
abiDoesNotCreateRust ()

sameNumericByteDoesNotFixDeviceRepresentation :
  SameNumericByteImpliesSameDeviceRepresentation → ⊥
sameNumericByteDoesNotFixDeviceRepresentation ()
