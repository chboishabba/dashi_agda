module DASHI.Physics.Closure.YM4DFromProductCarrierReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
import DASHI.Physics.Closure.YM4DEmbeddingObstructionReceipt as Obstruction

record YM4DFromProductCarrierReceipt : Setω where
  field
    obstructionReceipt : Obstruction.YM4DEmbeddingObstructionReceipt
    obstructionRecorded : Obstruction.YM4DEmbeddingObstructionReceipt.fourDEmbeddingObstruction obstructionReceipt ≡ true
    productLatticeStatement : String
    productCarrierLatticeDefined : Bool
    productCarrierLatticeDefinedProof : productCarrierLatticeDefined ≡ true
    bulkIsStandardWilsonYM : Bool
    bulkIsStandardWilsonYMProof : bulkIsStandardWilsonYM ≡ true
    carrierAddsExternalBoundaryStructure : Bool
    carrierAddsExternalBoundaryStructureProof : carrierAddsExternalBoundaryStructure ≡ true
    nativeCarrierFourDConstructed : Bool
    nativeCarrierFourDConstructedProof : nativeCarrierFourDConstructed ≡ false
    clayYangMillsPromoted : Bool
    clayYangMillsPromotedProof : clayYangMillsPromoted ≡ false

canonicalYM4DFromProductCarrierReceipt : YM4DFromProductCarrierReceipt
canonicalYM4DFromProductCarrierReceipt =
  record
    { obstructionReceipt = Obstruction.canonicalYM4DEmbeddingObstructionReceipt
    ; obstructionRecorded = refl
    ; productLatticeStatement = "A 4D product carrier lattice is standard Wilson YM with carrier coupling/spacing and three Heegner boundary-source sites."
    ; productCarrierLatticeDefined = true
    ; productCarrierLatticeDefinedProof = refl
    ; bulkIsStandardWilsonYM = true
    ; bulkIsStandardWilsonYMProof = refl
    ; carrierAddsExternalBoundaryStructure = true
    ; carrierAddsExternalBoundaryStructureProof = refl
    ; nativeCarrierFourDConstructed = false
    ; nativeCarrierFourDConstructedProof = refl
    ; clayYangMillsPromoted = false
    ; clayYangMillsPromotedProof = refl
    }
