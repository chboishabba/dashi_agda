module DASHI.Quantum.GNSUniversalProperty where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.ModularTheoryReceiptSurface as Modular

-- Concrete GNS-style witness packaged from the canonical modular receipts.
-- The module stays upstream of Stone so it can be imported without creating an
-- import cycle through the current Stone front.

record GNSUniversalPropertyWitness : Setω where
  field
    gnsHilbertReceipt :
      Modular.GNSHilbertRepresentationReceipt
        Modular.abstractRegion
        Modular.abstractStateFunctional
        Modular.abstractGNSNullIdeal
        Modular.abstractGNSPreHilbertQuotient

    gnsUniversalReceipt :
      Modular.GNSUniversalPropertyReceipt
        Modular.abstractRegion
        Modular.abstractStateFunctional
        Modular.abstractGNSNullIdeal
        Modular.abstractGNSPreHilbertQuotient
        Modular.abstractGNSHilbertSpace
        Modular.abstractGNSRepresentation

    witnessBoundary :
      List String

open GNSUniversalPropertyWitness public

canonicalGNSUniversalPropertyWitness : GNSUniversalPropertyWitness
canonicalGNSUniversalPropertyWitness =
  record
    { gnsHilbertReceipt =
        Modular.canonicalGNSHilbertRepresentationReceipt
    ; gnsUniversalReceipt =
        Modular.canonicalGNSUniversalPropertyReceipt
    ; witnessBoundary =
        "GNSUniversalProperty packages the canonical modular GNS receipts"
        ∷ "The upstream receipt is concrete and does not import Stone"
        ∷ "This is a packaging module, not a promoted universal-property theorem"
        ∷ []
    }

gnsUniversalPropertyBoundary : List String
gnsUniversalPropertyBoundary =
  "GNSUniversalProperty packages the canonical Modular GNS receipts upstream of Stone"
  ∷ "No cycle with Stone is introduced"
  ∷ []
