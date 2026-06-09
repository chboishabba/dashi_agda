module DASHI.Physics.QFT.DHRThermodynamicLimit where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.AQFTCarrierAlgebraQuotientSurface as AQFT
import DASHI.Physics.QFT.DHRSectorDecomposition as DHR
import DASHI.Physics.QFT.DHRThermodynamicLimitBoundary as THLimitBoundary

------------------------------------------------------------------------
-- DHR thermodynamic / inductive-limit boundary.
--
-- The directed-system shape is recorded explicitly here: finite-depth local
-- algebra data, connecting maps, the colimit carrier, and the universal
-- property target already present in the AQFT quotient surface.  The finite
-- repository does not become the infinite limit; it only packages the limit
-- interface.

data DHRThermodynamicLimitStatus : Set where
  thermodynamicLimitRecordedNoPromotion :
    DHRThermodynamicLimitStatus

record DHRThermodynamicLimitBoundary : Setω where
  field
    dhrSectorDecomposition :
      DHR.DHRSectorDecomposition

    typedBoundaryReceipt :
      THLimitBoundary.DHRThermodynamicLimitBoundaryReceipt

    depthFilteredLocalAlgebraSurface :
      AQFT.DepthFilteredLocalAlgebraSurface

    colimitUniversalityReceiptTarget :
      AQFT.ColimitUniversalityReceiptTarget

    depthIndexedFamilyLabel :
      String

    connectingMapLabel :
      String

    colimitObjectLabel :
      String

    universalPropertyLabel :
      String

    thermodynamicLimitPromoted :
      Bool

    thermodynamicLimitPromotedIsFalse :
      thermodynamicLimitPromoted ≡ false

    boundary :
      List String

open DHRThermodynamicLimitBoundary public

canonicalDHRThermodynamicLimitBoundary :
  DHRThermodynamicLimitBoundary
canonicalDHRThermodynamicLimitBoundary =
  record
    { dhrSectorDecomposition =
        DHR.canonicalDHRSectorDecomposition
    ; typedBoundaryReceipt =
        THLimitBoundary.canonicalDHRThermodynamicLimitBoundaryReceipt
    ; depthFilteredLocalAlgebraSurface =
        AQFT.canonicalConcreteDepthFilteredLocalAlgebraSurface
    ; colimitUniversalityReceiptTarget =
        AQFT.canonicalConcreteColimitUniversalityReceiptTarget
    ; depthIndexedFamilyLabel =
        "finite-depth local algebra family"
    ; connectingMapLabel =
        "depth-indexed connecting maps"
    ; colimitObjectLabel =
        "inductive-limit / colimit algebra carrier"
    ; universalPropertyLabel =
        "filtered-colimit universal property"
    ; thermodynamicLimitPromoted =
        false
    ; thermodynamicLimitPromotedIsFalse =
        refl
    ; boundary =
        "The DHR sector decomposition is threaded into the AQFT filtered-colimit surface"
        ∷ "The typed boundary receipt is threaded through as the explicit fail-closed integration surface"
        ∷ "The limit object is recorded as the inductive / colimit algebra carrier, not a finite-stage algebra"
        ∷ "The universal property is imported from the existing AQFT receipt target"
        ∷ "This module does not claim an inhabited infinite-volume theorem"
        ∷ []
    }

record DHRThermodynamicLimitReceipt : Setω where
  field
    boundary :
      DHRThermodynamicLimitBoundary

    dhrSectorDecompositionImported :
      Bool

    dhrSectorDecompositionImportedIsFalse :
      dhrSectorDecompositionImported ≡ false

    depthFilteredLocalAlgebraSurfaceImported :
      Bool

    depthFilteredLocalAlgebraSurfaceImportedIsFalse :
      depthFilteredLocalAlgebraSurfaceImported ≡ false

    colimitUniversalityReceiptTargetImported :
      Bool

    colimitUniversalityReceiptTargetImportedIsFalse :
      colimitUniversalityReceiptTargetImported ≡ false

    thermodynamicLimitStillOpen :
      Bool

    thermodynamicLimitStillOpenIsFalse :
      thermodynamicLimitStillOpen ≡ false

    receiptBoundary :
      List String

open DHRThermodynamicLimitReceipt public

canonicalDHRThermodynamicLimitReceipt :
  DHRThermodynamicLimitReceipt
canonicalDHRThermodynamicLimitReceipt =
  record
    { boundary =
        canonicalDHRThermodynamicLimitBoundary
    ; dhrSectorDecompositionImported =
        false
    ; dhrSectorDecompositionImportedIsFalse =
        refl
    ; depthFilteredLocalAlgebraSurfaceImported =
        false
    ; depthFilteredLocalAlgebraSurfaceImportedIsFalse =
        refl
    ; colimitUniversalityReceiptTargetImported =
        false
    ; colimitUniversalityReceiptTargetImportedIsFalse =
        refl
    ; thermodynamicLimitStillOpen =
        false
    ; thermodynamicLimitStillOpenIsFalse =
        refl
    ; receiptBoundary =
        "The thermodynamic-limit receipt keeps the finite-depth diagram and the colimit target separate"
        ∷ "Connecting maps are recorded as the directed-system interface, not as a claim of completed infinity"
        ∷ "The AQFT universal property is consumed as an existing receipt target"
        ∷ "No promotion of the thermodynamic limit is claimed here"
        ∷ []
    }
