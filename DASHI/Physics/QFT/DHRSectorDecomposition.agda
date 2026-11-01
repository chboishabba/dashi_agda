module DASHI.Physics.QFT.DHRSectorDecomposition where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.AQFTCarrierAlgebraQuotientSurface as AQFTColim
import DASHI.Physics.SFGC.NonAbelian.CliffordToM2Iso as CliffordM2
import DASHI.Physics.SFGC.NonAbelian.DepthQuotientIso as DepthQuotient
open import DASHI.Physics.SFGC.NonAbelian.DepthQuotientIsoSU3 using
  (DepthQuotientIsoSU3Witness; canonicalDepthQuotientIsoSU3Witness)
import DASHI.Physics.SFGC.NonAbelian.GradedSFGCSite2D as Graded
import DASHI.Physics.SFGC.NonAbelian.NonAbelianSFGCCarrier as Carrier
import DASHI.Physics.SFGC.NonAbelian.SU3ColorSectorNote as SU3

------------------------------------------------------------------------
-- DHR sector decomposition bridge.
--
-- The module is concrete where the repo already provides finite witnesses:
-- the graded 7/11/13 lane witness, the nonabelian SFGC carrier bundle,
-- the Clifford-even/M2 bridge, and the SU(3) route note.
--
-- It is honest about the remaining frontier: the exact Standard Model carrier
-- matching obstruction remains available only as the existing blocker value.

data DHRGaugeSectorAtom : Set where
  U1Sector :
    DHRGaugeSectorAtom

  SU2Sector :
    DHRGaugeSectorAtom

  SU3Frontier :
    DHRGaugeSectorAtom

canonicalDHRGaugeSectorAtoms :
  List DHRGaugeSectorAtom
canonicalDHRGaugeSectorAtoms =
  U1Sector
  ∷ SU2Sector
  ∷ SU3Frontier
  ∷ []

record U1SectorObject : Set₁ where
  field
    sectorKind :
      DHRGaugeSectorAtom

    gradedWitness :
      Graded.GradedSFGCSite2DWitness

    sectorBoundary :
      List String

open U1SectorObject public

canonicalU1SectorObject : U1SectorObject
canonicalU1SectorObject =
  record
    { sectorKind = U1Sector
    ; gradedWitness = Graded.canonicalGradedSFGCSite2DWitness
    ; sectorBoundary =
        "U(1) side is recorded as the canonical graded 7/11/13 witness"
        ∷ "This is an upstream decomposition bundle, not a proof of the full DHR sector carrier"
        ∷ []
    }

record SU2SectorObject : Set₁ where
  field
    sectorKind :
      DHRGaugeSectorAtom

    nonabelianCarrierWitness :
      Carrier.NonAbelianSFGCCarrierWitness

    depthQuotientWitness :
      DepthQuotient.DepthQuotientWitness

    cliffordM2Iso :
      CliffordM2.CliffordM2BasisIso

    sectorBoundary :
      List String

open SU2SectorObject public

canonicalSU2SectorObject : SU2SectorObject
canonicalSU2SectorObject =
  record
    { sectorKind = SU2Sector
    ; nonabelianCarrierWitness = Carrier.canonicalNonAbelianSFGCCarrierWitness
    ; depthQuotientWitness = DepthQuotient.canonicalDepthQuotientWitness
    ; cliffordM2Iso = CliffordM2.canonicalCliffordM2BasisIso
    ; sectorBoundary =
        "SU(2) side is recorded as the canonical nonabelian carrier bundle"
        ∷ "The depth quotient and Clifford-to-M2 bridge are explicit finite witnesses"
        ∷ []
    }

record SU3FrontierObject : Setω where
  field
    sectorKind :
      DHRGaugeSectorAtom

    rho3Witness :
      DepthQuotientIsoSU3Witness

    exactStandardModelCarrierFunctorMatchBlockerName :
      String

    sectorBoundary :
      List String

open SU3FrontierObject public

canonicalSU3FrontierObject : SU3FrontierObject
canonicalSU3FrontierObject =
  record
    { sectorKind = SU3Frontier
    ; rho3Witness = canonicalDepthQuotientIsoSU3Witness
    ; exactStandardModelCarrierFunctorMatchBlockerName =
        "missingExactStandardModelCarrierFunctorMatch"
    ; sectorBoundary =
        "SU(3) is recorded as a concrete rho3 depth-quotient witness plus a frontier blocker"
        ∷ "The rho3 witness packages the canonical SU(3) route note and W3/M3 bridge"
        ∷ "The exact Standard Model carrier-functor match remains missingExactStandardModelCarrierFunctorMatch"
        ∷ []
    }

record DHRSectorCompatibilityWitness : Set₁ where
  field
    gate1SectorBoundaryName :
      String

    gate1CompatibilityPrimitiveWitnessName :
      String

    aqftLocalAlgebraFrontierName :
      String

    compatibilityBoundary :
      List String

open DHRSectorCompatibilityWitness public

canonicalDHRSectorCompatibilityWitness :
  DHRSectorCompatibilityWitness
canonicalDHRSectorCompatibilityWitness =
  record
    { gate1SectorBoundaryName = "dhrSectorBoundaryRecordedOnly"
    ; gate1CompatibilityPrimitiveWitnessName =
        "missingDHRSectorCompatibilityPrimitiveWitness"
    ; aqftLocalAlgebraFrontierName = "missingDASHILocalAlgebra"
    ; compatibilityBoundary =
        "Gate 1 compatibility is the canonical missingDHRSectorCompatibility primitive witness"
        ∷ "Gate 6 agreement remains the exact Standard Model carrier-functor match obstruction"
        ∷ "The AQFT local-algebra frontier is recorded as missingDASHILocalAlgebra"
        ∷ []
    }

record DHRSectorDecomposition : Setω where
  field
    u1SectorObject :
      U1SectorObject

    su2SectorObject :
      SU2SectorObject

    su3FrontierObject :
      SU3FrontierObject

    compatibilityWitness :
      DHRSectorCompatibilityWitness

    sectorDecompositionPromoted :
      Bool

    sectorDecompositionPromotedIsFalse :
      sectorDecompositionPromoted ≡ false

    decompositionBoundary :
      List String

open DHRSectorDecomposition public

canonicalDHRSectorDecomposition :
  DHRSectorDecomposition
canonicalDHRSectorDecomposition =
  record
    { u1SectorObject = canonicalU1SectorObject
    ; su2SectorObject = canonicalSU2SectorObject
    ; su3FrontierObject = canonicalSU3FrontierObject
    ; compatibilityWitness = canonicalDHRSectorCompatibilityWitness
    ; sectorDecompositionPromoted = false
    ; sectorDecompositionPromotedIsFalse = refl
    ; decompositionBoundary =
        "Concrete DHR sector decomposition packs the canonical graded witness"
        ∷ "It also packages the nonabelian carrier bundle and the concrete SU(3) rho3 witness"
        ∷ "Gate 1 compatibility is carried by the canonical missingDHRSectorCompatibility primitive witness"
        ∷ "Gate 6 remains blocked by missingExactStandardModelCarrierFunctorMatch"
        ∷ []
    }

dhrSectorDecompositionWitness :
  DHRSectorDecomposition
dhrSectorDecompositionWitness = canonicalDHRSectorDecomposition

dhrSectorDecompositionBoundary :
  List String
dhrSectorDecompositionBoundary =
  "DHR sector decomposition is concrete on the existing graded/nonabelian/rho3 witnesses"
  ∷ "The exact Standard Model carrier-functor match is still an explicit frontier blocker"
  ∷ []
