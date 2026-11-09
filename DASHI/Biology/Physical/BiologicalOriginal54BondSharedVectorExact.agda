module DASHI.Biology.Physical.BiologicalOriginal54BondSharedVectorExact where

-- ORIGINAL 3x3x3 GEOMETRY WELD: all 27 actual Ternary27Point
-- constructors bijectively indexed by Fin 27; all 54 native positive
-- nearest-neighbour bonds are sent to distinct shared vector sites.
-- This is a concrete geometry instance of the universal shared-state
-- finite-volume conservation theorem, not an abstract assumed map.
--
-- Transfer is one exact integer material quantum; rates, charge signs,
-- source-specific BH4 permeability and full PNP still remain separate.

open import DASHI.Core.Prelude
import Data.Fin.Base as F
import Data.Vec.Base as V
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Biology.Physical.BiologicalFullCubeIncidenceExact as Grid
import DASHI.Biology.Physical.BiologicalSharedFiniteVectorTransferExact as Transfer

originalPointIndex : Cube.Ternary27Point → F.Fin 27
originalPointIndex (Cube.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne) = F.zero
originalPointIndex (Cube.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspZero) = F.suc (F.zero)
originalPointIndex (Cube.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne) = F.suc (F.suc (F.zero))
originalPointIndex (Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspNegOne) = F.suc (F.suc (F.suc (F.zero)))
originalPointIndex (Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero) = F.suc (F.suc (F.suc (F.suc (F.zero))))
originalPointIndex (Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspPosOne) = F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))
originalPointIndex (Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne) = F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))
originalPointIndex (Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspZero) = F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))
originalPointIndex (Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne) = F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))
originalPointIndex (Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspNegOne) = F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))
originalPointIndex (Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero) = F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))
originalPointIndex (Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspPosOne) = F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))))
originalPointIndex (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspNegOne) = F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))
originalPointIndex (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero) = F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))))))
originalPointIndex (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne) = F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))))
originalPointIndex (Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspNegOne) = F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))))))))
originalPointIndex (Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero) = F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))))))
originalPointIndex (Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspPosOne) = F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))))))))))
originalPointIndex (Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne) = F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))))))))
originalPointIndex (Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero) = F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))))))))))))
originalPointIndex (Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne) = F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))))))))))
originalPointIndex (Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspNegOne) = F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))))))))))))))
originalPointIndex (Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero) = F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))))))))))))
originalPointIndex (Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspPosOne) = F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))))))))))))))))
originalPointIndex (Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne) = F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))))))))))))))
originalPointIndex (Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspZero) = F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))))))))))))))))))
originalPointIndex (Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne) = F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))))))))))))))))

originalPointAtIndex : F.Fin 27 → Cube.Ternary27Point
originalPointAtIndex (F.zero) = Cube.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne
originalPointAtIndex (F.suc (F.zero)) = Cube.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspZero
originalPointAtIndex (F.suc (F.suc (F.zero))) = Cube.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne
originalPointAtIndex (F.suc (F.suc (F.suc (F.zero)))) = Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspNegOne
originalPointAtIndex (F.suc (F.suc (F.suc (F.suc (F.zero))))) = Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero
originalPointAtIndex (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))) = Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspPosOne
originalPointAtIndex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))) = Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne
originalPointAtIndex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))) = Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspZero
originalPointAtIndex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))) = Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne
originalPointAtIndex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))) = Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspNegOne
originalPointAtIndex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))) = Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero
originalPointAtIndex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))))) = Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspPosOne
originalPointAtIndex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))) = Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspNegOne
originalPointAtIndex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))))))) = Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero
originalPointAtIndex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))))) = Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne
originalPointAtIndex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))))))))) = Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspNegOne
originalPointAtIndex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))))))) = Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero
originalPointAtIndex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))))))))))) = Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspPosOne
originalPointAtIndex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))))))))) = Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne
originalPointAtIndex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))))))))))))) = Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero
originalPointAtIndex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))))))))))) = Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne
originalPointAtIndex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))))))))))))))) = Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspNegOne
originalPointAtIndex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))))))))))))) = Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero
originalPointAtIndex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))))))))))))))))) = Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspPosOne
originalPointAtIndex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))))))))))))))) = Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne
originalPointAtIndex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))))))))))))))))))) = Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspZero
originalPointAtIndex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))))))))))))))))) = Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne

originalPointRoundTrip :
  (p : Cube.Ternary27Point) →
  originalPointAtIndex (originalPointIndex p) ≡ p
originalPointRoundTrip (Cube.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspZero) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspNegOne) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspPosOne) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspZero) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspNegOne) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspPosOne) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspNegOne) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspNegOne) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspPosOne) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspNegOne) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspPosOne) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspZero) = refl
originalPointRoundTrip (Cube.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne) = refl

originalIndexRoundTrip :
  (i : F.Fin 27) →
  originalPointIndex (originalPointAtIndex i) ≡ i
originalIndexRoundTrip (F.zero) = refl
originalIndexRoundTrip (F.suc (F.zero)) = refl
originalIndexRoundTrip (F.suc (F.suc (F.zero))) = refl
originalIndexRoundTrip (F.suc (F.suc (F.suc (F.zero)))) = refl
originalIndexRoundTrip (F.suc (F.suc (F.suc (F.suc (F.zero))))) = refl
originalIndexRoundTrip (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))) = refl
originalIndexRoundTrip (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))) = refl
originalIndexRoundTrip (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))) = refl
originalIndexRoundTrip (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))) = refl
originalIndexRoundTrip (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))) = refl
originalIndexRoundTrip (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))) = refl
originalIndexRoundTrip (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))))) = refl
originalIndexRoundTrip (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))) = refl
originalIndexRoundTrip (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))))))) = refl
originalIndexRoundTrip (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))))) = refl
originalIndexRoundTrip (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))))))))) = refl
originalIndexRoundTrip (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))))))) = refl
originalIndexRoundTrip (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))))))))))) = refl
originalIndexRoundTrip (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))))))))) = refl
originalIndexRoundTrip (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))))))))))))) = refl
originalIndexRoundTrip (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))))))))))) = refl
originalIndexRoundTrip (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))))))))))))))) = refl
originalIndexRoundTrip (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))))))))))))) = refl
originalIndexRoundTrip (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))))))))))))))))) = refl
originalIndexRoundTrip (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))))))))))))))) = refl
originalIndexRoundTrip (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))))))))))))))))))) = refl
originalIndexRoundTrip (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))))))))))))))))) = refl

originalIndexIsInjective :
  (p q : Cube.Ternary27Point) →
  originalPointIndex p ≡ originalPointIndex q → p ≡ q
originalIndexIsInjective p q equality =
  trans
    (sym (originalPointRoundTrip p))
    (trans (cong originalPointAtIndex equality)
      (originalPointRoundTrip q))

originalIndexIsSurjective :
  (i : F.Fin 27) →
  Σ Cube.Ternary27Point (λ p → originalPointIndex p ≡ i)
originalIndexIsSurjective i =
  originalPointAtIndex i , originalIndexRoundTrip i

-- All 54 bonds are already certified nearest-neighbour by the
-- original incidence owner; source and target are indexed literally.
canonical54BondIndexing : Transfer.Original54BondIndexing
canonical54BondIndexing = record
  { pointIndex = originalPointIndex
  ; sourceIndex = λ bond → originalPointIndex (Grid.bondStart bond)
  ; targetIndex = λ bond → originalPointIndex (Grid.bondEnd bond)
  ; indexesOriginalSource = λ bond → refl
  ; indexesOriginalTarget = λ bond → refl
  }

originalIndexedBondIsGenuineNeighbour :
  (bond : Grid.PositiveBond) →
  Cube.HypervoxelAdjacent
    (originalPointAtIndex
      (Transfer.sourceIndex canonical54BondIndexing bond))
    (originalPointAtIndex
      (Transfer.targetIndex canonical54BondIndexing bond))
originalIndexedBondIsGenuineNeighbour bond
  rewrite originalPointRoundTrip (Grid.bondStart bond)
        | originalPointRoundTrip (Grid.bondEnd bond) =
  Grid.bondIsNearestNeighbour bond

originalForwardBond :
  Grid.PositiveBond → (F.Fin 27 × F.Fin 27)
originalForwardBond =
  Transfer.originalBondForwardAction canonical54BondIndexing

originalReverseBond :
  Grid.PositiveBond → (F.Fin 27 × F.Fin 27)
originalReverseBond =
  Transfer.originalBondReverseAction canonical54BondIndexing

all54ForwardBondActions : List (F.Fin 27 × F.Fin 27)
all54ForwardBondActions =
  Grid.mapList originalForwardBond Grid.allPositiveBonds

all54ReverseBondActions : List (F.Fin 27 × F.Fin 27)
all54ReverseBondActions =
  Grid.mapList originalReverseBond Grid.allPositiveBonds

mapPreservesListCount :
  ∀ {A B : Set}
  (f : A → B) (xs : List A) →
  Grid.countList (Grid.mapList f xs) ≡ Grid.countList xs
mapPreservesListCount f [] = refl
mapPreservesListCount f (x ∷ xs) =
  cong suc (mapPreservesListCount f xs)

indexedForwardBondCountExactly54 :
  Grid.countList all54ForwardBondActions ≡ 54
indexedForwardBondCountExactly54 =
  trans
    (mapPreservesListCount originalForwardBond Grid.allPositiveBonds)
    Grid.completeBondCount

indexedReverseBondCountExactly54 :
  Grid.countList all54ReverseBondActions ≡ 54
indexedReverseBondCountExactly54 =
  trans
    (mapPreservesListCount originalReverseBond Grid.allPositiveBonds)
    Grid.completeBondCount

-- This is the ACTUAL originally typed 54-bond geometric sweep on ONE
-- Vec Nat 27 state. Every individual transfer uses the immediately
-- updated shared inventory produced by the preceding transfer.
oneFullOriginal54BondSweepConserves :
  (state : V.Vec Nat 27) →
  V.sum (Transfer.runTransfers all54ForwardBondActions state)
    ≡ V.sum state
oneFullOriginal54BondSweepConserves =
  Transfer.all27SharedSitesConserve all54ForwardBondActions

oneFullOriginalReverse54BondSweepConserves :
  (state : V.Vec Nat 27) →
  V.sum (Transfer.runTransfers all54ReverseBondActions state)
    ≡ V.sum state
oneFullOriginalReverse54BondSweepConserves =
  Transfer.all27SharedSitesConserve all54ReverseBondActions

-- Any chronological sequence of source-selected directed original
-- bonds (forward or reversed) also preserves this same inventory.
allOriginal54BondHistoriesConserve :
  (actions : List (F.Fin 27 × F.Fin 27))
  (state : V.Vec Nat 27) →
  V.sum (Transfer.runTransfers actions state) ≡ V.sum state
allOriginal54BondHistoriesConserve =
  Transfer.all27SharedSitesConserve


------------------------------------------------------------------------
-- SAME ORIGINAL 3D GEOMETRY, POINTWISE SOURCE AND TARGET LEDGERS
-- (not a separate artificial per-edge inventory).
------------------------------------------------------------------------

originalBondLocalSourceDebitIsPaid :
  (bond : Grid.PositiveBond) (state : V.Vec Nat 27) →
  V.lookup
    (Transfer.debitAt (originalPointIndex (Grid.bondStart bond)) state)
    (originalPointIndex (Grid.bondStart bond))
    + Transfer.actualSourceDebit
        (originalPointIndex (Grid.bondStart bond)) state
    ≡ V.lookup state (originalPointIndex (Grid.bondStart bond))
originalBondLocalSourceDebitIsPaid bond state =
  Transfer.lookupAfterDebit
    (originalPointIndex (Grid.bondStart bond)) state

originalBondLocalTargetCreditIsPaid :
  (bond : Grid.PositiveBond) (state : V.Vec Nat 27) →
  V.lookup
    (Transfer.creditAt (originalPointIndex (Grid.bondEnd bond)) state)
    (originalPointIndex (Grid.bondEnd bond))
    ≡ suc (V.lookup state (originalPointIndex (Grid.bondEnd bond)))
originalBondLocalTargetCreditIsPaid bond state =
  Transfer.lookupAfterCredit
    (originalPointIndex (Grid.bondEnd bond)) state


------------------------------------------------------------------------
-- PHYSICALLY TYPED DIRECTED HISTORIES. Unlike an unconstrained list
-- of Fin 27 pairs, each constructor carries a genuine original
-- nearest-neighbour bond, either forward or reversed.
------------------------------------------------------------------------

data OriginalDirectedNativeBond : Set where
  forwardNative : Grid.PositiveBond → OriginalDirectedNativeBond
  reverseNative : Grid.PositiveBond → OriginalDirectedNativeBond

nativeDirectedSource : OriginalDirectedNativeBond → F.Fin 27
nativeDirectedSource (forwardNative bond) =
  originalPointIndex (Grid.bondStart bond)
nativeDirectedSource (reverseNative bond) =
  originalPointIndex (Grid.bondEnd bond)

nativeDirectedTarget : OriginalDirectedNativeBond → F.Fin 27
nativeDirectedTarget (forwardNative bond) =
  originalPointIndex (Grid.bondEnd bond)
nativeDirectedTarget (reverseNative bond) =
  originalPointIndex (Grid.bondStart bond)

applyNativeDirectedBond :
  OriginalDirectedNativeBond → V.Vec Nat 27 → V.Vec Nat 27
applyNativeDirectedBond action state =
  Transfer.transferOne
    (nativeDirectedSource action) (nativeDirectedTarget action) state

runOriginalDirectedNativeHistory :
  List OriginalDirectedNativeBond → V.Vec Nat 27 → V.Vec Nat 27
runOriginalDirectedNativeHistory [] state = state
runOriginalDirectedNativeHistory (action ∷ rest) state =
  runOriginalDirectedNativeHistory rest
    (applyNativeDirectedBond action state)

everyNativeDirectedBondConserves :
  (action : OriginalDirectedNativeBond)
  (state : V.Vec Nat 27) →
  V.sum (applyNativeDirectedBond action state) ≡ V.sum state
everyNativeDirectedBondConserves action state =
  Transfer.everyDirectedPairConservesSharedInventory
    (nativeDirectedSource action) (nativeDirectedTarget action) state

everyChronologicalOriginalDirectedHistoryConserves :
  (history : List OriginalDirectedNativeBond)
  (state : V.Vec Nat 27) →
  V.sum (runOriginalDirectedNativeHistory history state)
    ≡ V.sum state
everyChronologicalOriginalDirectedHistoryConserves [] state = refl
everyChronologicalOriginalDirectedHistoryConserves
  (action ∷ rest) state =
  trans
    (everyChronologicalOriginalDirectedHistoryConserves rest
      (applyNativeDirectedBond action state))
    (everyNativeDirectedBondConserves action state)

-- The *same observer voxel* is outside every certified physical
-- movement in the history. The evidence is recursively indexed by
-- the actual directed-bond list and cannot silently admit remote
-- synthetic pair actions.
data NativeHistoryAvoids (observer : F.Fin 27) :
  List OriginalDirectedNativeBond → Set where
  avoidsEmpty : NativeHistoryAvoids observer []
  avoidsCons :
    ∀ {action rest} →
    ¬ (nativeDirectedSource action ≡ observer) →
    ¬ (nativeDirectedTarget action ≡ observer) →
    NativeHistoryAvoids observer rest →
    NativeHistoryAvoids observer (action ∷ rest)

nativeHistoryLeavesUnvisitedVoxelUnchanged :
  (observer : F.Fin 27)
  (history : List OriginalDirectedNativeBond)
  (state : V.Vec Nat 27) →
  NativeHistoryAvoids observer history →
  V.lookup (runOriginalDirectedNativeHistory history state) observer
    ≡ V.lookup state observer
nativeHistoryLeavesUnvisitedVoxelUnchanged observer [] state
  avoidsEmpty = refl
nativeHistoryLeavesUnvisitedVoxelUnchanged observer (action ∷ rest)
  state (avoidsCons sourceAway targetAway restAway) =
  trans
    (nativeHistoryLeavesUnvisitedVoxelUnchanged observer rest
      (applyNativeDirectedBond action state) restAway)
    (Transfer.lookupTransferAwayFromEndpoints
      (nativeDirectedSource action)
      (nativeDirectedTarget action)
      observer state sourceAway targetAway)


-- The source and destination balances are proven for the *executed*
-- native transfer, when distinctness is supplied for the geometric
-- endpoints. This keeps the geometric inequality as an explicit
-- obligation rather than implicitly assuming a graph has no loops.
nativeDirectedBondSourceQuantityPaid :
  (action : OriginalDirectedNativeBond) (state : V.Vec Nat 27) →
  ¬ (nativeDirectedSource action ≡ nativeDirectedTarget action) →
  V.lookup (applyNativeDirectedBond action state)
    (nativeDirectedSource action)
    + Transfer.actualSourceDebit (nativeDirectedSource action) state
    ≡ V.lookup state (nativeDirectedSource action)
nativeDirectedBondSourceQuantityPaid action state different =
  Transfer.lookupTransferSourcePaid
    (nativeDirectedSource action) (nativeDirectedTarget action)
    state different

nativeDirectedBondTargetQuantityPaid :
  (action : OriginalDirectedNativeBond) (state : V.Vec Nat 27) →
  ¬ (nativeDirectedSource action ≡ nativeDirectedTarget action) →
  V.lookup (applyNativeDirectedBond action state)
    (nativeDirectedTarget action)
    ≡ V.lookup state (nativeDirectedTarget action)
      + Transfer.actualSourceDebit (nativeDirectedSource action) state
nativeDirectedBondTargetQuantityPaid action state different =
  Transfer.lookupTransferTargetReceivesActualSource
    (nativeDirectedSource action) (nativeDirectedTarget action)
    state different


------------------------------------------------------------------------
-- NO-LOOP CERTIFICATE FROM ORIGINAL CUBICAL GEOMETRY.
-- Discharge the source/target distinctness premise using genuine
-- ternary grid steps and the existing original 27-index injection.
------------------------------------------------------------------------

tritGridStepNeverStationary :
  ∀ {a b} → Cube.TritGridStep a b → ¬ (a ≡ b)
tritGridStepNeverStationary Cube.negToZero ()
tritGridStepNeverStationary Cube.zeroToNeg ()
tritGridStepNeverStationary Cube.zeroToPos ()
tritGridStepNeverStationary Cube.posToZero ()

originalPositiveBondEndpointsDistinct :
  (bond : Grid.PositiveBond) →
  ¬ (Grid.bondStart bond ≡ Grid.bondEnd bond)
originalPositiveBondEndpointsDistinct (Grid.xBond segment y z) equality =
  tritGridStepNeverStationary (Grid.forwardWitness segment)
    (cong Cube.x equality)
originalPositiveBondEndpointsDistinct (Grid.yBond x segment z) equality =
  tritGridStepNeverStationary (Grid.forwardWitness segment)
    (cong Cube.y equality)
originalPositiveBondEndpointsDistinct (Grid.zBond x y segment) equality =
  tritGridStepNeverStationary (Grid.forwardWitness segment)
    (cong Cube.z equality)

originalDirectedNativeEndpointsDistinct :
  (action : OriginalDirectedNativeBond) →
  ¬ (nativeDirectedSource action ≡ nativeDirectedTarget action)
originalDirectedNativeEndpointsDistinct (forwardNative bond) equality =
  originalPositiveBondEndpointsDistinct bond
    (originalIndexIsInjective
      (Grid.bondStart bond) (Grid.bondEnd bond) equality)
originalDirectedNativeEndpointsDistinct (reverseNative bond) equality =
  originalPositiveBondEndpointsDistinct bond
    (originalIndexIsInjective
      (Grid.bondStart bond) (Grid.bondEnd bond)
      (sym equality))

-- No free geometric premise now remains in these *actual* source/
-- destination flow equalities.
original369NativeSourceFluxExact :
  (action : OriginalDirectedNativeBond) (state : V.Vec Nat 27) →
  V.lookup (applyNativeDirectedBond action state)
    (nativeDirectedSource action)
    + Transfer.actualSourceDebit (nativeDirectedSource action) state
    ≡ V.lookup state (nativeDirectedSource action)
original369NativeSourceFluxExact action state =
  nativeDirectedBondSourceQuantityPaid action state
    (originalDirectedNativeEndpointsDistinct action)

original369NativeTargetFluxExact :
  (action : OriginalDirectedNativeBond) (state : V.Vec Nat 27) →
  V.lookup (applyNativeDirectedBond action state)
    (nativeDirectedTarget action)
    ≡ V.lookup state (nativeDirectedTarget action)
      + Transfer.actualSourceDebit (nativeDirectedSource action) state
original369NativeTargetFluxExact action state =
  nativeDirectedBondTargetQuantityPaid action state
    (originalDirectedNativeEndpointsDistinct action)
