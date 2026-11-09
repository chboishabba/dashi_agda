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
