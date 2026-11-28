module DASHI.Moonshine.CM163Hecke41Signed43TorusExact where

-- SOURCE-WRITTEN, kernel pending. Same Fin42 chart indices as the original
-- Hecke lattice owner. The nonsplit torus acts on reduced ROW lines
-- [1:k] and [0:1] in P^1(F41). Label its regular orbit by 3^e mod 43.
-- This is an auxiliary indexing action, not a new SL2Z modular symmetry.
-- Classical finite fields/projective tori and CRT retain attribution.
-- DASHI donors: HyperfabricPunctured27Projective13OrientationExact,
-- SSPRepresentationReductionRound9 (43 is a non-Ogg control),
-- SignedSSPProofCarryingExponentExact and the original Hecke product reindex.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin using (Fin; toℕ) renaming (zero to fz; suc to fs)
open import DASHI.Foundations.Base369Nat using (_%_)
open import Data.Product.Base using (_,_; _×_)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Moonshine.CM163BishopHecke41ProductExact as Prod

-- Orbit of infinity under right multiplication by [[4,3],[1,4]].
-- Determinant 13 mod 41. 3 is a nonsquare mod 41.
decode encode next halfTurn : Fin 42 → Fin 42
decode (fz) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))))))
decode (fs (fz)) = (fs (fs (fs (fs (fz)))))
decode (fs (fs (fz))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))
decode (fs (fs (fs (fz)))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))
decode (fs (fs (fs (fs (fz))))) = (fs (fs (fs (fs (fs (fs (fz)))))))
decode (fs (fs (fs (fs (fs (fz)))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fz))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fz)))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))) = (fs (fs (fs (fs (fs (fz))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))) = (fs (fs (fs (fz))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))) = (fz)
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))) = (fs (fs (fz)))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fz))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))) = (fs (fz))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))

encode (fz) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))
encode (fs (fz)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))
encode (fs (fs (fz))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))
encode (fs (fs (fs (fz)))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))
encode (fs (fs (fs (fs (fz))))) = (fs (fz))
encode (fs (fs (fs (fs (fs (fz)))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))
encode (fs (fs (fs (fs (fs (fs (fz))))))) = (fs (fs (fs (fs (fz)))))
encode (fs (fs (fs (fs (fs (fs (fs (fz)))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))) = (fs (fs (fs (fz))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))) = (fs (fs (fs (fs (fs (fz))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fz))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))) = (fs (fs (fz)))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fz)))))))
encode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))))) = (fz)

next (fz) = (fs (fz))
next (fs (fz)) = (fs (fs (fz)))
next (fs (fs (fz))) = (fs (fs (fs (fz))))
next (fs (fs (fs (fz)))) = (fs (fs (fs (fs (fz)))))
next (fs (fs (fs (fs (fz))))) = (fs (fs (fs (fs (fs (fz))))))
next (fs (fs (fs (fs (fs (fz)))))) = (fs (fs (fs (fs (fs (fs (fz)))))))
next (fs (fs (fs (fs (fs (fs (fz))))))) = (fs (fs (fs (fs (fs (fs (fs (fz))))))))
next (fs (fs (fs (fs (fs (fs (fs (fz)))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))))))
next (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))))) = (fz)

halfTurn (fz) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))
halfTurn (fs (fz)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))
halfTurn (fs (fs (fz))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))
halfTurn (fs (fs (fs (fz)))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))
halfTurn (fs (fs (fs (fs (fz))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))
halfTurn (fs (fs (fs (fs (fs (fz)))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fz))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fz)))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))) = (fz)
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))) = (fs (fz))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))) = (fs (fs (fz)))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))) = (fs (fs (fs (fz))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))) = (fs (fs (fs (fs (fz)))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fz))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fz)))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fz))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))
halfTurn (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))))) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))

encodeDecode : ∀ e → encode (decode e) ≡ e
encodeDecode (fz) = refl
encodeDecode (fs (fz)) = refl
encodeDecode (fs (fs (fz))) = refl
encodeDecode (fs (fs (fs (fz)))) = refl
encodeDecode (fs (fs (fs (fs (fz))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fz)))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fz))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fz)))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))))) = refl

decodeEncode : ∀ k → decode (encode k) ≡ k
decodeEncode (fz) = refl
decodeEncode (fs (fz)) = refl
decodeEncode (fs (fs (fz))) = refl
decodeEncode (fs (fs (fs (fz)))) = refl
decodeEncode (fs (fs (fs (fs (fz))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fz)))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fz))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fz)))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))))) = refl
decodeEncode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))))) = refl

halfTurnTwice : ∀ e → halfTurn (halfTurn e) ≡ e
halfTurnTwice (fz) = refl
halfTurnTwice (fs (fz)) = refl
halfTurnTwice (fs (fs (fz))) = refl
halfTurnTwice (fs (fs (fs (fz)))) = refl
halfTurnTwice (fs (fs (fs (fs (fz))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fz)))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fz))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fz)))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))))) = refl
halfTurnTwice (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))))) = refl

pow3 : Nat → Nat
pow3 zero = 1
pow3 (suc n) = (3 * pow3 n) % 43

unitLabel : Fin 42 → Nat
unitLabel e = pow3 (toℕ e)

unitStep : ∀ e → unitLabel (next e) ≡ (3 * unitLabel e) % 43
unitStep (fz) = refl
unitStep (fs (fz)) = refl
unitStep (fs (fs (fz))) = refl
unitStep (fs (fs (fs (fz)))) = refl
unitStep (fs (fs (fs (fs (fz))))) = refl
unitStep (fs (fs (fs (fs (fs (fz)))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fz))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fz)))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))))) = refl
unitStep (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))))) = refl

unitNeg : ∀ e → (unitLabel (halfTurn e) + unitLabel e) % 43 ≡ 0
unitNeg (fz) = refl
unitNeg (fs (fz)) = refl
unitNeg (fs (fs (fz))) = refl
unitNeg (fs (fs (fs (fz)))) = refl
unitNeg (fs (fs (fs (fs (fz))))) = refl
unitNeg (fs (fs (fs (fs (fs (fz)))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fz))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fz)))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))))) = refl
unitNeg (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))))) = refl

-- Original finite charts have reduced first row [1:k] for k<41;
-- the infinity chart has reduced second row [0:1].
rowX rowY : Fin 42 → Nat
rowX k with toℕ k ≟ 41
... | yes _ = 0
... | no _ = 1
rowY k with toℕ k ≟ 41
... | yes _ = 1
... | no _ = toℕ k

-- Same projective line after one nonsplit-torus step. Cross products
-- avoid field inversion and include the actual infinity chart.
torusEdge : ∀ e →
  ((4 * rowX (decode e) + rowY (decode e)) * rowY (decode (next e))) % 41
  ≡ ((3 * rowX (decode e) + 4 * rowY (decode e)) * rowX (decode (next e))) % 41
torusEdge (fz) = refl
torusEdge (fs (fz)) = refl
torusEdge (fs (fs (fz))) = refl
torusEdge (fs (fs (fs (fz)))) = refl
torusEdge (fs (fs (fs (fs (fz))))) = refl
torusEdge (fs (fs (fs (fs (fs (fz)))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fz))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fz)))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))))) = refl
torusEdge (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))))) = refl

-- CRT coordinate (sign phase, C3 phase, C7 phase). The recombination
-- uses orthogonal idempotents 21,28,36 in Z/42.
coordinate : Fin 42 → Nat × (Nat × Nat)
coordinate e = (toℕ e % 2) , ((toℕ e % 3) , (toℕ e % 7))

coordinateRead : ∀ e →
  (21 * (toℕ e % 2) + 28 * (toℕ e % 3) + 36 * (toℕ e % 7)) % 42 ≡ toℕ e
coordinateRead (fz) = refl
coordinateRead (fs (fz)) = refl
coordinateRead (fs (fs (fz))) = refl
coordinateRead (fs (fs (fs (fz)))) = refl
coordinateRead (fs (fs (fs (fs (fz))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fz)))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fz))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fz)))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))))) = refl
coordinateRead (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))))) = refl

-- Exponent-coordinate CRT and sign orientation are auxiliary to the
-- original product. This theorem uses its actual permutation transport.
sameProduct : (f : Fin 42 → C.BishopComplex) →
  C._≈C_ (Prod.product (λ e → f (decode e))) (Prod.product f)
sameProduct f = Prod.reindex f decode encode encodeDecode decodeEncode

-- Negative unit label is the same sign flip on the order-42 torus,
-- not the statement that the corresponding j-values are equal or opposite.
