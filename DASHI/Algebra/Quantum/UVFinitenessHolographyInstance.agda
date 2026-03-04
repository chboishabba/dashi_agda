module DASHI.Algebra.Quantum.UVFinitenessHolographyInstance where

open import Data.Nat using (ℕ; _*_ ; _≤_)
open import Data.Nat.Properties as NatP using (≤-refl)

open import DASHI.Algebra.Quantum.UVFinitenessHolographyTests
open import DASHI.Physics.Holography.AreaLaw as AL

uvFinitenessAxioms : UVFinitenessAxioms
uvFinitenessAxioms =
  record
    { L = ℕ
    ; vol = λ n → n
    ; area = λ n → n
    ; dimH = λ n → n
    ; eta = 1
    }

uvAreaBound : AreaBound uvFinitenessAxioms
uvAreaBound _ = NatP.≤-refl

uvFiniteness : _
uvFiniteness = UVFinitenessTheorem uvFinitenessAxioms uvAreaBound

-- Concrete area-law instance (physics-facing) using the minimal AreaLaw interface.
areaRegion : AL.RegionCounts
areaRegion =
  record
    { Region = ℕ
    ; area = λ n → n
    ; volume = λ n → n
    ; admCount = λ n → n
    }

areaLawUV : AL.UVFinite areaRegion
areaLawUV =
  record
    { K = 1
    ; areaLaw = λ _ → NatP.≤-refl
    }
