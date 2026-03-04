module DASHI.Algebra.Quantum.UVFinitenessHolographyInstance where

open import Data.Nat using (ℕ; _*_ ; _≤_; _^_; zero; suc)
open import Data.Nat.Properties as NatP using (≤-refl; ≤-reflexive; *-identityˡ)
open import Relation.Binary.PropositionalEquality using (sym; refl; trans; _≡_)

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
uvAreaBound n = NatP.≤-reflexive (sym (NatP.*-identityˡ n))

uvFinitenessInst : _
uvFinitenessInst = UVFinitenessTheorem uvFinitenessAxioms uvAreaBound

-- Concrete area-law instance (physics-facing) using the minimal AreaLaw interface.
areaRegion : AL.RegionCounts
areaRegion =
  record
    { Region = ℕ
    ; area = λ n → n
    ; volume = λ n → n
    ; admCount = λ _ → 1
    }

onePow : ∀ r → 1 ^ r ≡ 1
onePow zero = refl
onePow (suc r) = trans (NatP.*-identityˡ (1 ^ r)) (onePow r)

areaLawUV : AL.UVFinite areaRegion
areaLawUV =
  record
    { K = 1
    ; areaLaw = λ r → NatP.≤-reflexive (sym (onePow r))
    }
