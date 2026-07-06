module DASHI.Physics.Closure.NSTriadKNNatLeTest where
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; _≤_; zero; suc)
open import Data.Nat.Properties using (≤-refl; ≤-trans)

open import DASHI.Physics.Closure.NSTriadKNForcedTailPrimitiveEstimates
  using ( ForcedTailClass
        ; tailEnd; nearTail; transition; degenerate
        ; forcedTailClassProductN2Constant
        )

open import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteIncidenceType
  using ( ForcedTailTriadIncidence )

forcedTailScaledKernelWeight : (c : ForcedTailClass) (N : ℕ) → ForcedTailTriadIncidence c N → ℕ
forcedTailScaledKernelWeight c N τ = 1

forcedTailScaledEnvelope : (c : ForcedTailClass) (N : ℕ) → ForcedTailTriadIncidence c N → ℕ
forcedTailScaledEnvelope c N τ = 1

forcedTailConcreteKernelUpperBoundProxy :
  (c : ForcedTailClass) (N : ℕ) (τ : ForcedTailTriadIncidence c N)
  → forcedTailScaledKernelWeight c N τ ≤ forcedTailScaledEnvelope c N τ
forcedTailConcreteKernelUpperBoundProxy c N τ = ≤-refl

postulate
  actualForcedTailKernelWeight : {c : ForcedTailClass} (N : ℕ) (τ : ForcedTailTriadIncidence c N) → ℕ
  actualKernelBoundedByScaledProxy :
    {c : ForcedTailClass} (N : ℕ) (τ : ForcedTailTriadIncidence c N)
    → actualForcedTailKernelWeight N τ ≤ forcedTailScaledKernelWeight c N τ

forcedTailConcreteKernelUpperBoundActual :
  {c : ForcedTailClass} (N : ℕ) (τ : ForcedTailTriadIncidence c N)
  → actualForcedTailKernelWeight N τ ≤ forcedTailScaledEnvelope c N τ
forcedTailConcreteKernelUpperBoundActual {c} N τ =
  ≤-trans (actualKernelBoundedByScaledProxy N τ) (forcedTailConcreteKernelUpperBoundProxy c N τ)
