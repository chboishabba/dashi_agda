module DASHI.Physics.ConcreteClosureStack where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_; _<_; z≤n; s≤s)
open import Data.Bool using (false)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-<-trans; <-≤-trans)
open import Data.Unit.Polymorphic using (⊤; tt)

open import Ultrametric as UMetric
open import Contraction as Contraction using (_≢_; Contractive≢; StrictContraction)
open import DASHI.Geometry.Isotropy as Iso
open import DASHI.Geometry.FiniteSpeed as FS
open import DASHI.Geometry.RealFiniteSpeed as RFS
open import DASHI.Geometry.RealIsotropy as RIS
open import DASHI.Geometry.StrictContractionComposition as SCC
open import DASHI.Physics.TOperator as TOp
open import DASHI.Physics.ClosureBuilder as CB
open import DASHI.Physics.UnifiedClosure as UC
open import DASHI.Physics.ContractionQuadraticBridge as CQ
open import DASHI.Physics.SignatureClassificationBridge as SC
open import DASHI.Physics.CliffordEvenLiftBridge as CE
open import DASHI.Combinatorics.Entropy using (Involution)

open import DASHI.Physics.DefaultClosure as DC

-- Reuse the default Bool ultrametric and contraction as a concrete instance.

id : ∀ {A : Set} → A → A
id x = x

nonexp-id : ∀ {S : Set} (U : UMetric.Ultrametric S) → SCC.NonExpansive U id
nonexp-id U = record { nonexp = λ x y → ≤-refl }

preserves≢-id : ∀ {S : Set} → SCC.DistinctPreserving (id {S})
preserves≢-id = record { preserves≢ = λ x≢y → x≢y }

orderLawsNat : SCC.OrderLaws
orderLawsNat = record
  { le-trans = ≤-trans
  ; le-<-trans = ≤-<-trans
  ; <-le-trans = <-≤-trans
  }

-- RealStack using P = T, C = id, R = id so T = P.
realStack : CB.RealStack
realStack =
  record
    { S = DC.Carrier
    ; U = DC.boolUltrametric
    ; C = id
    ; P = DC.T
    ; R = id
    ; nonexpC = nonexp-id DC.boolUltrametric
    ; nonexpR = nonexp-id DC.boolUltrametric
    ; strictP = DC.contractiveBool
    ; orderLaws = orderLawsNat
    ; pres≢R = preserves≢-id
    ; fp0 = false
    ; fixedT = refl
    ; uniqueT = DC.uniqueBool
    ; inv = DC.invBool
    ; iso = record { iso = Iso.trivialIsotropy DC.boolUltrametric DC.T ; coneInvariant = ⊤ }
    ; fs = record { local = λ _ _ → ⊤ ; preservesLocality = λ _ _ _ → tt }
    }

realClosure : UC.closure realStack ≡ CB.buildClosure realStack
realClosure = refl

-- Concrete physics-unification witnesses on the concrete stack.
physicsUnification : UC.PhysicsUnification realStack
physicsUnification =
  record
    { cq = record
        { sc = CB.strictT realStack
        ; out = record
            { V = DC.Carrier
            ; Scalar = Nat
            ; B = λ _ _ → zero
            ; Q = λ _ → zero
            ; Q-def = λ _ → refl
            ; Lyapunov = ⊤
            ; UniqueUpToScale = ⊤
            }
        }
    ; sym = record
        { inv = DC.invBool
        ; iso = record { iso = Iso.trivialIsotropy DC.boolUltrametric DC.T ; coneInvariant = ⊤ }
        ; fs  = record { local = λ _ _ → ⊤ ; preservesLocality = λ _ _ _ → tt }
        }
    ; qs = record
        { classify = λ _ _ → record { p = suc (suc (suc zero)) ; q = suc zero } }
    ; q2cl = record
        { build = λ out →
            record
              { Cl = CQ.V out
              ; embed = id
              ; rel = ⊤
              ; universal = ⊤
              }
        }
    ; wl = record
        { buildEven = λ {V} {Scalar} Cℓ →
            record
              { Even = CE.Clifford.Cl Cℓ
              ; incl = id
              ; closed = ⊤
              }
        }
    }
