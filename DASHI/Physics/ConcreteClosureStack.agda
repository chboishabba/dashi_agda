module DASHI.Physics.ConcreteClosureStack where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_; _<_; z≤n; s≤s)
open import Data.Bool using (Bool; false; true)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-<-trans; <-≤-trans)
open import Data.Product using (Σ; _,_)
open import Data.Unit.Polymorphic using (⊤; tt)

open import Ultrametric as UMetric
open import Contraction as Contraction using (_≢_; Contractive≢; StrictContraction)
open import DASHI.Geometry.Isotropy as Iso
open import DASHI.Geometry.FiniteSpeed as FS
open import DASHI.Geometry.RealFiniteSpeed.Core as RFS
open import DASHI.Geometry.RealIsotropy.Core as RIS
open import DASHI.Geometry.StrictContractionComposition as SCC
open import DASHI.Physics.TOperator as TOp
open import DASHI.Physics.ClosureBuilder as CB
open import DASHI.Physics.UnifiedClosure as UC
open import DASHI.Physics.ContractionQuadraticBridge as CQ
open import DASHI.Physics.SignatureClassificationBridge as SC
open import DASHI.Physics.CliffordEvenLiftBridge as CE
open import DASHI.Physics.Core as Core
open import DASHI.Physics.DecimationToClifford as D2C
open import DASHI.Physics.Signature31FromShiftOrbitProfile as S31OP
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
            ; lyapunovWitness =
                record
                  { potential = λ _ → zero
                  ; potentialMatchesQuadratic = λ _ → refl
                  }
            ; uniqueUpToScaleWitness =
                record
                  { referenceQuadratic = λ _ → zero
                  ; normalized = λ _ → refl
                  }
            }
        }
    ; sym = record
        { inv = DC.invBool
        ; iso = record { iso = Iso.trivialIsotropy DC.boolUltrametric DC.T ; coneInvariant = ⊤ }
        ; fs  = record { local = λ _ _ → ⊤ ; preservesLocality = λ _ _ _ → tt }
        }
    ; qs = record
        { classify = λ _ _ →
            record
              { p = suc (suc (suc zero))
              ; q = suc zero
              ; signatureValue = S31OP.signature31
              ; signatureForced31 = refl
              ; signatureTheorem = S31OP.signature31-theorem
              }
        }
    ; q2cl = record
        { build = λ out →
            let
              q : Core.Quadratic (CQ.V out)
              q = record { Q = λ _ → ⊤ }
              d : D2C.DecimationAlgebra (CQ.V out)
              d = record
                { A = CQ.V out
                ; mul = λ x _ → x
                ; gen = λ x → x
                }
              r : D2C.CliffordRelations (CQ.V out) q d
              r = record { rel = ⊤ }
            in
            record
              { quadratic = q
              ; decimation = d
              ; relations = r
              ; universal = D2C.decimation⇒clifford q d r
              ; mul = D2C.DecimationAlgebra.mul d
              ; pairedWord = λ x y →
                  D2C.DecimationAlgebra.mul d
                    (D2C.DecimationAlgebra.gen d x)
                    (D2C.DecimationAlgebra.gen d y)
              }
        }
    ; wl = record
        { build = λ {V} {Scalar} Cℓ →
            record
              { State = Σ V (λ _ → V)
              ; grading = record
                  { parity = λ _ → true
                  ; evenClosedMul = ⊤
                  ; oneEven = ⊤
                  }
              ; Even = record
                  { Even = CE.Clifford.Cl Cℓ
                  ; incl = id
                  ; closed = ⊤
                  }
              ; waveLift = record
                  { lift = λ where
                      (x , y) → CE.Clifford.pairedWord Cℓ x y
                  }
              ; landsInEven = λ where
                  (x , y) →
                    CE.Clifford.pairedWord Cℓ x y , refl
              }
        }
    }
