module DASHI.Physics.ClosureBuilder where

open import Agda.Builtin.Equality using (_≡_)
open import Ultrametric as UMetric
open import Contraction as Contraction using (Contractive≢; StrictContraction)
open import DASHI.Combinatorics.Entropy using (Involution)

open import DASHI.Physics.TOperator as TOp
open import DASHI.Geometry.StrictContractionComposition as SCC
open import DASHI.Geometry.RealFiniteSpeed.Core as RFS
open import DASHI.Geometry.RealIsotropy.Core as RIS
import DASHI.Physics.ClosureGlue as Glue

-- Concrete data needed to build a real closure instance.
record RealStack : Set₁ where
  field
    S : Set
    U : UMetric.Ultrametric S

    -- Operator components
    C : S → S
    P : S → S
    R : S → S

    -- Contraction composition inputs
    nonexpC : SCC.NonExpansive U C
    nonexpR : SCC.NonExpansive U R
    strictP : Contractive≢ U P
    orderLaws : SCC.OrderLaws
    pres≢R : SCC.DistinctPreserving R

    -- Fixed point witnesses for T
    fp0 : S
    fixedT : TOp.TOperator.T (record { C = C ; P = P ; R = R }) fp0 ≡ fp0
    uniqueT : ∀ x → TOp.TOperator.T (record { C = C ; P = P ; R = R }) x ≡ x → x ≡ fp0

    -- Symmetry / locality
    inv : Involution S
    iso : RIS.RealIsotropy U (TOp.TOperator.T (record { C = C ; P = P ; R = R }))
    fs  : RFS.RealFiniteSpeed (TOp.TOperator.T (record { C = C ; P = P ; R = R }))

open RealStack public

-- Build T from components.
mkOp : (stk : RealStack) → TOp.TOperator (S stk)
mkOp stk = record { C = C stk ; P = P stk ; R = R stk }

T : (stk : RealStack) → S stk → S stk
T stk = TOp.TOperator.T (mkOp stk)

-- Strict contraction for T by composition.
contractiveT : (stk : RealStack) → Contractive≢ (U stk) (T stk)
contractiveT stk =
  SCC.composeStrict
    (U stk)
    (C stk) (R stk) (P stk)
    (orderLaws stk)
    (nonexpC stk)
    (nonexpR stk)
    (pres≢R stk)
    (strictP stk)

-- Build the StrictContraction record for T.
strictT : (stk : RealStack) → StrictContraction (U stk) (T stk)
strictT stk =
  record
    { contractive≢ = contractiveT stk
    ; fp = fp0 stk
    ; fixed = fixedT stk
    ; unique = uniqueT stk
    }

-- Final closure instance.
buildClosure : (stk : RealStack) → Glue.ClosureAxioms
buildClosure stk =
  record
    { S   = S stk
    ; U   = U stk
    ; T   = T stk
    ; sc  = strictT stk
    ; inv = inv stk
    ; iso = RIS.RealIsotropy.iso (iso stk)
    ; fs  = record
        { local = RFS.RealFiniteSpeed.local (fs stk)
        ; preservesLocality = RFS.RealFiniteSpeed.preservesLocality (fs stk)
        }
    }
