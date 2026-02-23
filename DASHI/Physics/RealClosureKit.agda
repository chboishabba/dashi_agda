module DASHI.Physics.RealClosureKit where

open import Agda.Builtin.Equality using (_≡_)
open import Ultrametric as UMetric
open import Contraction as Contraction using (Contractive≢; StrictContraction)
open import DASHI.Combinatorics.Entropy using (Involution)

open import DASHI.Physics.TOperator as TOp
open import DASHI.Geometry.StrictContractionComposition as SCC
open import DASHI.Geometry.RealIsotropy as RIS
open import DASHI.Geometry.RealFiniteSpeed as RFS

open import DASHI.Physics.ClosureBuilder as CB
import DASHI.Physics.ClosureGlue as Glue

record RealClosureKit : Set₁ where
  field
    S : Set
    U : UMetric.Ultrametric S

    C P R : S → S

    nonexpC : SCC.NonExpansive U C
    nonexpR : SCC.NonExpansive U R
    strictP : Contractive≢ U P
    orderLaws : SCC.OrderLaws
    pres≢R : SCC.DistinctPreserving R

    fp : S
    fixedT : (TOp.TOperator.T (record { C = C ; P = P ; R = R })) fp ≡ fp
    uniqueT : ∀ x → (TOp.TOperator.T (record { C = C ; P = P ; R = R })) x ≡ x → x ≡ fp

    inv : Involution S
    iso : RIS.RealIsotropy U (TOp.TOperator.T (record { C = C ; P = P ; R = R }))
    fs  : RFS.RealFiniteSpeed (TOp.TOperator.T (record { C = C ; P = P ; R = R }))

open RealClosureKit public

toRealStack : RealClosureKit → CB.RealStack
toRealStack k =
  record
    { S = S k
    ; U = U k
    ; C = C k
    ; P = P k
    ; R = R k
    ; nonexpC = nonexpC k
    ; nonexpR = nonexpR k
    ; strictP = strictP k
    ; orderLaws = orderLaws k
    ; pres≢R = pres≢R k
    ; fp0 = fp k
    ; fixedT = fixedT k
    ; uniqueT = uniqueT k
    ; inv = inv k
    ; iso = iso k
    ; fs  = fs k
    }

closureAxioms : (k : RealClosureKit) → Glue.ClosureAxioms
closureAxioms k = CB.buildClosure (toRealStack k)

