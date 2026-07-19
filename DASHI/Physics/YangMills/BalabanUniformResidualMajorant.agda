module DASHI.Physics.YangMills.BalabanUniformResidualMajorant where

record OrderedProduct (Bound : Set) : Set₁ where
  field
    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    transitive : ∀ {a b c} → LessEqual a b → LessEqual b c → LessEqual a c
    monotoneFirst : ∀ suffix {a b} →
      LessEqual a b → LessEqual (multiply a suffix) (multiply b suffix)

open OrderedProduct public

localToUniform :
  ∀ {Index Bound : Set} {Carrier : Index → Set} →
  (order : OrderedProduct Bound) →
  (residual : ∀ index → Carrier index → Carrier index) →
  (norm : ∀ {index} → Carrier index → Bound) →
  (localFactor : Index → Bound) →
  (uniformFactor : Bound) →
  (∀ index value →
    LessEqual order
      (norm (residual index value))
      (multiply order (localFactor index) (norm value))) →
  (∀ index → LessEqual order (localFactor index) uniformFactor) →
  ∀ index value →
  LessEqual order
    (norm (residual index value))
    (multiply order uniformFactor (norm value))
localToUniform order residual norm localFactor uniformFactor localBound factorBound index value =
  transitive order
    (localBound index value)
    (monotoneFirst order (norm value) (factorBound index))
