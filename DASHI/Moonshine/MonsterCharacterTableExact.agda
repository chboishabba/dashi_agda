module DASHI.Moonshine.MonsterCharacterTableExact where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.Equality using (_≡_)

------------------------------------------------------------------------
-- Exact owner for Monster table data.  Cyclotomic values are opaque here:
-- no floating-point table is accepted as an ExactMonsterCharacterTable.

postulate
  CyclotomicInteger : Set
  MonsterClassIndex : Set
  MonsterCharacterIndex : Set

record ExactMonsterCharacterTable : Set where
  field
    classCount             : Nat
    irreducibleCount        : Nat
    value                   : MonsterCharacterIndex → MonsterClassIndex → CyclotomicInteger
    classSize               : MonsterClassIndex → Nat
    centralizerOrder        : MonsterClassIndex → Nat
    degree                  : MonsterCharacterIndex → Nat
    classCountIs194         : classCount ≡ 194
    irreducibleCountIs194   : irreducibleCount ≡ 194
    rowOrthogonality        : ⊤
    columnOrthogonality     : ⊤
    sourceHash              : String
    indexingConvention      : String

record OrthogonalityCertificate (table : ExactMonsterCharacterTable) : Set where
  field
    rows    : ⊤
    columns : ⊤
    reading : String
