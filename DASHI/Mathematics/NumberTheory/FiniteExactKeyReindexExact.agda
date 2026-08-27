module DASHI.Mathematics.NumberTheory.FiniteExactKeyReindexExact where

------------------------------------------------------------------------
-- REPO CROSS-POLLINATION
--
-- PR #602 makes executable exposure factor through explicit typed key carriers
-- while proving the indexed relation exact.  The #570/#594 edit-locality
-- lineage separately requires unique correspondence and fails closed under
-- ambiguous matches.  This owner extracts the shared finite theorem shape:
--
--   proof-bearing object <-> proof-free key
--
-- with literal encode/decode round trips, a unique key enumeration, and an
-- object enumeration obtained by decoding those keys.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.List.Base using (map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
open import Relation.Binary.PropositionalEquality using (cong; trans)

------------------------------------------------------------------------
-- Exact key chart.

record ExactKeyChart (Object Key : Set) : Set where
  field
    encode : Object → Key
    decode : Key → Object
    decodeEncode : (object : Object) → decode (encode object) ≡ object
    encodeDecode : (key : Key) → encode (decode key) ≡ key

open ExactKeyChart public

encodeInjective :
  ∀ {Object Key : Set}
    (chart : ExactKeyChart Object Key)
    {left right : Object} →
  encode chart left ≡ encode chart right → left ≡ right
encodeInjective chart equality =
  trans
    (symDecodeEncode left)
    (trans (cong (decode chart) equality) (decodeEncode chart right))
  where
  symDecodeEncode :
    (object : Object) → object ≡ decode chart (encode chart object)
  symDecodeEncode object with decodeEncode chart object
  ... | refl = refl

decodeInjective :
  ∀ {Object Key : Set}
    (chart : ExactKeyChart Object Key)
    {left right : Key} →
  decode chart left ≡ decode chart right → left ≡ right
decodeInjective chart equality =
  trans
    (symEncodeDecode left)
    (trans (cong (encode chart) equality) (encodeDecode chart right))
  where
  symEncodeDecode :
    (key : Key) → key ≡ encode chart (decode chart key)
  symEncodeDecode key with encodeDecode chart key
  ... | refl = refl

------------------------------------------------------------------------
-- A unique finite key enumeration induces a unique object enumeration.

record FiniteExactKeyCarrier (Object Key : Set) : Set where
  field
    chart : ExactKeyChart Object Key
    keyEnumeration : List Key
    keyUnique : Unique keyEnumeration
    keyComplete : (key : Key) → key ∈ keyEnumeration

open FiniteExactKeyCarrier public

objectEnumeration :
  ∀ {Object Key : Set} →
  FiniteExactKeyCarrier Object Key → List Object
objectEnumeration carrier =
  map (decode (chart carrier)) (keyEnumeration carrier)

objectUnique :
  ∀ {Object Key : Set}
    (carrier : FiniteExactKeyCarrier Object Key) →
  Unique (objectEnumeration carrier)
objectUnique carrier =
  UniqueP.map⁺ (decodeInjective (chart carrier)) (keyUnique carrier)

------------------------------------------------------------------------
-- Exact key exposure is therefore strong enough to support literal unique
-- finite reindexing.  Domain modules remain responsible for constructing a
-- finite key type/enumeration whose coordinates are the intended mathematics;
-- proof fields should not be smuggled into the key merely to obtain equality.
------------------------------------------------------------------------
