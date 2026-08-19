module DASHI.Cognition.PNF.ConsumerRestrictionAggregationIntertwinerRegression where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Cognition.PNF.ConsumerRestrictionAggregationIntertwinerExact as Push

------------------------------------------------------------------------
-- A minimal key-indexed restriction is saturated by construction.
------------------------------------------------------------------------

canonicalKeyRestriction : Push.KeyIndexedRestriction Bool Bool Bool Bool
canonicalKeyRestriction = record
  { keyOf = λ row → row
  ; admitKey = λ consumer parent key → key
  }

canonicalRestrictionIsSaturated :
  Push.FibreSaturatedRestriction Bool Bool Bool Bool
canonicalRestrictionIsSaturated =
  Push.keyIndexedRestrictionIsSaturated canonicalKeyRestriction

sameKeyHasSameAdmission :
  Push.admitFine canonicalRestrictionIsSaturated true false true
  ≡ Push.admitFine canonicalRestrictionIsSaturated true false true
sameKeyHasSameAdmission = refl

------------------------------------------------------------------------
-- Identity fold/restriction gives a literal commuting-square inhabitant.
-- The runtime lookup/min-rank instance is a stronger specialization to prove
-- separately; this regression pins the generic theorem surface itself.
------------------------------------------------------------------------

listFold : Push.FibreLocalFold Bool (List Bool)
listFold = record { aggregate = λ xs → xs }

identityIntertwiner :
  Push.ConsumerRestrictionAggregationIntertwiner Bool Bool Bool (List Bool)
identityIntertwiner = record
  { fold = listFold
  ; restrictFine = λ consumer parent xs → xs
  ; restrictAggregate = λ consumer parent xs → xs
  ; intertwines = λ consumer parent xs → refl
  }

sampleRows : List Bool
sampleRows = true ∷ false ∷ []

identityPushdownCommutes :
  Push.restrictAggregate identityIntertwiner true false
    (Push.aggregate (Push.fold identityIntertwiner) sampleRows)
  ≡ Push.aggregate (Push.fold identityIntertwiner)
      (Push.restrictFine identityIntertwiner true false sampleRows)
identityPushdownCommutes =
  Push.consumerRestrictionMayMoveBeforeAggregation
    identityIntertwiner true false sampleRows
