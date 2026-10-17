module DASHI.Physics.Foundations.CMP119CosmologyP2RenormalizedSameObjectReductionValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.CMP119CosmologyP2RenormalizedSameObjectReductionExact as R

literatureTheoremNotReproved :
  R.traceAnomalyLiteratureAuthorityReused ≡ true
literatureTheoremNotReproved = refl

q2ReducedToTwoSameObjectTransports :
  R.q2ReducedToStressAndF2RenormalizedTransports ≡ true
q2ReducedToTwoSameObjectTransports = refl

citationAloneDoesNotPayCMP119Weld :
  R.citationAlonePaysCMP119SameObjectTransport ≡ false
citationAloneDoesNotPayCMP119Weld = refl
