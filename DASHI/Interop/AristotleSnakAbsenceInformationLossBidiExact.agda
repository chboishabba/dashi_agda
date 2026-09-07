module DASHI.Interop.AristotleSnakAbsenceInformationLossBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.PairIndexedInformationLossLocusBidiExact as Loss
import DASHI.Interop.AristotleSnakStatementPresenceBoundaryExact as Snaks

-- Three semantically distinct negative-looking states.
data PropertyNegativeSurface : Set where
  uninspected noStatementObserved nativeNoValue : PropertyNegativeSurface

uninspected≠noStatementObserved : uninspected ≡ noStatementObserved → ⊥
uninspected≠noStatementObserved ()

noStatementObserved≠nativeNoValue : noStatementObserved ≡ nativeNoValue → ⊥
noStatementObserved≠nativeNoValue ()

uninspected≠nativeNoValue : uninspected ≡ nativeNoValue → ⊥
uninspected≠nativeNoValue ()

-- Once a projection deliberately collapses no-statement-observed and native
-- novalue, downstream naming cannot reconstruct which source state existed.
data CollapsedAbsenceProjectionRestoresNativeSnak : Set where
collapsedAbsenceCannotRestoreNativeSnak :
  CollapsedAbsenceProjectionRestoresNativeSnak → ⊥
collapsedAbsenceCannotRestoreNativeSnak ()

record AristotleSnakInformationLossBoundary : Set where
  constructor aristotle-snak-information-loss-boundary
  field
    uninspectedDistinctFromNoStatement : Bool
    noStatementDistinctFromNativeNoValue : Bool
    collapsedDistinctionRecoverableDownstream : Bool
    lossIsProjectionPairIndexed : Bool

canonicalAristotleSnakInformationLossBoundary :
  AristotleSnakInformationLossBoundary
canonicalAristotleSnakInformationLossBoundary =
  aristotle-snak-information-loss-boundary true true false true

snakInformationLossStatement : String
snakInformationLossStatement =
  "Wikidata uninspected property-family state, covered-but-no-statement-observed, and native novalue snak are distinct. A projection that collapses no-statement-observed with native novalue loses information at that projection; downstream processing cannot reconstruct the distinction merely from the collapsed value."
