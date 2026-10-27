module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingDefectBipartite20261007Test where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingDefectBipartite20261007Exact as D

defectBipartiteClosed : D.b4DefectBipartiteSameObjectClosed ≡ true
defectBipartiteClosed = D.b4DefectBipartiteSameObjectClosedIsTrue

defectFourAggregateClosed : D.b4DefectFourAggregateNormalFormClosed ≡ true
defectFourAggregateClosed = D.b4DefectFourAggregateNormalFormClosedIsTrue

estimateStillOpen : D.b4DefectBipartiteEstimateClosed ≡ false
estimateStillOpen = D.b4DefectBipartiteEstimateClosedIsFalse
