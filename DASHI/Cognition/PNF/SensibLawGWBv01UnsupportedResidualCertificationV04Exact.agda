module DASHI.Cognition.PNF.SensibLawGWBv01UnsupportedResidualCertificationV04Exact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Exact bounded v0.4 receipt.
--
-- The eight-way v0.3 residual frontier remains the coarse observation.
-- v0.4 retains the actual spaCy dependency label only inside the coarse
-- unsupported_dependency fibre.  This is diagnostic refinement, not semantic
-- authority and not a change to the canonical semantic observation.
------------------------------------------------------------------------

data UnsupportedDependencyLabel : Set where
  ROOT acomp agent attr case cc compound conj csubj csubjpass dative dep det expl
  intj meta nummod oprd parataxis pcomp pobj poss preconj predet prep prt punct
  quantmod : UnsupportedDependencyLabel

labelCount : UnsupportedDependencyLabel → Nat
labelCount ROOT = 41044
labelCount acomp = 5044
labelCount agent = 1592
labelCount attr = 6696
labelCount case = 6428
labelCount cc = 20424
labelCount compound = 57199
labelCount conj = 22632
labelCount csubj = 434
labelCount csubjpass = 8
labelCount dative = 834
labelCount dep = 14168
labelCount det = 62273
labelCount expl = 878
labelCount intj = 308
labelCount meta = 176
labelCount nummod = 13133
labelCount oprd = 892
labelCount parataxis = 372
labelCount pcomp = 3430
labelCount pobj = 71046
labelCount poss = 16906
labelCount preconj = 347
labelCount predet = 434
labelCount prep = 73258
labelCount prt = 2974
labelCount punct = 109976
labelCount quantmod = 1088

unsupportedTotal : Nat
unsupportedTotal = 533994

record UnsupportedResidualV04Receipt : Set where
  constructor unsupportedResidualV04Receipt
  field
    schemaRef : String
    rustHead : String
    sourceObservationDigest : String
    coarseUnsupportedResiduals : Nat
    parityChecked : Nat
    parityFailed : Nat
    projectionFailures : Nat
    publicationEffects : Nat
    directOnlyRatioScaled : Nat
    directOnlyRatioScale : Nat
    productionOnePointTwoTier : Bool
    sameFineFibreAcrossPasses : Bool
    fineFibreSumsToCoarse : Bool
    changesSemanticAuthority : Bool
    changesCanonicalConsumerObservation : Bool

open UnsupportedResidualV04Receipt public

v04Receipt : UnsupportedResidualV04Receipt
v04Receipt =
  unsupportedResidualV04Receipt
    "sensiblaw.gwb-expanded-semantic-certification-receipt.v0_4"
    "ae154e24839cbb4d09fa62a197d2b2eb9900b79f"
    "994267e256e93776cea037fb0ad43834799c32dc4d28bfeecf438569fe387165"
    533994
    41044
    0
    0
    0
    10824943693474123
    10000000000000000
    true
    true
    true
    false
    false

parityFailuresZero : parityFailed v04Receipt ≡ 0
parityFailuresZero = refl

fineFibreMatchedAcrossPasses : sameFineFibreAcrossPasses v04Receipt ≡ true
fineFibreMatchedAcrossPasses = refl

fineFibreAccountsForCoarseResidual : fineFibreSumsToCoarse v04Receipt ≡ true
fineFibreAccountsForCoarseResidual = refl

fineDiagnosticDoesNotCreateSemanticAuthority : changesSemanticAuthority v04Receipt ≡ false
fineDiagnosticDoesNotCreateSemanticAuthority = refl

fineDiagnosticDoesNotChangeCanonicalObservation :
  changesCanonicalConsumerObservation v04Receipt ≡ false
fineDiagnosticDoesNotChangeCanonicalObservation = refl

data DependencyLabelIsLegalMeaning : Set where

dependencyLabelDoesNotByItselfEstablishLegalMeaning : DependencyLabelIsLegalMeaning → ⊥
dependencyLabelDoesNotByItselfEstablishLegalMeaning ()
