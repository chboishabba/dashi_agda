module DASHI.Biology.AvianMagneticPerturbationSourceRegistry where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

data PerturbationEvidenceRole : Set where
  controlledStaticFieldOrientation : PerturbationEvidenceRole
  inclinationCompassReceipt : PerturbationEvidenceRole
  broadbandElectromagneticNoisePerturbation : PerturbationEvidenceRole
  shieldingControlReceipt : PerturbationEvidenceRole
  groundingControlReceipt : PerturbationEvidenceRole
  ruralBackgroundControlReceipt : PerturbationEvidenceRole
  apparatusFieldMeasurementReceipt : PerturbationEvidenceRole
  receptorMechanismUnresolved : PerturbationEvidenceRole

record AvianMagneticPerturbationSource : Set where
  constructor avian-magnetic-perturbation-source
  field
    authors : String
    title : String
    venue : String
    year : Nat
    identifier : String
    species : String
    roles : List PerturbationEvidenceRole
    behavioralMagneticEffectObserved : Bool
    receptorMechanismEstablished : Bool
    sourceBoundary : String

open AvianMagneticPerturbationSource public

wiltschkoWiltschko1972 : AvianMagneticPerturbationSource
wiltschkoWiltschko1972 =
  avian-magnetic-perturbation-source
    "Wolfgang Wiltschko; Roswitha Wiltschko"
    "Magnetic Compass of European Robins"
    "Science 176(4030):62-64"
    1972
    "DOI 10.1126/science.176.4030.62; PMID 17784420"
    "Erithacus rubecula"
    ( controlledStaticFieldOrientation
    ∷ inclinationCompassReceipt
    ∷ receptorMechanismUnresolved
    ∷ []
    )
    true
    false
    "Supports an inclination-sensitive magnetic compass under controlled magnetic-field manipulation; does not identify the receptor mechanism."

engelsEtAl2014 : AvianMagneticPerturbationSource
engelsEtAl2014 =
  avian-magnetic-perturbation-source
    "Svenja Engels; Nils-Lasse Schneider; Nele Lefeldt; Christine Maira Hein; Manuela Zapka; Andreas Michalik; Dana Elbers; Achim Kittel; P. J. Hore; Henrik Mouritsen"
    "Anthropogenic electromagnetic noise disrupts magnetic compass orientation in a migratory bird"
    "Nature 509:353-356"
    2014
    "DOI 10.1038/nature13290"
    "Erithacus rubecula"
    ( broadbandElectromagneticNoisePerturbation
    ∷ shieldingControlReceipt
    ∷ groundingControlReceipt
    ∷ ruralBackgroundControlReceipt
    ∷ apparatusFieldMeasurementReceipt
    ∷ receptorMechanismUnresolved
    ∷ []
    )
    true
    false
    "Supports reproducible disruption of robin magnetic compass orientation by broadband electromagnetic noise together with shielding/grounding/rural controls; the behavioral result does not by itself identify a receptor mechanism."

wiltschkoBehaviorObserved :
  behavioralMagneticEffectObserved wiltschkoWiltschko1972 ≡ true
wiltschkoBehaviorObserved = refl

wiltschkoMechanismNotEstablished :
  receptorMechanismEstablished wiltschkoWiltschko1972 ≡ false
wiltschkoMechanismNotEstablished = refl

engelsBehaviorObserved :
  behavioralMagneticEffectObserved engelsEtAl2014 ≡ true
engelsBehaviorObserved = refl

engelsMechanismNotEstablished :
  receptorMechanismEstablished engelsEtAl2014 ≡ false
engelsMechanismNotEstablished = refl
