module DASHI.Physics.Closure.ChemistryRightLimitsQuotientCrossBandCouplingRequirement where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)
import Data.Vec as Vec
open import Data.Vec using (Vec; map)

open import DASHI.Physics.Closure.AtomicChemistryRecoveryTheorem as ACRT
open import DASHI.Physics.Closure.AtomicChemistryRightLimitsAdapter as ACRLA
open import DASHI.Physics.Closure.ChemistryRightLimitsPromotedObservableCouplingLaw as CRPOCL
open import DASHI.Physics.Closure.ChemistryRightLimitsQuotientObservableCouplingLaw as TripleLaw
open import Ontology.DNA.ChemistryUVCoordinates as UV
open import Ontology.DNA.ChemistryQuotient as CDQ
open import Ontology.DNA.ChemistrySheetHamiltonian as CSH

------------------------------------------------------------------------
-- First non-vacuous atomic blocker route after stable triple compatibility.
--
-- The quotient-visible observable and triple coupling law are already landed.
-- The missing witness is now non-degenerate: hold the defect/promoted pair
-- fixed while the quotient observable separates, and require a chemistry-facing
-- cross-band coupling quantity to separate with it.

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

sheetTimeReverse : CSH.Signed → CSH.Signed
sheetTimeReverse CSH.neg = CSH.pos
sheetTimeReverse CSH.zer = CSH.zer
sheetTimeReverse CSH.pos = CSH.neg

sheetTimeReverse-involutive :
  ∀ s → sheetTimeReverse (sheetTimeReverse s) ≡ s
sheetTimeReverse-involutive CSH.neg = refl
sheetTimeReverse-involutive CSH.zer = refl
sheetTimeReverse-involutive CSH.pos = refl

sameSign-timeReverse :
  ∀ x y →
  CSH.sameSign (sheetTimeReverse x) (sheetTimeReverse y)
    ≡
  CSH.sameSign x y
sameSign-timeReverse CSH.neg CSH.neg = refl
sameSign-timeReverse CSH.neg CSH.zer = refl
sameSign-timeReverse CSH.neg CSH.pos = refl
sameSign-timeReverse CSH.zer CSH.neg = refl
sameSign-timeReverse CSH.zer CSH.zer = refl
sameSign-timeReverse CSH.zer CSH.pos = refl
sameSign-timeReverse CSH.pos CSH.neg = refl
sameSign-timeReverse CSH.pos CSH.zer = refl
sameSign-timeReverse CSH.pos CSH.pos = refl

countCrossBandCoupling-timeReverse :
  ∀ {n} (u v : Vec CSH.Signed n) →
  CSH.countCrossBandCoupling
    (Vec.map sheetTimeReverse u)
    (Vec.map sheetTimeReverse v)
    ≡
  CSH.countCrossBandCoupling u v
countCrossBandCoupling-timeReverse Vec.[] Vec.[] = refl
countCrossBandCoupling-timeReverse (u Vec.∷ us) (v Vec.∷ vs)
  rewrite sameSign-timeReverse u v with CSH.sameSign u v
... | true = countCrossBandCoupling-timeReverse us vs
... | false rewrite countCrossBandCoupling-timeReverse us vs = refl

record TimeSymmetricCrossBandKernel : Set₁ where
  field
    timeReverseSigned : CSH.Signed → CSH.Signed
    involutive :
      ∀ s → timeReverseSigned (timeReverseSigned s) ≡ s
    sameSignInvariant :
      ∀ x y →
      CSH.sameSign (timeReverseSigned x) (timeReverseSigned y)
        ≡
      CSH.sameSign x y
    crossBandInvariant :
      ∀ {n} (u v : Vec CSH.Signed n) →
      CSH.countCrossBandCoupling
        (Vec.map timeReverseSigned u)
        (Vec.map timeReverseSigned v)
        ≡
      CSH.countCrossBandCoupling u v

canonicalTimeSymmetricCrossBandKernel :
  TimeSymmetricCrossBandKernel
canonicalTimeSymmetricCrossBandKernel =
  record
    { timeReverseSigned = sheetTimeReverse
    ; involutive = sheetTimeReverse-involutive
    ; sameSignInvariant = sameSign-timeReverse
    ; crossBandInvariant = countCrossBandCoupling-timeReverse
    }

RequirementSupport :
  TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw →
  Set
RequirementSupport tripleLaw =
  ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
    (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
      (CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.atomicRightLimitsAdapter
        (TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw.promotedCouplingLaw
          tripleLaw)))

record ChemistryRightLimitsQuotientCrossBandCouplingRequirement : Setω where
  field
    tripleLaw :
      TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw

    toFeature :
      ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
        (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
          (CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.atomicRightLimitsAdapter
            (TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw.promotedCouplingLaw
              tripleLaw)))
      →
      CDQ.ChemistryFeature
    defect :
      ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
        (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
          (CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.atomicRightLimitsAdapter
            (TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw.promotedCouplingLaw
              tripleLaw)))
      →
      Nat
    promoted :
      ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
        (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
          (CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.atomicRightLimitsAdapter
            (TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw.promotedCouplingLaw
              tripleLaw)))
      →
      Nat
    quotient :
      ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
        (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
          (CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.atomicRightLimitsAdapter
            (TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw.promotedCouplingLaw
              tripleLaw)))
      →
      Nat

    defectVisible :
      (s :
        ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
          (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
            (CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.atomicRightLimitsAdapter
              (TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw.promotedCouplingLaw
                tripleLaw)))) →
      defect s
      ≡
      CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.adaptedDefectObservable
        (TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw.promotedCouplingLaw
          tripleLaw)
        s

    promotedVisible :
      (s :
        ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
          (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
            (CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.atomicRightLimitsAdapter
              (TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw.promotedCouplingLaw
                tripleLaw)))) →
      promoted s
      ≡
      CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.adaptedPromotedObservable
        (TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw.promotedCouplingLaw
          tripleLaw)
        s

    quotientVisible :
      (s :
        ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
          (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
            (CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.atomicRightLimitsAdapter
              (TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw.promotedCouplingLaw
                tripleLaw)))) →
      quotient s
      ≡
      TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw.adaptedQuotientObservable
        tripleLaw
        s

    crossBandCoupling :
      ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
        (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
          (CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.atomicRightLimitsAdapter
            (TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw.promotedCouplingLaw
              tripleLaw)))
      →
      Nat

    crossBandCouplingVisible :
      (s :
        ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
          (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
            (CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.atomicRightLimitsAdapter
              (TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw.promotedCouplingLaw
                tripleLaw)))) →
      crossBandCoupling s
      ≡
      CSH.countCrossBandCoupling
        (map CSH.signStrength (CDQ.ChemistryFeature.u (toFeature s)))
        (map CSH.signPurine (CDQ.ChemistryFeature.v (toFeature s)))

    left right :
      ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
        (ACRLA.AtomicChemistryRightLimitsAdapter.atomicChemistryRecovery
          (CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.atomicRightLimitsAdapter
            (TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw.promotedCouplingLaw
              tripleLaw)))

    sameDefect : defect left ≡ defect right
    samePromoted : promoted left ≡ promoted right
    quotientSeparates : quotient left ≢ quotient right
    crossBandCouplingSeparates : crossBandCoupling left ≢ crossBandCoupling right

    preSpectralBoundary : Set
    preScaleSettingBoundary : Set

    nonClaimBoundary : List String

record ChemistryRightLimitsQuotientCrossBandCouplingTheorem : Setω where
  field
    requirement : ChemistryRightLimitsQuotientCrossBandCouplingRequirement

    pairHeldFixed :
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.defect requirement
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left requirement)
      ≡
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.defect requirement
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right requirement)
      ×
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.promoted requirement
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left requirement)
      ≡
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.promoted requirement
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right requirement)

    quotientSeparates :
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.quotient requirement
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left requirement)
      ≢
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.quotient requirement
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right requirement)

    crossBandCouplingSeparates :
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.crossBandCoupling requirement
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left requirement)
      ≢
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.crossBandCoupling requirement
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right requirement)

crossBandRequirementToTheorem :
  (req : ChemistryRightLimitsQuotientCrossBandCouplingRequirement) →
  ChemistryRightLimitsQuotientCrossBandCouplingTheorem
crossBandRequirementToTheorem req =
  record
    { requirement = req
    ; pairHeldFixed =
        ChemistryRightLimitsQuotientCrossBandCouplingRequirement.sameDefect req
        ,
        ChemistryRightLimitsQuotientCrossBandCouplingRequirement.samePromoted req
    ; quotientSeparates =
        ChemistryRightLimitsQuotientCrossBandCouplingRequirement.quotientSeparates req
    ; crossBandCouplingSeparates =
        ChemistryRightLimitsQuotientCrossBandCouplingRequirement.crossBandCouplingSeparates req
    }

record ChemistryRightLimitsLaw
  (req : ChemistryRightLimitsQuotientCrossBandCouplingRequirement) :
  Set₁ where
  field
    pairAndPromotedHeldFixed :
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.defect req
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left req)
      ≡
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.defect req
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right req)
      ×
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.promoted req
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left req)
      ≡
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.promoted req
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right req)

    quotientStructureSeparates :
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.quotient req
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left req)
      ≢
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.quotient req
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right req)

    crossBandStructureSeparates :
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.crossBandCoupling req
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left req)
      ≢
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.crossBandCoupling req
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right req)

    preSpectralBoundary :
      Set

    preScaleSettingBoundary :
      Set

record ChemistryRightLimitsStrictEnrichment
  (req : ChemistryRightLimitsQuotientCrossBandCouplingRequirement) :
  Set₁ where
  field
    pairCompatibilityStillHolds :
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.defect req
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left req)
      ≡
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.defect req
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right req)
      ×
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.promoted req
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left req)
      ≡
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.promoted req
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right req)

    quotientNotCollapsedByPair :
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.quotient req
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left req)
      ≢
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.quotient req
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right req)

    crossBandNotInTripleCompatibility :
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.crossBandCoupling req
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left req)
      ≢
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.crossBandCoupling req
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right req)

    enrichmentBoundary : List String

record ChemistryRightLimitsQuotientCrossBandLaw : Setω where
  field
    requirement :
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement

    Q : Set

    q :
      RequirementSupport
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.tripleLaw
          requirement)
      →
      Q

    -- Agda underscores are mixfix slots, so this field names the requested
    -- L_chem law as `Lchem` at the identifier level.
    Lchem : Q → Q → Set₁

    lawAtWitness :
      Lchem
        (q (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left
              requirement))
        (q (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right
              requirement))

    lawAtSwappedWitness :
      Lchem
        (q (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right
              requirement))
        (q (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left
              requirement))

    LchemSymmetricAtWitness :
      Lchem
        (q (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left
              requirement))
        (q (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right
              requirement))
      →
      Lchem
        (q (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right
              requirement))
        (q (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left
              requirement))

    LchemEntailsChemistryRightLimitsLaw :
      Lchem
        (q (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left
              requirement))
        (q (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right
              requirement))
      →
      ChemistryRightLimitsLaw requirement

    I× : Q × Q → Nat

    I×SymmetricAtWitness :
      I×
        ( q (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left
              requirement)
        , q (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right
              requirement)
        )
      ≡
      I×
        ( q (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right
              requirement)
        , q (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left
              requirement)
        )

    quotientSensitivityAtWitness :
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.quotient
        requirement
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left
          requirement)
      ≢
      ChemistryRightLimitsQuotientCrossBandCouplingRequirement.quotient
        requirement
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right
          requirement)

    I×BandSensitivityWitness :
      I×
        ( q (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left
              requirement)
        , q (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left
              requirement)
        )
      ≢
      I×
        ( q (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right
              requirement)
        , q (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right
              requirement)
        )

    nontrivialDiagonalAtWitness :
      I×
        ( q (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left
              requirement)
        , q (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left
              requirement)
        )
      ≢
      I×
        ( q (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right
              requirement)
        , q (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right
              requirement)
        )

    strictEnrichment :
      ChemistryRightLimitsStrictEnrichment requirement

    timeSymmetricKernel :
      TimeSymmetricCrossBandKernel

    nonClaimBoundary : List String

requirementToChemistryRightLimitsLaw :
  (req : ChemistryRightLimitsQuotientCrossBandCouplingRequirement) →
  ChemistryRightLimitsLaw req
requirementToChemistryRightLimitsLaw req =
  record
    { pairAndPromotedHeldFixed =
        ChemistryRightLimitsQuotientCrossBandCouplingRequirement.sameDefect req
        ,
        ChemistryRightLimitsQuotientCrossBandCouplingRequirement.samePromoted req
    ; quotientStructureSeparates =
        ChemistryRightLimitsQuotientCrossBandCouplingRequirement.quotientSeparates req
    ; crossBandStructureSeparates =
        ChemistryRightLimitsQuotientCrossBandCouplingRequirement.crossBandCouplingSeparates
          req
    ; preSpectralBoundary =
        ChemistryRightLimitsQuotientCrossBandCouplingRequirement.preSpectralBoundary
          req
    ; preScaleSettingBoundary =
        ChemistryRightLimitsQuotientCrossBandCouplingRequirement.preScaleSettingBoundary
          req
    }

requirementToStrictEnrichment :
  (req : ChemistryRightLimitsQuotientCrossBandCouplingRequirement) →
  ChemistryRightLimitsStrictEnrichment req
requirementToStrictEnrichment req =
  record
    { pairCompatibilityStillHolds =
        ChemistryRightLimitsQuotientCrossBandCouplingRequirement.sameDefect req
        ,
        ChemistryRightLimitsQuotientCrossBandCouplingRequirement.samePromoted req
    ; quotientNotCollapsedByPair =
        ChemistryRightLimitsQuotientCrossBandCouplingRequirement.quotientSeparates req
    ; crossBandNotInTripleCompatibility =
        ChemistryRightLimitsQuotientCrossBandCouplingRequirement.crossBandCouplingSeparates
          req
    ; enrichmentBoundary =
        "The defect/promoted pair is held fixed, so the law is not obtained by changing the existing pair observables"
        ∷ "The quotient observable separates the same pair, so pair compatibility alone cannot recover this law"
        ∷ "The cross-band coupling separates as an additional chemistry-facing structure not present in the stable triple-compatibility law"
        ∷ []
    }

requirementToQuotientCrossBandLaw :
  (req : ChemistryRightLimitsQuotientCrossBandCouplingRequirement) →
  (I× : CDQ.ChemistryFeature × CDQ.ChemistryFeature → Nat) →
  I×
    ( ChemistryRightLimitsQuotientCrossBandCouplingRequirement.toFeature req
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left req)
    , ChemistryRightLimitsQuotientCrossBandCouplingRequirement.toFeature req
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right req)
    )
  ≡
  I×
    ( ChemistryRightLimitsQuotientCrossBandCouplingRequirement.toFeature req
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right req)
    , ChemistryRightLimitsQuotientCrossBandCouplingRequirement.toFeature req
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left req)
    )
  →
  I×
    ( ChemistryRightLimitsQuotientCrossBandCouplingRequirement.toFeature req
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left req)
    , ChemistryRightLimitsQuotientCrossBandCouplingRequirement.toFeature req
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left req)
    )
  ≢
  I×
    ( ChemistryRightLimitsQuotientCrossBandCouplingRequirement.toFeature req
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right req)
    , ChemistryRightLimitsQuotientCrossBandCouplingRequirement.toFeature req
        (ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right req)
    )
  →
  ChemistryRightLimitsQuotientCrossBandLaw
requirementToQuotientCrossBandLaw req I× sym sensitive =
  record
    { requirement = req
    ; Q = CDQ.ChemistryFeature
    ; q =
        ChemistryRightLimitsQuotientCrossBandCouplingRequirement.toFeature req
    ; Lchem =
        λ _ _ → ChemistryRightLimitsLaw req
    ; lawAtWitness =
        requirementToChemistryRightLimitsLaw req
    ; lawAtSwappedWitness =
        requirementToChemistryRightLimitsLaw req
    ; LchemSymmetricAtWitness =
        λ law → law
    ; LchemEntailsChemistryRightLimitsLaw =
        λ law → law
    ; I× = I×
    ; I×SymmetricAtWitness = sym
    ; quotientSensitivityAtWitness =
        ChemistryRightLimitsQuotientCrossBandCouplingRequirement.quotientSeparates
          req
    ; I×BandSensitivityWitness = sensitive
    ; nontrivialDiagonalAtWitness = sensitive
    ; strictEnrichment =
        requirementToStrictEnrichment req
    ; timeSymmetricKernel =
        canonicalTimeSymmetricCrossBandKernel
    ; nonClaimBoundary =
        "L_chem is a quotient/cross-band pre-spectral chemistry law on ChemistryFeature, not a spectral or scale-setting semantics"
        ∷ "Its witness keeps the defect/promoted observables fixed while quotient and cross-band structure separate"
        ∷ "L_chem is inhabited in both witness orders, and I× is symmetric on the Candidate256 pair"
        ∷ "The cross-band kernel is invariant under simultaneous sheet-sign reversal; this records native TSFV-style structural compatibility, not an external temporal/provenance predicate"
        ∷ "I× is band-sensitive and nontrivial on the same fixed defect/promoted pair, so it is not just pair or triple compatibility"
        ∷ "It strictly enriches the landed pair/triple compatibility surface but does not claim bonding, periodic-table completion, nuclear dynamics, physics-facing handoff, or finished chemistry"
        ∷ []
    }

canonicalTripleLaw :
  TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw
canonicalTripleLaw =
  TripleLaw.canonicalChemistryRightLimitsQuotientObservableCouplingLaw

canonicalDefectObservable :
  CDQ.ChemistryFeature → Nat
canonicalDefectObservable =
  CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.adaptedDefectObservable
    (TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw.promotedCouplingLaw
      canonicalTripleLaw)

canonicalPromotedObservable :
  CDQ.ChemistryFeature → Nat
canonicalPromotedObservable =
  CRPOCL.ChemistryRightLimitsPromotedObservableCouplingLaw.adaptedPromotedObservable
    (TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw.promotedCouplingLaw
      canonicalTripleLaw)

canonicalQuotientObservable :
  CDQ.ChemistryFeature → Nat
canonicalQuotientObservable =
  TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw.adaptedQuotientObservable
    canonicalTripleLaw

canonicalCrossBandCoupling :
  CDQ.ChemistryFeature → Nat
canonicalCrossBandCoupling f =
  CSH.countCrossBandCoupling
    (map CSH.signStrength (CDQ.ChemistryFeature.u f))
    (map CSH.signPurine (CDQ.ChemistryFeature.v f))

record CanonicalQuotientCrossBandCouplingCandidate256 : Setω where
  field
    leftUV : UV.UVCoordinates 256
    rightUV : UV.UVCoordinates 256

    sameDefect :
      canonicalDefectObservable (UV.feature256 leftUV)
      ≡
      canonicalDefectObservable (UV.feature256 rightUV)

    samePromoted :
      canonicalPromotedObservable (UV.feature256 leftUV)
      ≡
      canonicalPromotedObservable (UV.feature256 rightUV)

    quotientSeparates :
      canonicalQuotientObservable (UV.feature256 leftUV)
      ≢
      canonicalQuotientObservable (UV.feature256 rightUV)

    crossBandCouplingSeparates :
      canonicalCrossBandCoupling (UV.feature256 leftUV)
      ≢
      canonicalCrossBandCoupling (UV.feature256 rightUV)

canonicalCandidate256ToRequirement :
  CanonicalQuotientCrossBandCouplingCandidate256 →
  ChemistryRightLimitsQuotientCrossBandCouplingRequirement
canonicalCandidate256ToRequirement candidate =
  record
    { tripleLaw = canonicalTripleLaw
    ; toFeature = λ f → f
    ; defect = canonicalDefectObservable
    ; promoted = canonicalPromotedObservable
    ; quotient = canonicalQuotientObservable
    ; defectVisible = λ _ → refl
    ; promotedVisible = λ _ → refl
    ; quotientVisible = λ _ → refl
    ; crossBandCoupling = canonicalCrossBandCoupling
    ; crossBandCouplingVisible = λ _ → refl
    ; left =
        UV.feature256
          (CanonicalQuotientCrossBandCouplingCandidate256.leftUV candidate)
    ; right =
        UV.feature256
          (CanonicalQuotientCrossBandCouplingCandidate256.rightUV candidate)
    ; sameDefect =
        CanonicalQuotientCrossBandCouplingCandidate256.sameDefect candidate
    ; samePromoted =
        CanonicalQuotientCrossBandCouplingCandidate256.samePromoted candidate
    ; quotientSeparates =
        CanonicalQuotientCrossBandCouplingCandidate256.quotientSeparates candidate
    ; crossBandCouplingSeparates =
        CanonicalQuotientCrossBandCouplingCandidate256.crossBandCouplingSeparates
          candidate
    ; preSpectralBoundary =
        TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw.preSpectralBoundary
          canonicalTripleLaw
    ; preScaleSettingBoundary =
        TripleLaw.ChemistryRightLimitsQuotientObservableCouplingLaw.preScaleSettingBoundary
          canonicalTripleLaw
    ; nonClaimBoundary =
        "CanonicalQuotientCrossBandCouplingCandidate256 only lifts a UV-coordinate witness candidate into the existing atomic blocker requirement surface"
        ∷ "It does not yet provide a canonical pair of UV witnesses by itself"
        ∷ "Any later theorem still has to prove the candidate pair is chemistry-facing and not merely bookkeeping"
        ∷ []
    }
