module DASHI.Moonshine.VNaturalOrbifoldConstruction where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)

import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA

------------------------------------------------------------------------
-- FLM-shaped orbifold construction surface for V^natural.
--
-- This module does not postulate that the moonshine module exists.  Instead it
-- isolates the exact construction data required by the standard Leech-lattice
-- involution/orbifold route:
--
--   V_Λ  -- fixed-point VOA under θ
--       \-- θ-twisted module, integral/even sector
--
--   V^natural = V_Λ^+ ⊕ (V_Λ^T)^+.
--
-- The direct-sum carrier below is constructive.  Promotion to a VOA requires
-- the supplied closure, locality, Jacobi, conformal, and simplicity witnesses.

record VOAInvolution (V : VOA.VertexOperatorAlgebra) : Setω where
  field
    theta :
      VOA.GradedModule.Carrier (VOA.VertexOperatorAlgebra.gradedModule V) →
      VOA.GradedModule.Carrier (VOA.VertexOperatorAlgebra.gradedModule V)
    involutive : ∀ x → theta (theta x) ≡ x
    preservesVacuum : Set
    preservesConformalVector : Set
    preservesVertexModes : Set
    preservesGrading : Set

open VOAInvolution public

record FixedPointVOA
  (V : VOA.VertexOperatorAlgebra)
  (involution : VOAInvolution V) : Setω where
  field
    fixedCarrier : Set
    includeFixed :
      fixedCarrier →
      VOA.GradedModule.Carrier (VOA.VertexOperatorAlgebra.gradedModule V)
    fixedByTheta :
      ∀ x →
      VOAInvolution.theta involution (includeFixed x) ≡ includeFixed x
    fixedVOA : VOA.VertexOperatorAlgebra
    inclusionPreservesVOA : Set

open FixedPointVOA public

record TwistedModule
  (V : VOA.VertexOperatorAlgebra)
  (involution : VOAInvolution V) : Setω where
  field
    Scalar : Set
    Carrier : Set
    TwistIndex : Set
    twistedMode :
      VOA.GradedModule.Carrier (VOA.VertexOperatorAlgebra.gradedModule V) →
      TwistIndex → Carrier → Carrier
    twistedLowerTruncation : Set
    twistedVacuumCompatibility : Set
    twistedTranslationCovariance : Set
    twistedJacobiIdentity : Set
    thetaMonodromy : Set
    conformalWeight : Carrier → Set

open TwistedModule public

record TwistedEvenSector
  {V : VOA.VertexOperatorAlgebra}
  {involution : VOAInvolution V}
  (twisted : TwistedModule V involution) : Setω where
  field
    CarrierPlus : Set
    includePlus : CarrierPlus → TwistedModule.Carrier twisted
    integralWeight : ∀ x → TwistedModule.conformalWeight twisted (includePlus x)
    thetaEven : Set

open TwistedEvenSector public

OrbifoldCarrier :
  ∀ {V involution}
  (fixed : FixedPointVOA V involution)
  (twisted : TwistedModule V involution)
  (plus : TwistedEvenSector twisted) → Set
OrbifoldCarrier fixed twisted plus =
  FixedPointVOA.fixedCarrier fixed ⊎ TwistedEvenSector.CarrierPlus plus

record OrbifoldVOAAssembly
  {V : VOA.VertexOperatorAlgebra}
  {involution : VOAInvolution V}
  (fixed : FixedPointVOA V involution)
  (twisted : TwistedModule V involution)
  (plus : TwistedEvenSector twisted) : Setω where
  field
    orbifoldVOA : VOA.VertexOperatorAlgebra
    identifyCarrier :
      VOA.GradedModule.Carrier
        (VOA.VertexOperatorAlgebra.gradedModule orbifoldVOA)
      → OrbifoldCarrier fixed twisted plus
    includeFixedSummand :
      FixedPointVOA.fixedCarrier fixed →
      VOA.GradedModule.Carrier
        (VOA.VertexOperatorAlgebra.gradedModule orbifoldVOA)
    includeTwistedSummand :
      TwistedEvenSector.CarrierPlus plus →
      VOA.GradedModule.Carrier
        (VOA.VertexOperatorAlgebra.gradedModule orbifoldVOA)
    fixedSummandIdentifies :
      ∀ x → identifyCarrier (includeFixedSummand x) ≡ inj₁ x
    twistedSummandIdentifies :
      ∀ x → identifyCarrier (includeTwistedSummand x) ≡ inj₂ x
    mixedVertexProductsClosed : Set
    localityAcrossSummands : Set
    JacobiAcrossSummands : Set
    conformalVectorAgrees : Set
    centralCharge24 : Set
    CFTType : Set
    holomorphic : Set
    simple : Set

open OrbifoldVOAAssembly public

record LeechLatticeVOAInput : Setω where
  field
    leechLatticeVOA : VOA.VertexOperatorAlgebra
    leechInvolution : VOAInvolution leechLatticeVOA
    fixedPoint : FixedPointVOA leechLatticeVOA leechInvolution
    canonicalTwistedModule : TwistedModule leechLatticeVOA leechInvolution
    twistedEvenSector : TwistedEvenSector canonicalTwistedModule
    leechRootless : Set
    latticeVOACentralCharge24 : Set

open LeechLatticeVOAInput public

record VNaturalConstruction : Setω where
  field
    leechInput : LeechLatticeVOAInput
    orbifoldAssembly :
      OrbifoldVOAAssembly
        (LeechLatticeVOAInput.fixedPoint leechInput)
        (LeechLatticeVOAInput.canonicalTwistedModule leechInput)
        (LeechLatticeVOAInput.twistedEvenSector leechInput)

  Vnatural : VOA.VertexOperatorAlgebra
  Vnatural = OrbifoldVOAAssembly.orbifoldVOA orbifoldAssembly

  VnaturalCarrier : Set
  VnaturalCarrier =
    OrbifoldCarrier
      (LeechLatticeVOAInput.fixedPoint leechInput)
      (LeechLatticeVOAInput.canonicalTwistedModule leechInput)
      (LeechLatticeVOAInput.twistedEvenSector leechInput)

  centralCharge24 : Set
  centralCharge24 = OrbifoldVOAAssembly.centralCharge24 orbifoldAssembly

  holomorphic : Set
  holomorphic = OrbifoldVOAAssembly.holomorphic orbifoldAssembly

  simple : Set
  simple = OrbifoldVOAAssembly.simple orbifoldAssembly

open VNaturalConstruction public

constructVNatural :
  (input : LeechLatticeVOAInput) →
  OrbifoldVOAAssembly
    (LeechLatticeVOAInput.fixedPoint input)
    (LeechLatticeVOAInput.canonicalTwistedModule input)
    (LeechLatticeVOAInput.twistedEvenSector input) →
  VNaturalConstruction
constructVNatural input assembly =
  record
    { leechInput = input
    ; orbifoldAssembly = assembly
    }


------------------------------------------------------------------------
-- Actual source-specific direct-summand embedding properties.
-- Unlike weight-two dimension accounting, these proofs identify the
-- original fixed/twisted inclusion maps of the SAME orbifold assembly.
------------------------------------------------------------------------

open import Data.Empty using (⊥)

cong : ∀ {A B : Set} (f : A → B) {x y : A} →
  x ≡ y → f x ≡ f y
cong f refl = refl

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} →
  x ≡ y → y ≡ z → x ≡ z
trans refl q = q

leftSumInjective : ∀ {A B : Set} {x y : A} →
  (inj₁ {B = B} x ≡ inj₁ y) → x ≡ y
leftSumInjective refl = refl

rightSumInjective : ∀ {A B : Set} {x y : B} →
  (inj₂ {A = A} x ≡ inj₂ y) → x ≡ y
rightSumInjective refl = refl

leftRightSumDistinct : ∀ {A B : Set} (x : A) (y : B) →
  inj₁ x ≡ inj₂ y → ⊥
leftRightSumDistinct x y ()

module ActualSelectedSummandInclusions
  (construction : VNaturalConstruction) where

  input : LeechLatticeVOAInput
  input = VNaturalConstruction.leechInput construction

  assembly :
    OrbifoldVOAAssembly
      (LeechLatticeVOAInput.fixedPoint input)
      (LeechLatticeVOAInput.canonicalTwistedModule input)
      (LeechLatticeVOAInput.twistedEvenSector input)
  assembly = VNaturalConstruction.orbifoldAssembly construction

  Fixed : Set
  Fixed = FixedPointVOA.fixedCarrier
    (LeechLatticeVOAInput.fixedPoint input)

  Twisted : Set
  Twisted = TwistedEvenSector.CarrierPlus
    (LeechLatticeVOAInput.twistedEvenSector input)

  originalFixedInclusionInjective : (x y : Fixed) →
    includeFixedSummand assembly x ≡ includeFixedSummand assembly y →
    x ≡ y
  originalFixedInclusionInjective x y eq =
    leftSumInjective
      (trans (sym (fixedSummandIdentifies assembly x))
        (trans (cong (identifyCarrier assembly) eq)
          (fixedSummandIdentifies assembly y)))

  originalTwistedInclusionInjective : (x y : Twisted) →
    includeTwistedSummand assembly x ≡ includeTwistedSummand assembly y →
    x ≡ y
  originalTwistedInclusionInjective x y eq =
    rightSumInjective
      (trans (sym (twistedSummandIdentifies assembly x))
        (trans (cong (identifyCarrier assembly) eq)
          (twistedSummandIdentifies assembly y)))

  originalFixedTwistedDisjoint : (x : Fixed) (y : Twisted) →
    includeFixedSummand assembly x ≡ includeTwistedSummand assembly y →
    ⊥
  originalFixedTwistedDisjoint x y eq =
    leftRightSumDistinct x y
      (trans (sym (fixedSummandIdentifies assembly x))
        (trans (cong (identifyCarrier assembly) eq)
          (twistedSummandIdentifies assembly y)))


  -- Original summands construct a section of the selected carrier
  -- identification. This proves that every tagged direct-sum state is
  -- realized by a selected orbifold state, without asserting that ALL
  -- selected states are in the image (that needs the reverse law).
  SelectedState : Set
  SelectedState =
    VOA.GradedModule.Carrier
      (VOA.VertexOperatorAlgebra.gradedModule
        (OrbifoldVOAAssembly.orbifoldVOA assembly))

  reconstructTaggedState : Fixed ⊎ Twisted → SelectedState
  reconstructTaggedState (inj₁ x) = includeFixedSummand assembly x
  reconstructTaggedState (inj₂ y) = includeTwistedSummand assembly y

  identifyAfterReconstruct :
    (s : Fixed ⊎ Twisted) →
    identifyCarrier assembly (reconstructTaggedState s) ≡ s
  identifyAfterReconstruct (inj₁ x) = fixedSummandIdentifies assembly x
  identifyAfterReconstruct (inj₂ y) = twistedSummandIdentifies assembly y

  reconstructTaggedStateInjective :
    (s t : Fixed ⊎ Twisted) →
    reconstructTaggedState s ≡ reconstructTaggedState t →
    s ≡ t
  reconstructTaggedStateInjective s t eq =
    trans (sym (identifyAfterReconstruct s))
      (trans (cong (identifyCarrier assembly) eq)
        (identifyAfterReconstruct t))


  ----------------------------------------------------------------------
  -- ORIGINAL SOURCE FIBRE NORMALISATION / EXACT V0 NO-JUNK EQUIVALENCE
  --
  -- A retraction from the selected weak VOA carrier to the ACTUAL
  -- orbifold tagged sum is already given by identifyAfterReconstruct.
  -- The canonical state normalizer is therefore an idempotent, and
  -- it distinguishes exactly the fibres of the original identify map.
  -- The missing opposite inverse is EQUIVALENT to identify injectivity:
  -- either one is an acceptable, source-specific V0 acceptance lemma.
  ----------------------------------------------------------------------

  normalizeSelectedState : SelectedState → SelectedState
  normalizeSelectedState w =
    reconstructTaggedState (identifyCarrier assembly w)

  identifyAfterNormalize : (w : SelectedState) →
    identifyCarrier assembly (normalizeSelectedState w)
    ≡ identifyCarrier assembly w
  identifyAfterNormalize w =
    identifyAfterReconstruct (identifyCarrier assembly w)

  normalizeSelectedStateIdempotent : (w : SelectedState) →
    normalizeSelectedState (normalizeSelectedState w)
    ≡ normalizeSelectedState w
  normalizeSelectedStateIdempotent w =
    cong reconstructTaggedState (identifyAfterNormalize w)

  reconstructedStatesAlreadyNormal : (s : Fixed ⊎ Twisted) →
    normalizeSelectedState (reconstructTaggedState s)
    ≡ reconstructTaggedState s
  reconstructedStatesAlreadyNormal s =
    cong reconstructTaggedState (identifyAfterReconstruct s)

  originalSameTagImpliesSameNormalization :
    (x y : SelectedState) →
    identifyCarrier assembly x ≡ identifyCarrier assembly y →
    normalizeSelectedState x ≡ normalizeSelectedState y
  originalSameTagImpliesSameNormalization x y eq =
    cong reconstructTaggedState eq

  sameNormalizationImpliesOriginalSameTag :
    (x y : SelectedState) →
    normalizeSelectedState x ≡ normalizeSelectedState y →
    identifyCarrier assembly x ≡ identifyCarrier assembly y
  sameNormalizationImpliesOriginalSameTag x y eq =
    trans (sym (identifyAfterNormalize x))
      (trans (cong (identifyCarrier assembly) eq)
        (identifyAfterNormalize y))

  -- The exact extra theorem needed for a bidirectional original
  -- selected-carrier identification is injectivity of identifyCarrier.
  -- Do NOT fill it with an arbitrary external Set label.
  NoExtraSelectedStates : Set
  NoExtraSelectedStates =
    (w : SelectedState) → normalizeSelectedState w ≡ w

  OriginalIdentificationInjective : Set
  OriginalIdentificationInjective =
    (x y : SelectedState) →
    identifyCarrier assembly x ≡ identifyCarrier assembly y →
    x ≡ y

  noExtraStatesFromOriginalIdentificationInjective :
    OriginalIdentificationInjective → NoExtraSelectedStates
  noExtraStatesFromOriginalIdentificationInjective injective w =
    injective (normalizeSelectedState w) w
      (identifyAfterNormalize w)

  originalIdentificationInjectiveFromNoExtraStates :
    NoExtraSelectedStates → OriginalIdentificationInjective
  originalIdentificationInjectiveFromNoExtraStates noExtra x y eq =
    trans (sym (noExtra x))
      (trans (cong reconstructTaggedState eq)
        (noExtra y))

  -- Exact two-way replacement for the outstanding V0 no-junk gate.
  -- Neither direction asserts that the needed source evidence exists.
  originalNoExtraStatesIffIdentificationInjective :
    (OriginalIdentificationInjective → NoExtraSelectedStates)
    × (NoExtraSelectedStates → OriginalIdentificationInjective)
  originalNoExtraStatesIffIdentificationInjective =
    noExtraStatesFromOriginalIdentificationInjective ,
    originalIdentificationInjectiveFromNoExtraStates
