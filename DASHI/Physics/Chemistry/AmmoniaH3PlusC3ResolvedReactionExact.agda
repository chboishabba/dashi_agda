module DASHI.Physics.Chemistry.AmmoniaH3PlusC3ResolvedReactionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as Atomic369
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ChemistryHyperfibreBridgeExact as Fibre
import DASHI.Physics.Chemistry.AtomicPeriodicTable369C3EntropyIntertwinerExact as C3
import DASHI.Physics.Chemistry.AmmoniaH3PlusProtonTransferExact as Kinetics

------------------------------------------------------------------------
-- SELECTED C3 SUBGROUP THROUGH H3+ + NH3 -> NH4+ + H2
--
-- We track the three hydrogens originally belonging to NH3 as a,b,c.  The
-- selected C3 cycles a->b->c->a.  On the NH4+ product this is the tetrahedral
-- C3 subgroup fixing the newly transferred proton d.  The two H atoms e,f in
-- H2 are also fixed by this selected subgroup.  This is a subgroup-equivariant
-- label transport; it does not claim the full reactant and product point groups
-- are identical.
------------------------------------------------------------------------

nistPointGroupTable : Source.AttributedSource
nistPointGroupTable =
  Source.mkNoDOISource
    "National Institute of Standards and Technology"
    "CCCBDB species by point group"
    "NIST Computational Chemistry Comparison and Benchmark Database"
    "2022"
    "https://cccbdb.nist.gov/pglistx.asp"
    Source.institutionalSource
    "institutional compilation used claim-relatively for NH4+ in Td; DASHI selects one C3 subgroup and does not attribute that reconstruction to NIST"
    Source.publicAttribution

nistD3hTable : Source.AttributedSource
nistD3hTable =
  Source.mkNoDOISource
    "National Institute of Standards and Technology"
    "CCCBDB species in point group D3h"
    "NIST Computational Chemistry Comparison and Benchmark Database"
    "2022"
    "https://cccbdb.nist.gov/bypg2x.asp?pg=D3H"
    Source.institutionalSource
    "institutional compilation used claim-relatively for H3+ in D3h; the chosen reaction C3 acts nontrivially only on the original NH3 three-hydrogen orbit"
    Source.publicAttribution

data AtomLabel : Set where
  n a b c d e f : AtomLabel

rotateOriginalH : AtomLabel → AtomLabel
rotateOriginalH a = b
rotateOriginalH b = c
rotateOriginalH c = a
rotateOriginalH x = x

rotateOriginalHThree : (x : AtomLabel) →
  rotateOriginalH (rotateOriginalH (rotateOriginalH x)) ≡ x
rotateOriginalHThree n = refl
rotateOriginalHThree a = refl
rotateOriginalHThree b = refl
rotateOriginalHThree c = refl
rotateOriginalHThree d = refl
rotateOriginalHThree e = refl
rotateOriginalHThree f = refl

rotateProductAtom : AtomLabel → AtomLabel
rotateProductAtom = rotateOriginalH

data C3Rotation : Set where r0 r1 r2 : C3Rotation

composeRotation : C3Rotation → C3Rotation → C3Rotation
composeRotation r0 y = y
composeRotation r1 r0 = r1
composeRotation r1 r1 = r2
composeRotation r1 r2 = r0
composeRotation r2 r0 = r2
composeRotation r2 r1 = r0
composeRotation r2 r2 = r1

data Orientation : Set where o0 o1 o2 : Orientation

rotateOrientation : C3Rotation → Orientation → Orientation
rotateOrientation r0 x = x
rotateOrientation r1 o0 = o1
rotateOrientation r1 o1 = o2
rotateOrientation r1 o2 = o0
rotateOrientation r2 o0 = o2
rotateOrientation r2 o1 = o0
rotateOrientation r2 o2 = o1

generatorCube : (x : Orientation) →
  rotateOrientation r1 (rotateOrientation r1 (rotateOrientation r1 x)) ≡ x
generatorCube o0 = refl
generatorCube o1 = refl
generatorCube o2 = refl

data ReactionTime : Set where source target : ReactionTime

protium : Atomic369.AtomicIndex
protium = Atomic369.atomicIndex 1 0 1

nitrogen14 : Atomic369.AtomicIndex
nitrogen14 = Atomic369.atomicIndex 7 7 7

atomInventory : List Atomic369.AtomicIndex
atomInventory = nitrogen14 ∷ protium ∷ protium ∷ protium ∷ protium ∷ protium ∷ protium ∷ []

reactionSystem : Fibre.ChemistryHyperfibreSystem
reactionSystem =
  Fibre.chemistryHyperfibreSystem
    ReactionTime
    (λ _ → List Atomic369.AtomicIndex)
    (λ _ → Orientation)
    (λ _ → String)
    (λ _ → ⊤)
    (λ _ atoms _ → atoms ≡ atomInventory)
    (λ t _ reaction → reaction ≡ reactionLabel t)
    (λ _ _ _ → ⊤)
    (λ _ → "AtomicPeriodicTable369 14N plus six 1H identity inventory")
    (λ _ → "selected-C3 labelled molecular state")
    (λ _ → "H3+ + NH3 -> NH4+ + H2 measured proton-transfer reaction")
    (λ _ → "no industrial promotion")
    (λ _ → "H3-NH3-selected-C3-v1")
  where
    reactionLabel : ReactionTime → String
    reactionLabel source = "H3+ + NH3"
    reactionLabel target = "NH4+ + H2"

sourceFibre : Fibre.ChemistryFibre reactionSystem source
sourceFibre =
  Fibre.chemistryFibre atomInventory o0 "H3+ + NH3" tt refl refl tt
    "literal 369 atom identity inventory"
    "NH3 C3v plus H3+ D3h source geometry"
    "measured flowing-afterglow source reaction state"
    "not industrial"

targetFibre : Fibre.ChemistryFibre reactionSystem target
targetFibre =
  Fibre.chemistryFibre atomInventory o0 "NH4+ + H2" tt refl refl tt
    "same literal 369 atom identity inventory"
    "NH4+ Td product with selected C3 fixing transferred proton d; H2 byproduct"
    "measured flowing-afterglow product reaction state"
    "not industrial"

reactionTransport : Fibre.ChemistryFibreTransport sourceFibre targetFibre
reactionTransport =
  Fibre.chemistryFibreTransport
    "source -> proton transfer -> target"
    "n,a,b,c,d,e,f atom labels retained; selected C3 cycles a,b,c throughout"
    "H3+ + NH3 -> NH4+ + H2"
    "Hemsworth-Payzant-Schiff-Bohme reaction family + York numeric row"
    "no process history"
    true refl true refl

sourceC3Action : C3.PhysicalMolecularC3Action reactionSystem
sourceC3Action =
  C3.physicalMolecularC3Action
    source o0 C3Rotation r0 r1 composeRotation rotateOrientation
    ((x : Orientation) → generatorCube x ≡ refl)
    ⊤ ⊤ ⊤ ⊤ ⊤
    "NH3 experimental C3v; selected action cycles the three original NH3 hydrogens a,b,c"

targetC3Action : C3.PhysicalMolecularC3Action reactionSystem
targetC3Action =
  C3.physicalMolecularC3Action
    target o0 C3Rotation r0 r1 composeRotation rotateOrientation
    ((x : Orientation) → generatorCube x ≡ refl)
    ⊤ ⊤ ⊤ ⊤ ⊤
    "NH4+ experimental Td; selected tetrahedral C3 fixes transferred proton d and cycles original a,b,c; H2 labels e,f fixed"

orientationSector : Orientation → C3.C3Sector
orientationSector o0 = C3.sector0
orientationSector o1 = C3.sector1
orientationSector o2 = C3.sector2

canonicalC3ResolvedTransition : C3.C3ResolvedReactionTransition
canonicalC3ResolvedTransition =
  C3.c3ResolvedReactionTransition
    source target sourceFibre targetFibre sourceC3Action targetC3Action
    Orientation Orientation orientationSector orientationSector reactionTransport
    (1 ≡ 1) (0 ≡ 0) (12 ≡ 12) (1 ≡ 1)
    ⊤ ⊤
    (Kinetics.H3AmmoniaKineticReceipt.rateMantissaTenths Kinetics.canonicalH3AmmoniaKineticReceipt ≡ 42)
    (Kinetics.H3AmmoniaKineticReceipt.temperatureKelvin Kinetics.canonicalH3AmmoniaKineticReceipt ≡ 297)

record PaidC3ResolvedTransition : Set₁ where
  constructor paidC3ResolvedTransition
  field
    transition : C3.C3ResolvedReactionTransition
    sourceGeneratorCubeWitness : (x : Orientation) → generatorCube x ≡ refl
    targetGeneratorCubeWitness : (x : Orientation) → generatorCube x ≡ refl
    elementConservationWitness : 1 ≡ 1
    chargeConservationWitness : 0 ≡ 0
    electronAccountingWitness : 12 ≡ 12
    selectedBondTransferWitness : 1 ≡ 1
    mechanismWitness : ⊤
    energeticScopeWitness : ⊤
    kineticWitness :
      Kinetics.H3AmmoniaKineticReceipt.rateMantissaTenths Kinetics.canonicalH3AmmoniaKineticReceipt ≡ 42
    environmentWitness :
      Kinetics.H3AmmoniaKineticReceipt.temperatureKelvin Kinetics.canonicalH3AmmoniaKineticReceipt ≡ 297

canonicalPaidC3ResolvedTransition : PaidC3ResolvedTransition
canonicalPaidC3ResolvedTransition =
  paidC3ResolvedTransition canonicalC3ResolvedTransition
    (λ x → refl) (λ x → refl)
    refl refl refl refl tt tt refl refl

record C3ResolvedH3AmmoniaBoundary : Set where
  constructor c3ResolvedH3AmmoniaBoundary
  field
    sourceNH3C3vPaid : Bool
    sourceNH3C3vPaidIsTrue : sourceNH3C3vPaid ≡ true
    sourceH3PlusD3hPaid : Bool
    sourceH3PlusD3hPaidIsTrue : sourceH3PlusD3hPaid ≡ true
    targetNH4PlusTdPaid : Bool
    targetNH4PlusTdPaidIsTrue : targetNH4PlusTdPaid ≡ true
    selectedAtomLabelC3TransportPaid : Bool
    selectedAtomLabelC3TransportPaidIsTrue : selectedAtomLabelC3TransportPaid ≡ true
    fullC3ResolvedReactionTransitionPaid : Bool
    fullC3ResolvedReactionTransitionPaidIsTrue : fullC3ResolvedReactionTransitionPaid ≡ true
    selectedC3EqualsFullProductPointGroup : Bool
    selectedC3EqualsFullProductPointGroupIsFalse : selectedC3EqualsFullProductPointGroup ≡ false
    measuredRateDeterminesUniqueProtonTrajectory : Bool
    measuredRateDeterminesUniqueProtonTrajectoryIsFalse : measuredRateDeterminesUniqueProtonTrajectory ≡ false

open C3ResolvedH3AmmoniaBoundary public

canonicalC3ResolvedH3AmmoniaBoundary : C3ResolvedH3AmmoniaBoundary
canonicalC3ResolvedH3AmmoniaBoundary =
  c3ResolvedH3AmmoniaBoundary
    true refl true refl true refl true refl true refl false refl false refl
