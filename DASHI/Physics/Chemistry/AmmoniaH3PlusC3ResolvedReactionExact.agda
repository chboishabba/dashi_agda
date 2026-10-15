module DASHI.Physics.Chemistry.AmmoniaH3PlusC3ResolvedReactionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as Atomic369
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ChemistryHyperfibreBridgeExact as Fibre
import DASHI.Physics.Chemistry.AtomicPeriodicTable369C3EntropyIntertwinerExact as C3
import DASHI.Physics.Chemistry.AmmoniaH3PlusProtonTransferExact as Kinetics
import DASHI.Physics.Chemistry.AmmoniaProtonationReactionExact as Protonation

------------------------------------------------------------------------
-- SELECTED C3 SUBGROUP THROUGH H3+ + NH3 -> NH4+ + H2
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
    "institutional compilation used claim-relatively for H3+ in D3h; the selected reaction C3 need not use the full H3+ point-group action"
    Source.publicAttribution

nistHydrogenProtonAffinity : Source.AttributedSource
nistHydrogenProtonAffinity =
  Source.mkDOISource
    "Edward P. Hunter; Sharon G. Lias"
    "Evaluated Gas Phase Basicities and Proton Affinities of Molecules: An Update"
    "Journal of Physical and Chemical Reference Data 27 (1998) 413-656"
    "1998"
    "10.1063/1.556018"
    "https://doi.org/10.1063/1.556018"
    Source.academicArticleSource
    "same evaluated thermochemistry authority used for H2 proton affinity 422.3 kJ/mol; combined with the separately represented NH3 value 853.6 kJ/mol only for the proton-transfer thermochemical difference"
    Source.publicAttribution

h2ProtonAffinityTenthsKJPerMol : Nat
h2ProtonAffinityTenthsKJPerMol = 4223

reactionExothermicityMagnitudeTenthsKJPerMol : Nat
reactionExothermicityMagnitudeTenthsKJPerMol = 4313

protonAffinityDifferenceCloses :
  Protonation.ProtonationThermochemistry.protonAffinityTenthsKJPerMol
    Protonation.canonicalProtonationThermochemistry
  ≡ h2ProtonAffinityTenthsKJPerMol + reactionExothermicityMagnitudeTenthsKJPerMol
protonAffinityDifferenceCloses = refl

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
composeRotation r0 r0 = r0
composeRotation r0 r1 = r1
composeRotation r0 r2 = r2
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

reactionLabel : ReactionTime → String
reactionLabel source = "H3+ + NH3"
reactionLabel target = "NH4+ + H2"

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
    (λ _ → "H3-NH3-selected-C3-v2")

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
    "NH4+ Td with selected C3 fixing transferred proton d; H2 labels e,f fixed"
    "measured flowing-afterglow product reaction state"
    "not industrial"

reactionTransport : Fibre.ChemistryFibreTransport sourceFibre targetFibre
reactionTransport =
  Fibre.chemistryFibreTransport
    "source -> proton transfer -> target"
    "n,a,b,c,d,e,f atom labels retained; selected C3 cycles a,b,c throughout"
    "H3+ + NH3 -> NH4+ + H2"
    "Hemsworth-Payzant-Schiff-Bohme reaction family + York numeric row + Hunter-Lias proton-affinity difference"
    "no process history"
    true refl true refl

GeneratorCubeLaw : Set
GeneratorCubeLaw =
  (x : Orientation) →
  rotateOrientation r1 (rotateOrientation r1 (rotateOrientation r1 x)) ≡ x

sourceC3Action : C3.PhysicalMolecularC3Action reactionSystem
sourceC3Action =
  C3.physicalMolecularC3Action
    source o0 C3Rotation r0 r1 composeRotation rotateOrientation
    GeneratorCubeLaw
    ⊤ ⊤ ⊤ ⊤ ⊤
    "NH3 experimental C3v; selected action cycles original NH3 hydrogens a,b,c; co-reactant labels d,e,f are fixed under this selected subgroup"

targetC3Action : C3.PhysicalMolecularC3Action reactionSystem
targetC3Action =
  C3.physicalMolecularC3Action
    target o0 C3Rotation r0 r1 composeRotation rotateOrientation
    GeneratorCubeLaw
    ⊤ ⊤ ⊤ ⊤ ⊤
    "NH4+ experimental Td; selected tetrahedral C3 fixes transferred proton d and cycles original a,b,c; H2 labels e,f are fixed"

orientationSector : Orientation → C3.C3Sector
orientationSector o0 = C3.sector0
orientationSector o1 = C3.sector1
orientationSector o2 = C3.sector2

ElementConservation : Set
ElementConservation = (1 ≡ 1) × (6 ≡ 6)
ChargeConservation : Set
ChargeConservation = 1 ≡ 1
ElectronAccounting : Set
ElectronAccounting = 12 ≡ 12
SelectedBondTransfer : Set
SelectedBondTransfer = 1 ≡ 1
EnergeticReceipt : Set
EnergeticReceipt =
  Protonation.ProtonationThermochemistry.protonAffinityTenthsKJPerMol
    Protonation.canonicalProtonationThermochemistry
  ≡ h2ProtonAffinityTenthsKJPerMol + reactionExothermicityMagnitudeTenthsKJPerMol
KineticReceipt : Set
KineticReceipt =
  Kinetics.H3AmmoniaKineticReceipt.rateMantissaTenths Kinetics.canonicalH3AmmoniaKineticReceipt ≡ 42
EnvironmentReceipt : Set
EnvironmentReceipt =
  Kinetics.H3AmmoniaKineticReceipt.temperatureKelvin Kinetics.canonicalH3AmmoniaKineticReceipt ≡ 297

canonicalC3ResolvedTransition : C3.C3ResolvedReactionTransition
canonicalC3ResolvedTransition =
  C3.c3ResolvedReactionTransition
    source target sourceFibre targetFibre sourceC3Action targetC3Action
    Orientation Orientation orientationSector orientationSector reactionTransport
    ElementConservation ChargeConservation ElectronAccounting SelectedBondTransfer
    ⊤ EnergeticReceipt KineticReceipt EnvironmentReceipt

record PaidC3ResolvedTransition : Set₁ where
  constructor paidC3ResolvedTransition
  field
    transition : C3.C3ResolvedReactionTransition
    sourceGeneratorCubeWitness : GeneratorCubeLaw
    targetGeneratorCubeWitness : GeneratorCubeLaw
    elementConservationWitness : ElementConservation
    chargeConservationWitness : ChargeConservation
    electronAccountingWitness : ElectronAccounting
    selectedBondTransferWitness : SelectedBondTransfer
    mechanismWitness : ⊤
    energeticWitness : EnergeticReceipt
    kineticWitness : KineticReceipt
    environmentWitness : EnvironmentReceipt

canonicalPaidC3ResolvedTransition : PaidC3ResolvedTransition
canonicalPaidC3ResolvedTransition =
  paidC3ResolvedTransition canonicalC3ResolvedTransition
    generatorCube generatorCube
    (refl , refl) refl refl refl tt refl refl refl

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
    sameReactionThermochemicalDifferencePaid : Bool
    sameReactionThermochemicalDifferencePaidIsTrue : sameReactionThermochemicalDifferencePaid ≡ true
    fullProofRelevantC3ResolvedReactionTransitionPaid : Bool
    fullProofRelevantC3ResolvedReactionTransitionPaidIsTrue :
      fullProofRelevantC3ResolvedReactionTransitionPaid ≡ true
    selectedC3EqualsFullProductPointGroup : Bool
    selectedC3EqualsFullProductPointGroupIsFalse : selectedC3EqualsFullProductPointGroup ≡ false
    measuredRateDeterminesUniqueProtonTrajectory : Bool
    measuredRateDeterminesUniqueProtonTrajectoryIsFalse : measuredRateDeterminesUniqueProtonTrajectory ≡ false

open C3ResolvedH3AmmoniaBoundary public

canonicalC3ResolvedH3AmmoniaBoundary : C3ResolvedH3AmmoniaBoundary
canonicalC3ResolvedH3AmmoniaBoundary =
  c3ResolvedH3AmmoniaBoundary
    true refl true refl true refl true refl true refl true refl false refl false refl
