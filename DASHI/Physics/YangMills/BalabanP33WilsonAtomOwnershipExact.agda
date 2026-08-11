module DASHI.Physics.YangMills.BalabanP33WilsonAtomOwnershipExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson, "Confinement of Quarks".
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field".
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Give every nonempty subset term in the four-factor Wilson telescope exactly
-- one budget owner.  Four singleton and six pair terms belong to the
-- correlated channel; four triple and one quartic term belong to the deep
-- channel.  This prevents pair leakage into the diagonal budget and prevents
-- any atom from being paid twice.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)
open import Data.List.Base using (length)

open import DASHI.Physics.YangMills.CompactLieProofLevel

data WilsonSubsetAtom : Set where
  singleton0 singleton1 singleton2 singleton3 : WilsonSubsetAtom
  pair01 pair02 pair03 pair12 pair13 pair23 : WilsonSubsetAtom
  triple012 triple013 triple023 triple123 : WilsonSubsetAtom
  quartic0123 : WilsonSubsetAtom

data AtomDegree : Set where
  degree1 degree2 degree3 degree4 : AtomDegree

data BudgetOwner : Set where
  correlatedOwner deepOwner : BudgetOwner

data SignStatus : Set where
  curvatureSensitive youngControlled : SignStatus

atomDegree : WilsonSubsetAtom → AtomDegree
atomDegree singleton0 = degree1
atomDegree singleton1 = degree1
atomDegree singleton2 = degree1
atomDegree singleton3 = degree1
atomDegree pair01 = degree2
atomDegree pair02 = degree2
atomDegree pair03 = degree2
atomDegree pair12 = degree2
atomDegree pair13 = degree2
atomDegree pair23 = degree2
atomDegree triple012 = degree3
atomDegree triple013 = degree3
atomDegree triple023 = degree3
atomDegree triple123 = degree3
atomDegree quartic0123 = degree4

owner : WilsonSubsetAtom → BudgetOwner
owner singleton0 = correlatedOwner
owner singleton1 = correlatedOwner
owner singleton2 = correlatedOwner
owner singleton3 = correlatedOwner
owner pair01 = correlatedOwner
owner pair02 = correlatedOwner
owner pair03 = correlatedOwner
owner pair12 = correlatedOwner
owner pair13 = correlatedOwner
owner pair23 = correlatedOwner
owner triple012 = deepOwner
owner triple013 = deepOwner
owner triple023 = deepOwner
owner triple123 = deepOwner
owner quartic0123 = deepOwner

signStatus : WilsonSubsetAtom → SignStatus
signStatus singleton0 = curvatureSensitive
signStatus singleton1 = curvatureSensitive
signStatus singleton2 = curvatureSensitive
signStatus singleton3 = curvatureSensitive
signStatus pair01 = youngControlled
signStatus pair02 = youngControlled
signStatus pair03 = youngControlled
signStatus pair12 = youngControlled
signStatus pair13 = youngControlled
signStatus pair23 = youngControlled
signStatus triple012 = youngControlled
signStatus triple013 = youngControlled
signStatus triple023 = youngControlled
signStatus triple123 = youngControlled
signStatus quartic0123 = youngControlled

allSubsetAtoms : List WilsonSubsetAtom
allSubsetAtoms =
  singleton0 ∷ singleton1 ∷ singleton2 ∷ singleton3 ∷
  pair01 ∷ pair02 ∷ pair03 ∷ pair12 ∷ pair13 ∷ pair23 ∷
  triple012 ∷ triple013 ∷ triple023 ∷ triple123 ∷
  quartic0123 ∷ []

correlatedAtoms : List WilsonSubsetAtom
correlatedAtoms =
  singleton0 ∷ singleton1 ∷ singleton2 ∷ singleton3 ∷
  pair01 ∷ pair02 ∷ pair03 ∷ pair12 ∷ pair13 ∷ pair23 ∷ []

deepAtoms : List WilsonSubsetAtom
deepAtoms =
  triple012 ∷ triple013 ∷ triple023 ∷ triple123 ∷ quartic0123 ∷ []

allSubsetAtomCountExact : length allSubsetAtoms ≡ 15
allSubsetAtomCountExact = refl

correlatedAtomCountExact : length correlatedAtoms ≡ 10
correlatedAtomCountExact = refl

deepAtomCountExact : length deepAtoms ≡ 5
deepAtomCountExact = refl

correlatedAndDeepCountExact :
  length correlatedAtoms + length deepAtoms ≡ length allSubsetAtoms
correlatedAndDeepCountExact = refl

ownerCannotBeBoth : ∀ atom →
  owner atom ≡ correlatedOwner → owner atom ≡ deepOwner → ⊥
ownerCannotBeBoth singleton0 refl ()
ownerCannotBeBoth singleton1 refl ()
ownerCannotBeBoth singleton2 refl ()
ownerCannotBeBoth singleton3 refl ()
ownerCannotBeBoth pair01 refl ()
ownerCannotBeBoth pair02 refl ()
ownerCannotBeBoth pair03 refl ()
ownerCannotBeBoth pair12 refl ()
ownerCannotBeBoth pair13 refl ()
ownerCannotBeBoth pair23 refl ()
ownerCannotBeBoth triple012 ()
ownerCannotBeBoth triple013 ()
ownerCannotBeBoth triple023 ()
ownerCannotBeBoth triple123 ()
ownerCannotBeBoth quartic0123 ()

record AtomSignature : Set where
  constructor atomSignature
  field
    atom : WilsonSubsetAtom
    degree : AtomDegree
    chargeOwner : BudgetOwner
    sign : SignStatus

signature : WilsonSubsetAtom → AtomSignature
signature atom = atomSignature atom (atomDegree atom) (owner atom) (signStatus atom)

pairTermsAreCorrelated : owner pair01 ≡ correlatedOwner
pairTermsAreCorrelated = refl

tripleTermsAreDeep : owner triple012 ≡ deepOwner
tripleTermsAreDeep = refl

wilsonAtomOwnershipLevel : ProofLevel
wilsonAtomOwnershipLevel = machineChecked
