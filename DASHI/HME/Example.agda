module DASHI.HME.Example where

open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List.Relation.Unary.All using ([]; _∷_)

open import DASHI.HME.Path
open import DASHI.Geometry.TimeOrientation using (mono)
open import DASHI.Geometry.ConeArrowIsotropyOrbitProfile using (AbstractOrbitProfile)
open import DASHI.Physics.ClosureGlue using (ClosureAxioms; T)

record ExampleContext : Set₁ where
  field
    closure : ClosureAxioms
    hme : CanonicalContext closure
    seed : ClosureAxioms.S closure
    seed-cone : CanonicalContext.cone hme seed
    witness-profile : AbstractOrbitProfile

open ExampleContext public

examplePath : (ctx : ExampleContext) → Path (T (closure ctx))
examplePath ctx = idPath (seed ctx)

exampleAdmissible : (ctx : ExampleContext) → Admissible (closure ctx) (hme ctx)
exampleAdmissible ctx =
  record
    { path = examplePath ctx
    ; cone-ok = seed-cone ctx ∷ []
    ; mdl-ok = mono (CanonicalContext.orientation (hme ctx)) (seed ctx) ∷ []
    }

exampleProof : (ctx : ExampleContext) → Proof (closure ctx) (hme ctx)
exampleProof ctx =
  record
    { admissible = exampleAdmissible ctx
    ; witness = witness-profile ctx
    }
