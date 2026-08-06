module DASHI.Biology.TernaryLogicRelaxationSourceAtlas where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.Round5SourceAtlas as Sources

------------------------------------------------------------------------
-- Sources for the explicit separation of many-valued logic from cyclic group
-- arithmetic and for differentiable categorical relaxations.  The finite Agda
-- modules do not assume that any relaxation is an exact logical semantics.

kleeneMetamathematicsSource : Sources.SourceRecord
kleeneMetamathematicsSource =
  Sources.sourceRecord
    "Stephen Cole Kleene"
    "Introduction to Metamathematics"
    "North-Holland Publishing Company"
    1952
    "No DOI assigned to the book"
    "Supports treating truth tables, designated values, connectives, and consequence as explicit logical structure rather than residue names."
    "The finite ordered three-value table is not identified with every Kleene logic or with cyclic addition in Z/3Z."

jangGumbelSoftmaxSource : Sources.SourceRecord
jangGumbelSoftmaxSource =
  Sources.sourceRecord
    "Eric Jang; Shixiang Gu; Ben Poole"
    "Categorical Reparameterization with Gumbel-Softmax"
    "International Conference on Learning Representations"
    2017
    "10.48550/arXiv.1611.01144"
    "Supports temperature-controlled differentiable relaxation of categorical one-hot variables."
    "The finite temperature labels do not implement a Gumbel sampler, gradient estimator, or zero-temperature convergence theorem."

maddisonConcreteSource : Sources.SourceRecord
maddisonConcreteSource =
  Sources.sourceRecord
    "Chris J. Maddison; Andriy Mnih; Yee Whye Teh"
    "The Concrete Distribution: A Continuous Relaxation of Discrete Random Variables"
    "International Conference on Learning Representations"
    2017
    "10.48550/arXiv.1611.00712"
    "Supports continuous simplex-valued relaxations of discrete categorical variables and annealing semantics."
    "The cyclic-convolution mass law is exact discrete algebra and is not promoted to a Concrete-distribution reparameterisation."

canonicalTernaryLogicRelaxationSources : List Sources.SourceRecord
canonicalTernaryLogicRelaxationSources =
  kleeneMetamathematicsSource
  ∷ jangGumbelSoftmaxSource
  ∷ maddisonConcreteSource
  ∷ []

ternaryLogicRelaxationSourceCount : List Sources.SourceRecord → Nat
ternaryLogicRelaxationSourceCount [] = 0
ternaryLogicRelaxationSourceCount (_ ∷ sources) =
  suc (ternaryLogicRelaxationSourceCount sources)

canonicalTernaryLogicRelaxationSourceCount : Nat
canonicalTernaryLogicRelaxationSourceCount =
  ternaryLogicRelaxationSourceCount canonicalTernaryLogicRelaxationSources

canonicalTernaryLogicRelaxationSourceCountIsThree :
  canonicalTernaryLogicRelaxationSourceCount ≡ 3
canonicalTernaryLogicRelaxationSourceCountIsThree = refl
