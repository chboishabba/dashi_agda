module DASHI.Philosophy.PatternPreservingTeaching where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Knowledge is laminated across registers and teaching is pattern-preserving
-- participation, not merely transfer of a compressed object.

record KnowledgeRegisters
       (Sensory Practical Ecological Historical Ethical : Set) : Set₁ where
  field
    sensory :
      Sensory

    practical :
      Practical

    ecological :
      Ecological

    historical :
      Historical

    ethical :
      Ethical

open KnowledgeRegisters public

record PatternPreservingTeaching
       (Teacher Learner Place Practice Pattern : Set) : Set₁ where
  field
    teacher :
      Teacher

    learner :
      Learner

    place :
      Place

    practice :
      Practice

    localPattern :
      Pattern

    learnerEntersRelation :
      Set

    patternPreserved :
      Set

    teacherAlsoTransformed :
      Set

    wholeTraditionEncodedInLesson :
      Bool

    representationAuthorityClaimed :
      Bool

open PatternPreservingTeaching public

record TeachingBoundary : Set where
  constructor mkTeachingBoundary
  field
    localLessonCanCarryRelationalPattern :
      Bool

    localLessonEqualsWholeTradition :
      Bool

    culturalAuthorityAutomaticallyPromoted :
      Bool

open TeachingBoundary public

canonicalTeachingBoundary :
  TeachingBoundary
canonicalTeachingBoundary =
  mkTeachingBoundary
    true
    false
    false

canonicalLessonIsNotWholeTradition :
  localLessonEqualsWholeTradition canonicalTeachingBoundary
  ≡
  false
canonicalLessonIsNotWholeTradition =
  refl
