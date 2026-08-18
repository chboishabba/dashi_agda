# SIO semantic surface bridge

## Reference

Michel Dumontier, Christopher JO Baker, Joachim Baran, Alison Callahan, Leonid Chepelev, José Cruz-Toledo, Nicholas R Del Rio, Geraint Duck, Laura I Furlong, Nichealla Keath, Dana Klassen, Jamie P McCusker, Núria Queralt-Rosinach, Matthias Samwald, Natalia Villanueva-Rosales, Mark D Wilkinson, Robert Hoehndorf. **“The Semanticscience Integrated Ontology (SIO) for biomedical research and knowledge discovery.”** *Journal of Biomedical Semantics* **5**, 14 (2014). DOI: **10.1186/2041-1480-5-14**.

SIO provides an interoperable RDF/OWL vocabulary for entities, processes, attributes, information entities, values, units, evidence and roles. The DASHI bridge deliberately does **not** reimplement SIO. It interprets an ontology-facing SIO description as a public semantic surface over the existing DASHI carrier/evidence/provenance machinery.

## Architecture

The intended layering is

\[
\boxed{
\text{fine carrier}
\xrightarrow{\text{DASHI projection}}
\text{semantic surface}
\xrightarrow{\text{SIO encoding}}
\text{RDF/OWL consumers}
}
\]

with a separately retained provenance receipt when exact reopening is required.

The implementation reuses:

- `DASHI.Core.FibreRestrictionCore` for the carrier/surface/evidence distinction;
- `DASHI.Core.ProvenanceBearingQuotient` for exact reopening and the rule that provenance is not semantic-erasure authority;
- the new `DASHI.Core.ObserverRefinementCore` for observer-family refinement, incomparability and joins.

The SIO-specific file is `DASHI.Semantics.SIOSemanticSurfaceBridge`.

## Observation and measurement surfaces

`SIOObservationSurface` adds ontology-facing information entities and the familiar measurement pattern

\[
\text{surface}
\longrightarrow
\text{information entity}
\xrightarrow{\text{denotes attribute}}
\text{attribute},
\]

with separate `hasValue` and `hasUnit` relations.

This is intentionally weaker than identification of the information entity with the fine carrier. The carrier/surface distinction remains owned by `FibreRestrictionCore`.

## Evidence is not proof authority

`SIOEvidenceSurface` supports graph-level relations

\[
\text{supports},\qquad
\text{disputes},\qquad
\text{refutes}.
\]

The canonical boundary proves that the authority token `graphAssertionOnly` has no inhabitant of `WorldTruthPermission`:

\[
\boxed{
\text{SIO graph evidence assertion}
\not\Rightarrow
\text{world truth authority}.
}
\]

This is the ontology-facing counterpart of the existing DASHI rule

\[
\boxed{
\text{evidence restricts fibre}
\neq
\text{evidence recovers carrier}
\neq
\text{evidence promotes truth}.
}
\]

## Roles are not current authority

`SIORoleSurface` separates

\[
\text{bearsRole}(e,r),
\qquad
\text{realizes}(p,r),
\qquad
\text{currentlyAuthorized}(e,r).
\]

The bridge deliberately provides no promotion from a role assertion to current authority. The theorem

`SioRoleAssertionCannotCreateCurrentAuthority`

is represented in code as `sioRoleAssertionCannotCreateCurrentAuthority` and witnesses

\[
\boxed{
\text{historical/social/process role assertion}
\not\Rightarrow
\text{present authorization}.
}
\]

This keeps SIO-style role modelling compatible with DASHI’s stronger revocation, present-will and authority-indexed modules.

## Reopenable public semantic surfaces

`ReopenableSIOSurface` composes an `SIOObservationSurface` with an existing `ProvenanceBearingQuotient`.

For every fine state \(x\),

\[
\boxed{
\operatorname{reopen}
(\operatorname{project}(x),\operatorname{receipt}(x))
=x.
}
\]

The theorem is `reopenProjectedExactly`.

Importantly, RDF/OWL encoding of the projected surface does not itself provide the receipt and does not authorize erasure of distinctions hidden by the projection.

## Attribute observers form a refinement partial order

The generic `ObserverRefinementCore` defines

\[
O_A \preceq O_B
\quad\Longleftrightarrow\quad
O_A(x)=O_A(y)
\Rightarrow
O_B(x)=O_B(y).
\]

Thus \(O_A\) is at least as informative as \(O_B\): every fibre of \(O_A\) lies inside a fibre of \(O_B\).

A `CrossCollision` consists of witnesses

\[
O_A(x)=O_A(y),\quad O_B(x)\neq O_B(y)
\]

and

\[
O_B(u)=O_B(v),\quad O_A(u)\neq O_A(v).
\]

The theorem

`crossCollisionImpliesIncomparable`

then proves

\[
\boxed{
O_A\not\preceq O_B
\quad\land\quad
O_B\not\preceq O_A.
}
\]

This directly captures the observer-incomparability pattern that has appeared in the exact Base369/representation examples.

## Pairing is the binary join

The paired observer is

\[
O_{A\times B}(x)=(O_A(x),O_B(x)).
\]

The core proves:

\[
O_{A\times B}\preceq O_A,
\qquad
O_{A\times B}\preceq O_B,
\]

and under a cross-collision each refinement is strict.

More importantly, if another observer \(O\) refines both \(O_A\) and \(O_B\), then

\[
\boxed{
O\preceq O_{A\times B}.
}
\]

This is `jointRefinesPair`. Therefore the paired observer is the least joint refinement, up to observational equivalence.

The SIO bridge reexports this interpretation through:

- `sioCrossCollisionImpliesIncomparable`;
- `sioPairedObserverStrictlyRefinesBoth`;
- `sioPairedObserverIsLeastJointRefinement`.

This gives multiple SIO attributes a precise mathematical semantics: they need not lie on a single information ladder; they can be transverse coordinates whose correct combined public surface is their join.

## Practical interpretation

The resulting stack is

\[
\boxed{
\begin{array}{c}
\text{DASHI fine carrier / world state}\\
\downarrow\\
\text{DASHI observer + provenance fibre}\\
\downarrow\\
\text{SIO information / attribute / evidence / role surface}\\
\downarrow\\
\text{RDF, Wikidata, ITIR and scientific-data consumers}
\end{array}
}
\]

SIO supplies public vocabulary and interoperability. DASHI supplies the proof-relevant rules governing what projection, evidence, role assertions and reopening actually license.
