# Relational Shared-State and Process-Bearing Response Formalism

This document abstracts a recurring parent–child communication pattern without treating either role as a diagnosis or moral identity. The same structures may apply to other caregiving, dependent, familial, clinical, administrative, or institutional relationships.

## 1. Shared-state update

A conversation maintains a provisional shared state

\[
S_t=(O_t,C_t,P_t,Q_t,A_t,D_t,H_t,U_t,R_t),
\]

where:

- \(O_t\) is the current conversational object;
- \(C_t\) is the ordered contribution history;
- \(P_t\) is the typed durable-preference state;
- \(Q_t\) is the set of unresolved questions;
- \(A_t\) records assents and refusals;
- \(D_t\) is the current decision and provenance;
- \(H_t\) is retained decision history;
- \(U_t\) records attributed future obligations;
- \(R_t\) records unresolved rupture status.

`DurablePreference` is not merely a preference utterance. It records owner, label, scope, time, and provenance. A preference contribution enters \(P_t\) only through an explicit `DurablePreferenceTransition`.

A contribution may be heard without being taken up:

\[
\operatorname{Heard}(c)\not\Rightarrow\operatorname{Uptaken}(c).
\]

The Agda `Uptaken c before after` contract is proof-carrying. It requires a `ContributionTransition c before after` proving:

1. the after-state contribution history is exactly
   \[
   C_{t+1}=c::C_t;
   \]
2. the contribution is classified as a retained non-question, an open question, a question resolved by assent, or a question resolved by refusal;
3. the durable-preference list is either preserved for a non-preference contribution or extended by a preference whose owner and label match the contribution;
4. both the prior and current decision records occur in the after-state decision history.

Thus the type does not permit an `Uptaken` witness relating an arbitrary contribution to unrelated before and after states.

Object displacement is different. Its proof requires that a replacement object becomes operative and that the original contribution is not retained in the after-state contribution list.

## 2. Pseudo-consultation and provenance

Consultation is genuine only when the consulted contribution enters the decision procedure as actual information. It does not give the consulted person unilateral control, but the decision must be sensitive to their input.

The following implications are invalid:

\[
\operatorname{Asked}(y,p)\not\Rightarrow\operatorname{Agreed}(y,p),
\]

\[
\operatorname{Discussed}(p)\not\Rightarrow\operatorname{JointlyDecided}(p),
\]

\[
\operatorname{NoReply}(y,p)\not\Rightarrow\operatorname{Assent}(y,p).
\]

If a participant does not answer and action is necessary, the correct provenance is *unilateral decision due to no recorded response*, not *joint decision*.

## 3. Conditional proposition trees

The object of response is normally not an atomic proposition. It is an exact guarded node

\[
n=(\Gamma,\alpha,\mu,\tau,\omega,\epsilon,\kappa)
\]

within a refinement tree, where the fields encode context, contemplated action, modality, temporal scope, practical extent, exceptions, and unresolved conditions.

The general response object is

\[
\operatorname{ActualResponse}(x,n,d,t),
\]

indexed internally by participant, node, decision episode, and time.

Affirmation is local. It does not automatically transport to descendant tasks, broader antecedents, stronger modalities, larger practical scopes, later decision episodes, or changed capacity states.

In particular,

\[
\operatorname{Affirm}(\mathsf{Consider}(z)\mid\Gamma)
\not\Rightarrow
\operatorname{Affirm}(\mathsf{Commit}(z)\mid\Gamma').
\]

### Exact transport

`ResponseTransportWitness source target` contains propositional equalities proving preservation of:

- antecedent;
- contemplated action;
- modality;
- temporal scope;
- practical scope;
- exceptions;
- unresolved conditions.

`transportResponse` additionally requires a proof that the original response targets `source`. It returns an `ActualResponse` targeting `target` while preserving the response state and decision episode.

This is re-addressing under semantic equality, not broadening. If modality, context, or scope becomes stronger, exact transport is unavailable. `FreshStrengthenedResponse source target` instead requires a distinct new response targeting the stronger node, with the original retained only as provenance.

A statement that an option *might be considered* can positively affirm branch liveness while leaving the option itself unresolved:

\[
+1\text{ toward }\mathsf{MightConsider}(z),
\qquad
z=0_{\mathrm{open}}.
\]

## 4. Refined zero

A bare zero destroys important historical distinctions. Relevant zero states include:

\[
0_{\mathrm{absent}},
0_{\mathrm{open}},
0_{\mathrm{suspended}},
0_{\mathrm{blocked}},
0_{\mathrm{expired-unweighed}},
0_{\mathrm{handover}},
0_{\mathrm{completed-neutral}}.
\]

Hence:

\[
0_{\mathrm{expired-unweighed}}\neq -1_{\mathrm{rejected}}.
\]

Memory must retain whether a branch was rejected, blocked, expired, abandoned, or remained pending.

## 5. Future-capacity capture

Ambiguous present participation can later be rewritten as an obligation against another person's future labour:

\[
\operatorname{Invitation}_t
\to
\operatorname{AttributedCommitment}_{t+1}
\to
\operatorname{DemandOnFutureCapacity}.
\]

The protective invariant is implemented as an exact projection:

\[
\operatorname{FutureObligation}(x,a)
\Rightarrow
\operatorname{ExplicitCommitmentEvidence}(x,a).
\]

`ExplicitCommitmentEvidence x a` contains a typed representation together with proofs that its owner is \(x\), its representation type is `commitmentRepresentation`, and its label is exactly \(a\).

`futureObligationRequiresExplicitCommitment` extracts this evidence from every valid `FutureObligation`. Conversely, `FutureCapacityCapture` carries a function proving that no such evidence exists for the later attributed commitment.

This matters most where capacity is scarce or unpredictable because attribution errors are not cheaply reversible.

## 6. Causal order and defensive reversal

Conflict reconstruction should preserve

\[
\text{act}\to\text{impact}\to\text{objection}\to\text{defensive response}.
\]

The objection and its delivery may require review, but they must not erase the event that prompted them.

A defensive route may transform a concrete complaint into an unparticularised counter-allegation. A request for exact particulars can then itself be reframed as further misconduct, generating recursive conflict expansion:

\[
\mathcal D(M,x)=(M\text{ unresolved},x\text{ newly accused}).
\]

“DARVO-like” is therefore used only as a cautious structural descriptor. It is not inferred without incident reconstruction, and the formalism does not establish deliberate strategy or the truth of the initiating allegation.

## 7. Experience reports and behavioural allegations

These are differently typed:

- “That felt accusatory” is an experience report.
- “You gaslit me” is a behavioural allegation.

A behavioural allegation requires an actor, observable particular, context, affected person, alleged effect, and evidential receipt. Requesting particulars does not negate the reported feeling; it makes behavioural repair determinate.

## 8. Partial family-name intrusion

`CorrectedNameIntrusion` is deliberately an observation record. It may contain uncertain coding and does not by itself establish that an event was corrected, non-composite, or referentially distinct.

The proof-bearing subtype is

\[
\operatorname{ValidatedCorrectedNameIntrusion}(e).
\]

A value of this type proves immediate self-correction, no deliberate composite label, distinct intended and competing referent roles, speaker-role distinction from each referent, and agreement between each candidate role and the corresponding referent role.

Only the validated subtype supports the phrase *corrected name intrusion* as a guaranteed classification.

The relevant sequence may be:

\[
\text{intended name activation}
+
\text{competing family-name activation}
\to
\text{partial intrusion}
\to
\text{monitoring and correction}.
\]

Freud's parapraxis framework supplies historical provenance for asking whether slips can reflect structured association. Modern lexical-access and speech-error models supply a less motive-heavy account in terms of competing semantic, lexical, phonological, and affective activation.

The evidence boundary is:

\[
\operatorname{PartialSlip}
\not\Rightarrow
\operatorname{DeliberateComparison},
\]

\[
\operatorname{PartialSlip}
\not\Rightarrow
\operatorname{StableIdentitySubstitution},
\]

\[
\operatorname{PartialSlip}
\not\Rightarrow
\operatorname{RecoveredHiddenMotive}.
\]

Repeated context-sensitive intrusions may support a defeasible associative-transport hypothesis, but current acts must still be evaluated on current evidence.

## 9. Process-bearing branches and memory

Some propositions authorise extended goal processes rather than atomic acts. A goal branch may carry applications, documents, contacts, queue positions, learned constraints, pending responses, deadlines, external dependencies, assigned participants, and handover obligations even while its outcome remains absent:

\[
G_t=0\not\Rightarrow S_t=0.
\]

A PNF memory should retain branch status, liveness layer, capacity, unresolved residual, alternatives, and provenance rather than quotienting every unrealised outcome into “nothing happened.”

Revocation changes which future transitions remain authorised; it does not erase completed acts, pending external processing, closure requirements, or accumulated state:

\[
\operatorname{AuthorityRevoked}
\neq
\operatorname{ProcessStateErased}.
\]

Quantitative promotion is synchronized. A family refinement carries one authoritative list of branch refinements and proves:

\[
\begin{aligned}
\text{qualitative branches}
&=\operatorname{map}(\text{qualitativeBranch},R),\\
\text{portfolio metrics}
&=\operatorname{map}(\text{selectionMetric},R),\\
\text{branch waves}
&=\operatorname{map}(\text{branchWave},R).
\end{aligned}
\]

Each branch refinement also proves metric identity and cost preservation and exact derivation of its wave from the qualitative branch's recorded amplitude and phase. Foreign, missing, or duplicated metrics and waves therefore cannot inhabit the synchronized refinement type.

Hyperformal incidence requires a membership proof that the participant occurs in the branch's `assignedParticipants`; it is not true by construction for every participant–branch pair.

## 10. Feasibility filtration

A named branch may be logically imaginable without being institutionally available, economically survivable, accessible to the agent, compatible with capacity, or temporally live.

Represent liveness as a vector over layers:

\[
\mathbf L(B,t)=
(L_{\mathrm{logical}},L_{\mathrm{institutional}},L_{\mathrm{economic}},L_{\mathrm{agent}},L_{\mathrm{capacity}},L_{\mathrm{temporal}}).
\]

Thus:

\[
\operatorname{NamedOption}(B)
\not\Rightarrow
\operatorname{FeasibleOption}(B).
\]

## 11. Attractor alignment and branch interference

More branches do not necessarily improve outcomes. A branch must be serviceable and usefully tend toward the desired attractor.

Qualitatively, a branch may be aligned, orthogonal, opposed, or of unknown alignment. Pairs of branches may interfere constructively, neutrally, destructively, or incoherently through shared resources, incompatible requirements, conflicting provenance, or timing.

The portfolio optimizer accepts only a `ValidatedInteractions branches` matrix. Its upper-triangular type contains exactly one cell for each unordered pair of list positions, has no diagonal cell, and cannot mention a foreign branch endpoint. Only interactions represented in that validated matrix contribute to benefit or burden.

A useful branch family should remain within servicing capacity, improve attractor reachability, preserve useful optionality, value information gain, penalise destructive interference, and distinguish visible activity from genuine progress.

## 12. Trauma and memory deformation

A traumatic history may alter later branch-management weights. It can produce either branch hoarding, because closure feels dangerous, or premature pruning, because similar branches are expected to fail or harm.

This is represented as a defeasible transition deformation, not a diagnosis. A sound model records whether the transported constraint remains context-sensitive.

## 13. Repair invariants

A minimally corrigible relational process preserves:

1. open conversational objects until answered, explicitly deferred, or withdrawn by their originator;
2. exact proposition identity, context, modality, scope, and time;
3. durable preference and decision-history provenance;
4. feeling–fact–allegation type separation;
5. causal order;
6. particularity of serious allegations;
7. unresolved rupture status until bilateral repair;
8. future-capacity protection;
9. care/accountability separation;
10. person-specific evaluation rather than inherited family substitution;
11. prior versions and provenance when accounts change;
12. a non-retaliatory correction channel.

The central law is:

\[
\boxed{
\text{A response may be re-addressed only under a proof that every semantic node coordinate is preserved. Any strengthening requires a fresh response.}
}
\]
