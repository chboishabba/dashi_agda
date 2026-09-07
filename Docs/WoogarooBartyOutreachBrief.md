# Save Woogaroo Forest — Ash Barty outreach brief

## Purpose

This brief supports one bounded outreach action: a respectful private invitation to Ash Barty or an authorised Ash Barty Foundation representative to receive a factual briefing and, if interested, take a private site walk in the Opossum Creek / Woogaroo landscape.

It does **not** assert that Ash Barty supports or opposes any development proposal.

## Proof-directed status

The companion formal owner is:

`DASHI/Law/SensibLawWoogarooBartyOutreachExact.agda`

Current state:

- local nexus: PAID
- exact ecological / hydrological spatial relation: PAID at the catchment-system level
- development provenance: PAID for Peninsula and Scenic at the EPBC-project level
- factual outreach brief: PAID
- representative consent: OPEN
- attributable public position: OPEN

The first live residual is therefore `consentUnresolved` and the next producer is `directConsentProducer`.

## Source-paid facts

### 1. Barty community nexus

Queensland Government, 21 March 2025, states that the Ash Barty Playground was co-designed with Ash Barty and delivered through work involving the Queensland Government, Ipswich City Council, Springfield City Group and Ms Barty. The statement records Barty describing Springfield as her home/community and says she chose a playground for local children and families instead of a statue.

Carrier:

- Queensland Government Ministerial Media Statement, `Ash Barty playground a grand slam for the community`, 21 March 2025.

### 2. Opossum Creek Parklands

Ipswich City Council locates Opossum Creek Parklands at 58 Scoparia Drive, Brookwater and identifies it as a public park with playground and recreational facilities.

Carrier:

- Ipswich City Council, `Opossum Creek Parklands`.

### 3. Opossum / Woogaroo relationship

Ipswich City Council states that the Woogaroo Creek sub-catchment includes Mountain Creek and Opossum Creek. Council's Springfield planning material identifies significant natural vegetation and wildlife linkages particularly along Woogaroo Creek and Opossum Creek.

Council's Platypus Recovery Plan separately defines an Opossum Creek recovery area from the Opossum–Woogaroo confluence to Springfield Greenbank Arterial Road, records high habitat quality around Opossum Creek Parklands, and reports platypus evidence at the parklands.

This pays the bounded claim:

> Opossum Creek Parklands is part of an ecological and hydrological system connected through Opossum Creek to the Woogaroo Creek sub-catchment.

It does **not** by itself prove that every proposed development footprint is adjacent to the playground or that every affected species moves continuously between those exact footprints.

Carriers:

- Ipswich City Council, `Brisbane River Catchment — Woogaroo Creek (including Mountain and Opossum creeks)`.
- Ipswich Planning Scheme / Springfield Estate and Augustine Heights valuable-features statement.
- City of Ipswich, `Platypus Recovery Plan 2020`, recovery areas WG2/WG3/OP1.

### 4. Development provenance

The federal EPBC public record identifies:

- Peninsula Precinct, Springfield — EPBC 2020/8629 — under assessment.
- Scenic Precinct, Springfield — EPBC 2020/8651 — under assessment; preliminary documentation identifies Springfield City Group Pty Ltd as the proponent and threatened species / communities as controlling provisions.

The proposition that these projects form part of the campaign-defined `Woogaroo Forest` development threat is a Save Woogaroo Forest campaign classification and must remain distinguishable from the narrower federal project-status facts.

Carriers:

- National EPA / EPBC Act Public Portal, EPBC 2020/8629.
- National EPA / EPBC Act Public Portal, EPBC 2020/8651 and preliminary documentation.
- Save Woogaroo Forest development inventory for the campaign's Woogaroo classification.

## WrongType / SensibLaw firewalls

The following implications are prohibited:

```text
Barty associated with Springfield City Group
  != Barty endorses a development

Barty helped create a Springfield playground
  != Barty has a policy obligation

same catchment / ecological system
  != exact footprint adjacency

invitation sent
  != support

meeting accepted
  != support

site visit
  != opposition to development

consent to a visit
  != consent to quote or publish photographs

brand compatibility
  != consent
```

Only a direct, claim-scoped statement from Ash Barty or an authorised representative can pay a public-attribution residual.

## Recommended first ask

The lowest-conflict, highest-fit request is a **private site walk / factual briefing**.

Suggested framing:

> Ash chose a living community space for local children and families rather than a statue. Save Woogaroo Forest would value the opportunity to show Ash or a Foundation representative the Opossum Creek / Woogaroo landscape connected to that local community and explain, factually and without any expectation of endorsement, why residents are seeking to protect remaining habitat as Greater Springfield grows.

Operational conditions:

1. No media unless separately agreed.
2. No public announcement that an invitation has been sent unless there is a campaign reason independent of pressure on Barty.
3. No expectation of endorsement or public statement.
4. No claim that Barty supports or opposes Springfield City Group or any proposal.
5. Keep the first meeting small: campaign representative plus an appropriate ecology / local-knowledge representative where available.
6. Provide a one-page evidence pack and a simple map before or at the walk.
7. Ask separately for permission before quoting, photographing for publication, naming attendance, or using Foundation/Barty branding.

## Public contact route

The Ash Barty Foundation's official website provides an online `get in touch` contact form and states that the Foundation welcomes messages. This is the preferred initial route; do not seek private contact details.

## Initial contact copy

**Subject:** Invitation to learn about the Opossum Creek / Woogaroo landscape in Greater Springfield

Dear Ash and the Ash Barty Foundation team,

We are volunteers with Save Woogaroo Forest, a local community group concerned with the future of remaining native habitat in the Greater Springfield and Ipswich area.

We are reaching out because Ash has such a longstanding connection to Springfield and because the playground she helped create reflects a generous idea: a living place for local children and families rather than a statue.

We would be grateful for the opportunity to give Ash, or a Foundation representative, a short factual briefing about the Opossum Creek and Woogaroo landscape and, if of interest, arrange a quiet site walk with local residents and someone familiar with the area's ecology.

We recognise Ash has existing community and professional relationships in Greater Springfield. We are not asking her to criticise any organisation, and we do not presume what her view of any development proposal should be. There is no expectation of an endorsement, public statement or media involvement.

We would simply value the opportunity to share the evidence and local context and let Ash decide for herself whether there is any way she would feel comfortable helping.

Warm regards,

Save Woogaroo Forest

## Next admissible event

The proof state cannot advance beyond the current boundary through more inference.

The next admissible event is one of:

- an authorised response accepting or declining the briefing / walk;
- a request for more information;
- a separately authorised statement defining any public position.

Until then:

`InvitationPermitted = true`

`ConsentPaid = false`

`PublicAttributionPermitted = false`
