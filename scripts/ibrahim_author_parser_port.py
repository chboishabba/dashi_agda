#!/usr/bin/env python3
"""Independent Python-3 behavioural port of an ORIGINAL Ibrahim FLN parser.

Original author/source: Mark Ibrahim et al., first-link study (2017),
DOI 10.1016/j.jocs.2016.12.001; marksibrahim/wikipedia_network
code/first_link_txt.py git blob a830c47905d4cde90876e1097f2620f4f19a63df.

This port intentionally preserves the original algorithm's *quirks*
instead of fixing them invisibly: substring blacklisting (even display
labels), no special italic rule, exact <ref>/<div> markers, parentheses
tracker, and nested brackets. It is a DASHI reconstruction. No claim
of original producer-revision identity or full corpus replay follows.
"""
from __future__ import annotations

SOURCE_BLOB = 'a830c47905d4cde90876e1097f2620f4f19a63df'
FALSE_LINKS = (
    'wikipedia:', 'w:', 'wikitionary:', 'wikt:', 'wikinews:', 'n:',
    'wikibooks:', 'b:', 'wikiquote:', 'q:', 'wikisource:', 's:',
    'wikispecies:', 'species:', 'wikiversity', 'v:', 'wikivoyage:',
    'voy:', 'wikimedia:', 'foundation:', 'wmf:', 'commonds:', 'c:',
    'chapter:', 'metawikipedia:', 'meta:', 'm:', 'incubator:',
    'outreach:', 'mw:', 'mediazilla:', 'bugzilla:', 'testwiki:',
    'wikitech:', 'wikidata:', 'd:', 'phabricator:', 'phab:',
    'talk:', 'user talk:', 'file:', 'user:', 'template:', 'category:',
    'file talk:', 'category talk:', 'image:', 'media:', 'special:',
    'help:', 'portal:', 'portal talk:', r'\#',
)


def spans_of_outer_links(body: str) -> list[tuple[int, int, str]]:
    """Preserve the 2016 parser's marker and evaluation ordering."""
    if not isinstance(body, str):
        raise TypeError('source wikitext must be a string')
    links: list[tuple[int, int, str]] = []
    link_char: list[int] = []
    wiki_template: list[int] = []
    parens: list[int] = []
    rtag: list[int] = []
    dtag: list[int] = []
    skip_char: set[int] = set()

    def inside_char(char: str, marker: tuple[str,str], tracker: list[int], i: int):
        if char == marker[0]:
            tracker.append(i)
        elif char == marker[1]:
            if tracker:
                tracker.pop()

    for i, c in enumerate(body):
        if i in skip_char:
            continue
        char=body[i:i+2]
        tag=body[i:i+4]
        inside_char(char, ('{{','}}'), wiki_template, i)
        if char in ('{{','}}'):
            skip_char.add(i+1)
        if wiki_template:
            continue
        inside_char(c, ('(',')'), parens, i)
        if parens:
            continue
        inside_char(tag, ('<ref','</re'), rtag, i)
        inside_char(tag, ('<div','</di'), dtag, i)
        if rtag or dtag:
            continue
        if char == '[[':
            link_char.append(i)
        elif char == ']]' and len(link_char) == 1:
            start = link_char.pop()
            links.append((start,i+2,body[start:i+2]))
        elif char == ']]' and len(link_char) > 1:
            link_char.pop()
    return links


def original_check_link(link: str) -> bool:
    if not isinstance(link,str):
        raise TypeError('link must be string')
    if not link:
        raise ValueError('empty link')
    return not (any(block in link.lower() for block in FALSE_LINKS)
                or link[0] == ':')


def original_clean_link(link: str) -> str:
    value=link.strip('[]')
    if '|' in value:
        value=value.split('|',1)[0]
    return value.strip()


def reference_first_qualifying_link(body: str) -> dict | None:
    for start,end,raw in spans_of_outer_links(body):
        if original_check_link(raw):
            return {'selected_span':[start,end],
                    'raw_link':raw,'selected_target':original_clean_link(raw),
                    'parser_source_blob':SOURCE_BLOB,
                    'parser_identity':'DASHI behavioural port; not author-executed'}
    return None
