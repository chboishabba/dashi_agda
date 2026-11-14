#!/usr/bin/env python3
"""Candidate-only multilingual first-link residual packet from pinned wikitext.

This is NOT a Wikipedia parser or editor. Link spans are supplied by an
independent selector, and their "first qualifying" status is not verified
here. QID agreement is merely a proposed same-entity coordinate; neither
translation equivalence nor repair authority follows.

Historical first-link method: Ibrahim, Danforth, Dodds, Journal of
Computational Science 19 (2017), DOI 10.1016/j.jocs.2016.12.001.
ITIR consumer-relative repair is existing DASHI core; this executable
source-envelope validator is new DASHI implementation.
"""
from __future__ import annotations
import hashlib
import json
import re
from pathlib import Path
from typing import Any

import ibrahim_author_parser_port as AuthorParser

AUTHOR_PORT_POLICY = "author-blob:" + AuthorParser.SOURCE_BLOB

SCHEMA='dashi.itir.wikipedia.first_link_candidate.v1'
SHA256=re.compile(r'^[0-9a-f]{64}$')
QID=re.compile(r'^Q[1-9][0-9]*$')
LANG=re.compile(r'^[a-z][a-z0-9-]{1,15}$')


def valid_surface(payload:dict[str,Any])->dict[str,Any]:
    required={'qid','language','title','page_id','revision_id','wikitext',
              'wikitext_sha256','selector_policy_ref','consumer_ref','observation',
              'selected_span','selected_target'}
    if not isinstance(payload,dict) or set(payload)!=required:
        raise ValueError('source surface must use complete explicit schema')
    if not isinstance(payload['qid'],str) or not QID.fullmatch(payload['qid']):
        raise ValueError('unverified QID syntax')
    if not isinstance(payload['language'],str) or not LANG.fullmatch(payload['language']):
        raise ValueError('invalid language edition')
    if not isinstance(payload['title'],str) or not payload['title']:
        raise ValueError('empty Wikipedia title')
    for n in ('page_id','revision_id'):
        if type(payload[n]) is not int or payload[n] <= 0:
            raise ValueError('page/revision ID must be positive integer')
    for n in ('selector_policy_ref','consumer_ref','observation','selected_target'):
        if not isinstance(payload[n],str) or not payload[n].strip():
            raise ValueError('missing consumer/selector/observation receipt')
    text=payload['wikitext']
    if not isinstance(text,str):
        raise ValueError('original wikitext must be present')
    digest=hashlib.sha256(text.encode('utf-8')).hexdigest()
    if not isinstance(payload['wikitext_sha256'],str) or not SHA256.fullmatch(payload['wikitext_sha256']) or digest != payload['wikitext_sha256']:
        raise ValueError('wikitext byte SHA-256 mismatch')
    span=payload['selected_span']
    if not isinstance(span,list) or len(span)!=2 or any(type(i) is not int for i in span):
        raise ValueError('selected span must be two integer codepoint offsets')
    a,b=span
    if not (0<=a<b<=len(text)):
        raise ValueError('invalid selected span')
    selected=text[a:b]
    # Verify only a literal local selected-link token. Complex MediaWiki
    # templates/links/exclusions are owned by the external selector policy.
    if (not selected.startswith('[[') or not selected.endswith(']]') or len(selected)<=4
            or '[[' in selected[2:-2] or ']]' in selected[2:-2]):
        raise ValueError('span is not a simple wiki-link token')
    name=selected[2:-2].split('|',1)[0].split('#',1)[0].strip()
    if name!=payload['selected_target']:
        raise ValueError('selected target does not match pinned source span')
    port_matches = False
    if payload['selector_policy_ref'] == AUTHOR_PORT_POLICY:
        proposed = AuthorParser.reference_first_qualifying_link(text)
        if proposed is None or proposed['selected_span'] != span or proposed['selected_target'] != name:
            raise ValueError('selected link differs from the author-parser behavioural port')
        port_matches = True
    # ITIR canonical text/span coordinates are deterministic from this exact
    # revision's bytes and offsets, not from a rendered title or QID.
    span_ref=hashlib.sha256(f'{digest}:{a}:{b}'.encode('ascii')).hexdigest()
    source_ref=f"{payload['language']}wiki:{payload['page_id']}@{payload['revision_id']}:{digest}"
    return {'qid':payload['qid'],'language':payload['language'],
            'source_ref':source_ref,'text_revision_id':digest,'span_ref':span_ref,
            'page_id':payload['page_id'],'revision_id':payload['revision_id'],
            'title':payload['title'],'source_sha256':digest,'selector_policy_ref':payload['selector_policy_ref'],
            'consumer_ref':payload['consumer_ref'],'observed_value':payload['observation'],
            'selected_target':name,'selected_span':span,
            'source_url':f"https://{payload['language']}.wikipedia.org/w/index.php?oldid={payload['revision_id']}",
            'reference_port_selection_matches':port_matches,
            'first_qualifying_link_soundness_paid':False,
            'source_fetched_independently_by_this_tool':False}


def compare_candidate(left:dict[str,Any],right:dict[str,Any])->dict[str,Any]:
    a,b=valid_surface(left),valid_surface(right)
    if a['language']==b['language'] or a['qid']!=b['qid']:
        raise ValueError('requires two editions and matching candidate entity QID')
    if a['consumer_ref']!=b['consumer_ref'] or a['selector_policy_ref']!=b['selector_policy_ref']:
        raise ValueError('different consumer or parser policy requires separate transport licence')
    differs=a['observed_value']!=b['observed_value']
    return {'schema':SCHEMA,'left':a,'right':b,
            'query':a['consumer_ref'],'candidate_entity_qid':a['qid'],
            'consumer_status':'collision_residual' if differs else 'value_agrees_unlicensed',
            'repair_candidate':({'coarse_coordinate':'qid','retain_coordinate':'observed_value',
                                 'reason':'candidate consumer non-descent / query collision'}
                                if differs else None),
            'translation_equivalence_paid':False,'semantic_authority_paid':False,
            'wiki_edit_authority_paid':False,'human_review_paid':False,
            'selected_consumer_licence_paid':False,
            'original_language_views_retained':True,
            'epistemic_unknown_not_mapped_to_signed_zero':True,
            'requires':'independent revision retrieval, first-link parser verification, source identity review and after-state consumer recheck'}


def main():
    import argparse
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--left',type=Path,required=True)
    p.add_argument('--right',type=Path,required=True)
    p.add_argument('--output',type=Path)
    args=p.parse_args()
    result=compare_candidate(json.loads(args.left.read_text(encoding='utf-8')),
                             json.loads(args.right.read_text(encoding='utf-8')))
    txt=json.dumps(result,sort_keys=True,ensure_ascii=False,indent=2)+'\n'
    if args.output: args.output.write_text(txt,encoding='utf-8')
    else: print(txt,end='')

if __name__=='__main__':main()
