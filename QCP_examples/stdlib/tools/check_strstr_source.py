#!/usr/bin/env python3
"""Check executable correspondence after the documented glibc adapters."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[3]
import os
os.chdir(ROOT)
def clean(s):return re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S)
def body(s,name):
 s=clean(s)
 for m in re.finditer(r'\b'+name+r'\s*\(',s):
  i=m.end();d=1
  while d:
   d+=(s[i]=='(')-(s[i]==')');i+=1
  while s[i].isspace():i+=1
  if s[i]!='{':continue
  start=i;d=1;i+=1
  while d:
   d+=(s[i]=='{')-(s[i]=='}');i+=1
  return s[start:i]
 raise ValueError(name)
def tokens(s):return re.sub(r'\s+','',s)
up=Path('docs/stdlib/upstream/glibc/glibc-2.40/string/strstr.c').read_text()
new=Path('QCP_examples/stdlib/glibc/strstr_RL.c').read_text()
def undo_reads(s):
 s=tokens(s)
 for ptr in ['ne','hs']:
  for i in range(4):s=s.replace('gs_read('+ptr+('+'+str(i) if i else '')+')',ptr+'['+str(i)+']')
 return s
results={}
for k in [2,3]:
 original=tokens(body(up,'strstr'+str(k)))
 original=original.replace('for(intc=hs[0];h1!=h2&&c!=0;c=*++hs)', 'intc=hs[0];while(h1!=h2&&c!=0){')
 update='h2=(h2<<16)|c;' if k==2 else 'h2=(h2|c)<<8;'
 original=original.replace(update,update+'++hs;c=hs[0];}')
 original=original.replace('NULL','(char*)0')
 assert original==undo_reads(body(new,'strstr'+str(k))), 'short helper '+str(k)
 results['strstr'+str(k)]='identical after proved read helper and for-update spelling'
original=tokens(body(up,'STRSTR'))
original=original[:original.index('constunsignedchar*end=')]+ 'returnhorspool_memmem_refinement(hs,hs_len,ne,ne_len);}'
original=original.replace("ne[0]=='\\0'",'ne[0]==0').replace("ne[1]=='\\0'",'ne[1]==0').replace("ne[2]=='\\0'",'ne[2]==0').replace("ne[3]=='\\0'",'ne[3]==0')
original=original.replace('if(hs==NULL||ne[1]==0)return(char*)hs;','if(hs==0)return(char*)hs;if(ne[1]==0)return(char*)hs;')
original=original.replace('returnNULL;','return(char*)0;')
original=original.replace('__strnlen((constchar*)hs,','__strnlen(hs,')
original=original.replace('if(__glibc_unlikely(ne_len>256))','if(ne_len>256)')
original=original.replace('two_way_long_needle(hs,hs_len,ne,ne_len)','strstr_tw_bridge(hs,hs_len,ne,(int)ne_len)')
actual=undo_reads(body(new,'strstr'))
if original!=actual:
 import difflib
 print('\n'.join(difflib.ndiff([original],[actual])))
 raise AssertionError('entry tokens')
results['strstr']='identical after branch-hint removal, equivalent short-circuit split, and proved component calls'
assert tokens(body(new,'gs_read'))=='{returnp[0];}'
print(results)

# Compare each search-call annotation with the proved component's public spec.
# Labels only choose QCP's named refinement spec; Require/Ensure text is kept.
def contract(source, name):
    m = re.search(r'\b' + name + r'\s*\([^)]*\)\s*/\*@\s*(.*?)\*/', source, re.S)
    if not m:
        raise ValueError('missing contract: ' + name)
    return tokens(m.group(1)[m.group(1).index('With'):])
bridge = Path('QCP_examples/stdlib/glibc/strstr_tw_bridge.c').read_text()
hp = Path('QCP_examples/stdlib/glibc/horspool_dynamic_RL.c').read_text()
tw = Path('QCP_examples/stdlib/glibc/two-way_dynamic_RL.c').read_text()
assert contract(new, 'horspool_memmem_refinement') == contract(hp, 'horspool_memmem_refinement')
assert contract(new, 'strstr_tw_bridge') == contract(bridge, 'strstr_tw_bridge')
assert contract(bridge, 'two_way_long_needle') == contract(tw, 'two_way_long_needle')
print('All three search-call contracts equal their proved component contracts')
