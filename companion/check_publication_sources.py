#!/usr/bin/env python3
"""Offline integrity and proof-escape scan; this is not a Lean proof check."""
import argparse,datetime,hashlib,json,pathlib,re,sys
from verify_publication_main import strip_comments

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=pathlib.Path,required=True);ap.add_argument('--manifest',type=pathlib.Path,required=True);ap.add_argument('--output',type=pathlib.Path);a=ap.parse_args()
 m=json.loads(a.manifest.read_text());problems=[];flags=[];graph={};mods=set(m['modules'])
 if len(mods)!=len(m['modules']):problems.append('Duplicate module name')
 files=dict(m['files'])
 for p,h in m.get('original_audit_manifests',{}).items():
  if p in files and files[p]!=h:problems.append('Conflicting manifest source: '+p)
  files[p]=h
 for p,h in files.items():
  f=a.root/p
  if not f.is_file():problems.append('Missing file: '+p);continue
  if sha(f)!=h:problems.append('Changed file: '+p)
  if p.startswith('SparseComponent/') and p.endswith('.lean'):
   s=strip_comments(f.read_text());words=re.findall(r'\b(sorry|sorryAx|admit|native_decide|axiom|unsafe|implemented_by|extern)\b',s)
   if words:flags.append({'path':p,'tokens':words})
   module=p[:-5].replace('/','.')
   graph[module]=[w for ln in s.splitlines() if re.match(r'^(?:public |private |meta )*import ',ln) for w in re.sub(r'^(?:public |private |meta )*import ','',ln).split() if w.startswith('SparseComponent')]
 for n in mods:
  if n not in graph:problems.append('Missing module source: '+n)
  for dep in graph.get(n,[]):
   if dep not in mods:problems.append('Project dependency outside manifest: '+n+' -> '+dep)
 positions={n:i for i,n in enumerate(m['modules'])}
 for n in mods:
  for dep in graph.get(n,[]):
   if dep in positions and positions[dep]>=positions[n]:problems.append('Invalid topological order: '+n+' -> '+dep)
 if flags:problems.append('Forbidden proof-escape token present')
 result={'status':'FAIL' if problems else 'PASS_SOURCE_INTEGRITY_ONLY','timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_commit':m['source_commit'],'project_modules':len(mods),'checked_files':len(files),'manifest_sha256':sha(a.manifest),'driver_sha256':sha(pathlib.Path(__file__)),'proof_escape_flags':flags,'errors':problems,'fresh_lean_compilation':False}
 if a.output:a.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2));return bool(problems)
if __name__=='__main__':sys.exit(main())
