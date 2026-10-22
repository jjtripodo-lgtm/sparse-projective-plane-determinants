#!/usr/bin/env python3
"""Clean project replay of the exact 3–14 family + real + order source union.
No project proof objects are reused. Pinned external library objects are reused.
Never changes, updates, downloads, deletes or uploads repository data.
"""
from __future__ import annotations
import argparse,datetime,hashlib,json,os,pathlib,re,subprocess,time,sys

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def require(b,msg):
 if not b:raise RuntimeError(msg)
def strip_comments(s):
 out=[];i=0;depth=0;string=False
 while i<len(s):
  c=s[i:i+2]
  if depth:
   if c=='/-':depth+=1;i+=2
   elif c=='-/':depth-=1;i+=2
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif not string and c=='/-':depth=1;i+=2
  elif not string and c=='--':
   j=s.find('\n',i);i=len(s) if j<0 else j
  else:
   if s[i]=='"' and (i==0 or s[i-1]!='\\'):string=not string
   out.append(s[i]);i+=1
 require(depth==0,'Unclosed block comment')
 return ''.join(out)
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--root',type=pathlib.Path,required=True,help='sparse-component-lean directory')
 ap.add_argument('--manifest',type=pathlib.Path,required=True)
 ap.add_argument('--lean',type=pathlib.Path,required=True)
 ap.add_argument('--mathlib',type=pathlib.Path,required=True)
 ap.add_argument('--build',type=pathlib.Path,required=True,help='must not already exist')
 ap.add_argument('--output',type=pathlib.Path,required=True,help='must not already exist')
 ap.add_argument('--memory',type=int,default=4096)
 ap.add_argument('--proofwidgets-materialization',type=pathlib.Path)
 a=ap.parse_args();a.root=a.root.resolve();a.mathlib=a.mathlib.resolve();a.lean=a.lean.resolve();a.build=a.build.resolve();a.output=a.output.resolve()
 require(not a.build.exists(),'Build directory already exists: refusing project-cache reuse')
 require(not a.output.exists(),'Output directory already exists: refusing receipt overwrite')
 manifest=json.loads(a.manifest.read_text());a.output.mkdir(parents=True)
 require(subprocess.check_output([str(a.lean),'--githash'],text=True).strip()==manifest['compiler'],'Wrong compiler')
 require(subprocess.check_output(['git','-C',str(a.mathlib),'rev-parse','HEAD'],text=True).strip()==manifest['mathlib'],'Wrong mathlib')
 require(not subprocess.check_output(['git','-C',str(a.mathlib),'diff','--name-only'],text=True).strip(),'Modified tracked mathlib sources')
 for p,h in {**manifest['files'],**manifest.get('original_audit_manifests',{})}.items():
  require(sha(a.root/p)==h,'Source hash mismatch: '+p)
  if p.startswith('SparseComponent/') and p.endswith('.lean'):
   require(not re.search(r'\b(sorry|sorryAx|admit|native_decide|axiom|unsafe|implemented_by|extern)\b',strip_comments((a.root/p).read_text())),'Source proof escape: '+p)
 package_pins=[]
 for p in json.loads((a.mathlib/'lake-manifest.json').read_text())['packages']:
  root=a.mathlib/'.lake/packages'/p['name']
  if p['name']=='proofwidgets' and a.proofwidgets_materialization:
   pm=json.loads(a.proofwidgets_materialization.read_text());require(pm['commit']==p['rev'],'ProofWidgets pin mismatch')
   for f in pm['files']:
    b=(root/f['path']).read_bytes();require(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==f['sha'],'ProofWidgets blob changed: '+f['path'])
   package_pins.append({'name':p['name'],'rev':p['rev'],'method':'official GitHub blob materialization','manifest_sha256':sha(a.proofwidgets_materialization)})
  else:
   head=subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD'],text=True).strip();require(head==p['rev'],'Dependency pin mismatch: '+p['name'])
   require(not subprocess.check_output(['git','-C',str(root),'diff','--name-only'],text=True).strip(),'Modified dependency: '+p['name'])
   package_pins.append({'name':p['name'],'rev':head,'method':'git checkout'})
 lib=a.build/'lib/lean';lib.mkdir(parents=True)
 deps=[*sorted((a.mathlib/'.lake/packages').glob('*/.lake/build/lib/lean')),a.mathlib/'.lake/build/lib/lean']
 external=[]
 for d in deps:
  require(not (d/'SparseComponent').exists(),'Unexpected project cache in external library path')
  for p in sorted(d.rglob('*.olean*')):
   if p.is_file():external.append({'path':str(p.relative_to(a.mathlib)),'sha256':sha(p),'bytes':p.stat().st_size})
 save(a.output/'EXTERNAL_OBJECTS_BEFORE.json',external)
 env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,[lib,*deps]));env['LEAN_NUM_THREADS']='1'
 runs=[];began=datetime.datetime.now(datetime.timezone.utc).isoformat()
 def run(label,p,out=None):
  cmd=[str(a.lean),'-j','1','-M',str(a.memory),'-t','0','-D','Elab.async=false']
  if out:out.parent.mkdir(parents=True,exist_ok=True);cmd+=['-o',str(out)]
  cmd+=[str(p)];log=a.output/(label+'.log');start=time.monotonic();save(a.output/'CURRENT_STAGE.json',{'label':label,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'command':cmd})
  with log.open('w') as f:
   q=subprocess.Popen(cmd,cwd=a.root,env=env,stdout=f,stderr=subprocess.STDOUT);_,st,u=os.wait4(q.pid,0);q.returncode=os.waitstatus_to_exitcode(st)
  row={'label':label,'returncode':q.returncode,'seconds':round(time.monotonic()-start,3),'max_rss_kib':u.ru_maxrss,'command':cmd,'source_sha256':sha(p),'log_sha256':sha(log),'object_sha256':sha(out) if out and out.exists() else None,'trust_level':0}
  runs.append(row);save(a.output/'RUNS.json',runs);print(json.dumps(row),flush=True)
  require(q.returncode==0,log.read_text())
 for m in manifest['modules']:
  p=pathlib.Path(m.replace('.','/')+'.lean');run(m.replace('.','_'),a.root/p,lib/p.with_suffix('.olean'))
 body={};audited_modules=set()
 for lane in ['total_family_full','real_entry_transfer','order_obstruction']:
  label='BodyAudit_'+lane;run(label,a.root/'audit'/lane/'BodyAudit.lean')
  lines=(a.output/(label+'.log')).read_text().splitlines();summaries=[json.loads(x[11:]) for x in lines if x.startswith('BODY_AUDIT ')]
  require(len(summaries)==1,'Missing/duplicate audit result: '+lane)
  s=summaries[0];expected_owned={'total_family_full':3433,'real_entry_transfer':12,'order_obstruction':5}[lane]
  require(s['owned_declarations']==expected_owned,'Owned declaration count differs from pinned receipt: '+lane)
  audited_modules.update(x[7:] for x in lines if x.startswith('MODULE '))
  ax=s.get('body_traced_axioms',s.get('axioms'))
  require(set(ax)=={'propext','Classical.choice','Quot.sound'},'Unapproved axiom: '+lane)
  decls=[json.loads(x[5:]) for x in lines if x.startswith('DECL ')];require(decls and len({x['name'] for x in decls})==len(decls),'Invalid owned enumeration: '+lane)
  require(len(decls)==s['owned_declarations'],'Enumeration length differs from audit summary: '+lane)
  save(a.output/('DECLARATIONS_'+lane+'.json'),decls);body[lane]=s
 require(audited_modules==set(manifest['modules']),'Owned module coverage differs from full release source manifest')
 for m in ['FullFamily','RealEntryTransfer','OrderObstruction']:
  run('Strict_'+m,a.root/'SparseComponent/TotalFamily'/(m+'.lean'))
 for p,h in manifest['files'].items():require(sha(a.root/p)==h,'Source changed during replay: '+p)
 for x in external:require(sha(a.mathlib/x['path'])==x['sha256'],'External proof object changed during replay: '+x['path'])
 receipt={'status':'PASS_FRESH_COMBINED_MAIN_GRAPH','started_utc':began,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_commit':manifest['source_commit'],'compiler':manifest['compiler'],'mathlib':manifest['mathlib'],'manifest_sha256':sha(a.manifest),'driver_sha256':sha(pathlib.Path(__file__)),'project_modules':len(manifest['modules']),'project_object_reuse':False,'external_object_reuse':True,'external_artifacts_rechecked':len(external),'external_object_manifest_sha256':sha(a.output/'EXTERNAL_OBJECTS_BEFORE.json'),'package_pins':package_pins,'body_audits':body,'runs':runs,'scope':manifest['scope'],'whole_repository_lake_build':'not_run','full_mathlib_source_rebuild':'not_run'}
 save(a.output/'VALIDATION.json',receipt);print(json.dumps({'status':receipt['status'],'modules':receipt['project_modules'],'body_audits':body}),flush=True)
if __name__=='__main__':
 try:main()
 except Exception as e:print('FAIL:',e,file=sys.stderr);sys.exit(1)
