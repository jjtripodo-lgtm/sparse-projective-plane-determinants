#!/usr/bin/env python3
"""Source-bound serialized replay of the full original-matrix total-ones proof graph."""
from __future__ import annotations
import argparse, datetime, hashlib, json, os, pathlib, re, shutil, subprocess, time
ROOT=pathlib.Path(__file__).resolve().parents[1]
PIN='0ed37c9258f123a2c76a2175596f75c2bd50f941'
COMPILER='fd009949156901e6cf15b6d9bf1122294b8e697a'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--mathlib',type=pathlib.Path,required=True);ap.add_argument('--lean',required=True);ap.add_argument('--memory',type=int,default=4096);ap.add_argument('--build',type=pathlib.Path,default=ROOT/'.build-total-ones-replay');ap.add_argument('--output',type=pathlib.Path,default=ROOT/'audit/total_ones_final/replay');a=ap.parse_args()
 a.mathlib=a.mathlib.resolve();a.output.mkdir(parents=True,exist_ok=True)
 version=subprocess.check_output([a.lean,'--version'],text=True).strip()
 if subprocess.check_output([a.lean,'--githash'],text=True).strip()!=COMPILER:raise RuntimeError('Wrong Lean compiler')
 if subprocess.check_output(['git','-C',str(a.mathlib),'rev-parse','HEAD'],text=True).strip()!=PIN:raise RuntimeError('Wrong mathlib checkout')
 if PIN not in (ROOT/'lake-manifest.json').read_text():raise RuntimeError('Wrong mathlib package pin')
 manifest=json.loads((ROOT/'audit/total_ones_final/SOURCE_MANIFEST.json').read_text())
 for path,expected in manifest['files'].items():
  p=ROOT/path
  if sha(p)!=expected['sha256']:raise RuntimeError('Source changed: '+path)
  blob=p.read_bytes()
  if hashlib.sha1(b'blob '+str(len(blob)).encode()+b'\0'+blob).hexdigest()!=expected['git_blob']:raise RuntimeError('Git blob changed: '+path)
  if path.startswith('SparseComponent/') and path.endswith('.lean'):
   s=re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S);s=re.sub(r'--[^\n]*','',s)
   if re.search(r'\b(sorry|admit|native_decide|axiom|unsafe|implemented_by|extern)\b',s):raise RuntimeError('Proof escape '+path)
 if a.build.exists():shutil.rmtree(a.build)
 lib=a.build/'lib/lean';lib.mkdir(parents=True)
 env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,[lib,*sorted((a.mathlib/'.lake/packages').glob('*/.lake/build/lib/lean')),a.mathlib/'.lake/build/lib/lean']))
 runs=[]
 def run(label,source,out=None,strict=False):
  cmd=[a.lean,'-M',str(a.memory),'-j','1','-D','Elab.async=false']
  if out is not None:out.parent.mkdir(parents=True,exist_ok=True);cmd+=['-o',str(out)]
  if strict:cmd+=['-t','0']
  cmd+=[str(source)];log=a.output/(label+'.log');start=time.monotonic()
  with log.open('w')as fh:
   p=subprocess.Popen(cmd,cwd=ROOT,env=env,stdout=fh,stderr=subprocess.STDOUT)
   stage={'label':label,'status':'running','pid':p.pid,'pid_namespace':os.readlink('/proc/self/ns/pid'),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'command':cmd}
   (a.output/'CURRENT_STAGE.json').write_text(json.dumps(stage,indent=2)+'\n')
   with (a.output/'PROGRESS.jsonl').open('a') as progress:progress.write(json.dumps(stage)+'\n')
   _,status,usage=os.wait4(p.pid,0);p.returncode=os.waitstatus_to_exitcode(status)
  row={'label':label,'returncode':p.returncode,'seconds':round(time.monotonic()-start,3),'max_rss_kib':usage.ru_maxrss,'command':cmd,'log_sha256':sha(log),'source_sha256':sha(source),'object_sha256':sha(out) if out is not None and out.exists() else None};runs.append(row);print(json.dumps(row),flush=True)
  (a.output/'CURRENT_STAGE.json').write_text(json.dumps(dict(row,status='finished'),indent=2)+'\n')
  with (a.output/'PROGRESS.jsonl').open('a') as progress:progress.write(json.dumps(dict(row,status='finished'))+'\n')
  if p.returncode:raise RuntimeError(log.read_text())
  if 'declaration uses' in log.read_text() and 'sorry' in log.read_text():raise RuntimeError('Sorry output')
 for m in manifest['modules']:
  p=pathlib.Path(m.replace('.','/')+'.lean');run(m.replace('.','_'),ROOT/p,lib/p.with_suffix('.olean'))
 for module in ['audit.fano_equality.Controls','audit.total_ones_scalar.Controls']:
  p=pathlib.Path(module.replace('.','/')+'.lean');run(module.split('.')[-2]+'Controls',ROOT/p,lib/p.with_suffix('.olean'))
 for name in ['ExternalInterface','Controls']:
  p=pathlib.Path('audit/total_ones_final')/(name+'.lean');run(name,ROOT/p,lib/p.with_suffix('.olean'))
 run('Environment',ROOT/'audit/total_ones_final/Environment.lean')
 run('StrictConsumer',ROOT/'audit/total_ones_final/ExternalInterface.lean',strict=True)
 decls=[json.loads(s[5:])for s in(a.output/'Environment.log').read_text().splitlines()if s.startswith('DECL ')]
 if not decls or len({x['name']for x in decls})!=len(decls):raise RuntimeError('Empty or duplicate declaration audit')
 (a.output/'ALL_DECLARATIONS.json').write_text(json.dumps(decls,indent=2)+'\n')
 record={'status':'passed','compiler':version,'compiler_commit':COMPILER,'mathlib_pin':PIN,'memory_mb':a.memory,'jobs':1,'project_artifact_reuse':False,'mathlib_artifact_reuse':True,'modules':manifest['modules'],'declaration_count':len(decls),'runs':runs,'sources':manifest['files'],'scope':'Full original-matrix all-edge-count exponential determinant bound, total-3n Fano bound and exact isolated-Fano equality classification. Empty and singular cases included. No original degree or spectral cap, supplied scalar gate, moment conclusion or minimum-degree theorem premise.'}
 (a.output/'VALIDATION.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({'status':'passed','declarations':len(decls),'max_rss_kib':max(r['max_rss_kib']for r in runs)}))
if __name__=='__main__':main()
