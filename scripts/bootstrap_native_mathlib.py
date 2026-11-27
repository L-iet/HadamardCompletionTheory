# SPDX-License-Identifier: Apache-2.0
"""Build licensed elaborator support. Mathematical proofs still use Lean-M1024.
All output is disposable .lake data. No theorem or axiom is supplied by this code.
"""
from pathlib import Path
import argparse,concurrent.futures,hashlib,json,os,queue,re,shutil,subprocess,sys,threading,time

def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def read(f):return json.loads(f.read_text(encoding='utf-8'))
def atomic(f,a):
 t=f.with_suffix(f.suffix+'.tmp')
 with t.open('w',encoding='utf-8',newline='\n') as w:w.write(json.dumps(a,indent=2)+'\n');w.flush();os.fsync(w.fileno())
 os.replace(t,f)
def run(cmd,r,log):
 with log.open('wb') as w:return subprocess.run(cmd,cwd=r,stdout=w,stderr=subprocess.STDOUT,creationflags=getattr(subprocess,'CREATE_NO_WINDOW',0)).returncode

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--project-root',type=Path,default=Path(__file__).resolve().parents[1]);ap.add_argument('--jobs',type=int,choices=[1,2],default=2);ap.add_argument('--seed-cache',type=Path);args=ap.parse_args()
 r=args.project_root.resolve();out=r/'.lake/cyclic-native';out.mkdir(parents=True,exist_ok=True)
 # This lock is local to the runtime target, not the outer verification/record lock.
 # It cannot deadlock a recorder which already holds the latter.
 lock=(out/'build.lock').open('a+b')
 if os.name=='nt':
  import msvcrt
  lock.seek(0);lock.write(b'0');lock.flush()
  while True:
   try:lock.seek(0);msvcrt.locking(lock.fileno(),msvcrt.LK_NBLCK,1);break
   except OSError:time.sleep(2)
 else:
  import fcntl
  fcntl.flock(lock,fcntl.LOCK_EX)
 try:build(r,out,args)
 finally:lock.close()

def build(r,out,args):
 win=os.name=='nt';assert win or sys.platform.startswith('linux'),'Native bootstrap supports Windows and Linux.'
 prefix=Path(subprocess.check_output(['lean','--print-prefix'],cwd=r,text=True).strip());cc=prefix/'bin'/('leanc.exe' if win else 'leanc');assert cc.is_file()
 rootsDir=r/'CompletionCyclicExistence';assert rootsDir.is_dir(),'Missing CompletionCyclicExistence sources'
 own={};todo=list(rootsDir.rglob('*.lean'));visited=set();roots={'Mathlib.NumberTheory.LSeries.PrimesInAP'}
 while todo:
  f=todo.pop().resolve()
  if f in visited:continue
  visited.add(f);own[f.relative_to(r).as_posix()]=sha(f)
  for name in re.findall(r'^(?:public )?(?:meta )?import\s+([A-Za-z0-9_.]+)',f.read_text(encoding='utf-8'),re.M):
   if name.startswith('Mathlib.'):roots.add(name)
   else:
    local=r/(name.replace('.','/')+'.lean')
    if local.is_file():todo.append(local)
 flags=['-c','-O0']+([] if win else ['-fPIC'])
 settings={'format':2,'compiler':str(cc),'compilerSHA256':sha(cc),'flags':flags,'platform':sys.platform,'leanToolchainSHA256':sha(r/'lean-toolchain'),'lakeManifestSHA256':sha(r/'lake-manifest.json'),'recipeSHA256':sha(Path(__file__)),'ownedSourceHashes':own}
 result=out/'result.json'
 if result.is_file():
  a=read(result)
  if a.get('status')=='native runtime built; no mathematical verification inferred' and a.get('proofLimit')=='-M1024' and a.get('settings')==settings and all(Path(x['file']).is_file() and sha(Path(x['file']))==x['sha256'] for x in a['libraries']) and Path(a['loader']['file']).is_file() and sha(Path(a['loader']['file']))==a['loader']['sha256'] and all(sha(Path(x['source']))==x['sha256'] for x in a['licenses'].values()):
   print('Validated cached licensed native runtime; proof limits unchanged.',flush=True);return
 index={}
 for pkg in (r/'.lake/packages').iterdir():
  ir=pkg/'.lake/build/ir'
  if ir.exists():
   for f in ir.rglob('*.c'):index['.'.join(f.relative_to(ir).with_suffix('').parts)]=(f.resolve(),pkg.resolve())
 ordered=[];seen=set();visiting=set();modules={};licenses={}
 def visit(n):
  if any(n==c or n.startswith(c+'.') for c in ['Init','Lean','Std','Lake']) or n in seen:return
  assert n not in visiting,('Dependency cycle',n)
  assert n in index,('Missing generated dependency C; run lake exe cache get first',n)
  visiting.add(n);f,pkg=index[n];s=f.read_text(encoding='utf-8');line=next((x for x in s.splitlines()[:5] if x.startswith('// Imports:')),'');deps=re.findall(r'\bimport\s+(?:all\s+)?([A-Za-z0-9_.]+)',line)
  for dep in deps:visit(dep)
  visiting.remove(n);seen.add(n);ordered.append(n)
  if pkg.name not in licenses:
   lf=next((x for x in pkg.iterdir() if x.is_file() and x.name.upper().startswith('LICENSE')),None);assert lf,('Missing license',pkg)
   text=lf.read_text(encoding='utf-8');assert ('Apache License' in text and 'Version 2.0' in text) or ('MIT License' in text and 'Permission is hereby granted' in text),('Unsupported license',lf)
   dst=out/'licenses'/pkg.name/lf.name;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(lf,dst);licenses[pkg.name]={'source':str(lf),'sha256':sha(lf),'copy':str(dst.relative_to(out))}
  modules[n]={'source':str(f),'sourceSHA256':sha(f),'package':pkg.name,'exportsUpperBound':s.count('LEAN_EXPORT'),'dependencies':deps}
 for n in sorted(roots):visit(n)
 key=hashlib.sha256(json.dumps(settings,sort_keys=True).encode()).hexdigest();chunks=[];part=[];size=0
 for n in ordered:
  count=modules[n]['exportsUpperBound'];assert count<60000,('Oversized native module',n)
  if part and size+count>24000:chunks.append(part);part=[];size=0
  part.append(n);size+=count
 if part:chunks.append(part)
 atomic(out/'plan.json',{'settings':settings,'key':key,'modules':modules,'topologicalOrder':ordered,'chunks':chunks,'licenses':licenses,'scope':'Native elaborator support only, no proof acceptance.'})
 objdir=out/'objects';objdir.mkdir(exist_ok=True);logs=out/'logs';logs.mkdir(exist_ok=True);work=queue.Queue();stop=threading.Event();guard=threading.Lock();done=[0];failed=[];start=time.time()
 seed=args.seed_cache.resolve() if args.seed_cache else None;seedSettings=None;seedData=None
 if seed and (seed/'result.json').is_file():
  seedData=read(seed/'result.json');seedSettings=seedData['settings']
  assert seedData['key']==hashlib.sha256(json.dumps(seedSettings,sort_keys=True).encode()).hexdigest()
  assert all(seedSettings[k]==settings[k] for k in ['compilerSHA256','flags','leanToolchainSHA256','lakeManifestSHA256']),'Seed compiler/config mismatch'
 for n in ordered:work.put(n)
 def worker():
  while not stop.is_set():
   try:n=work.get_nowait()
   except queue.Empty:return
   m=modules[n];tag=hashlib.sha256(n.encode()).hexdigest()[:24];obj=objdir/(tag+'.o');receipt=objdir/(tag+'.json');valid=False
   if obj.is_file() and receipt.is_file():
    a=read(receipt);valid=a.get('key')==key and a.get('sourceSHA256')==m['sourceSHA256'] and a.get('objectSHA256')==sha(obj)
   if not valid and seed:
    so=seed/'objects'/(tag+'.o');sr=seed/'objects'/(tag+'.json')
    if so.is_file() and sr.is_file():
     a=read(sr)
     if a.get('key')==seedData['key'] and n in seedData['modules'] and seedData['modules'][n]['sourceSHA256']==m['sourceSHA256'] and a['sourceSHA256']==m['sourceSHA256'] and seedData['modules'][n]['objectSHA256']==a['objectSHA256'] and a['objectSHA256']==sha(so):shutil.copy2(so,obj);valid=True
   if not valid:
    assert sha(Path(m['source']))==m['sourceSHA256'];temp=objdir/(tag+'.pending.o');code=run([str(cc),*flags,m['source'],'-o',str(temp)],r,logs/(tag+'.log'))
    if code:
     with guard:failed.append({'module':n,'actualExit':code});stop.set()
     return
    os.replace(temp,obj)
   atomic(receipt,{'module':n,'key':key,'sourceSHA256':m['sourceSHA256'],'objectSHA256':sha(obj),'actualExit':0});m['object']=str(obj);m['objectSHA256']=sha(obj)
   with guard:
    done[0]+=1
    if done[0]%100==0 or done[0]==len(ordered):atomic(out/'progress.json',{'completed':done[0],'total':len(ordered),'seconds':round(time.time()-start,1),'failures':failed});print('Native objects',done[0],'/',len(ordered),flush=True)
 with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
  tasks=[pool.submit(worker) for _ in range(args.jobs)]
  for task in tasks:task.result()
 if failed:atomic(out/'failures.json',failed);raise SystemExit(1)
 libraries=[]
 for i,part in enumerate(chunks):
  stem='CyclicNative'+str(i).zfill(2);lib=out/((stem+'.dll') if win else ('lib'+stem+'.so'));imp=out/('lib'+stem+'.dll.a') if win else lib;rsp=out/('link-'+str(i).zfill(2)+'.rsp')
  items=[modules[n]['object'] for n in part]+[x['linkFile'] for x in libraries]+['-L'+str(prefix/'lib/lean'),'-lLake_shared','-lStd']
  items+=['-Wl,--out-implib,'+str(imp)] if win else ['-Wl,-rpath,$ORIGIN']
  items+=['-o',str(lib)];rsp.write_text('\n'.join('"'+x.replace('\\','/')+'"' for x in items)+'\n',encoding='utf-8');code=run([str(cc),'-shared','@'+str(rsp)],r,logs/('link-'+str(i).zfill(2)+'.log'))
  print('Native chunk',i,'actual exit',code,flush=True)
  if code:raise SystemExit(code)
  libraries.append({'file':str(lib),'sha256':sha(lib),'linkFile':str(imp),'modules':part})
 # A single standard Lake plugin loads all bounded-export chunks in order.
 loaderSrc=out/'CyclicNativeLoader.lean';paths=[Path(x['file']).as_posix() for x in libraries]
 loaderSrc.write_text('/- Copyright (c) 2026 Joshua Mark. Apache-2.0. Runtime only. -/\nmodule\nimport Lean.LoadDynlib\ninitialize do\n  for path in #['+', '.join(json.dumps(x,ensure_ascii=False) for x in paths)+'] do\n    Lean.loadDynlib (System.FilePath.mk path)\n',encoding='utf-8',newline='\n')
 loaderLib=out/('CyclicNativeLoader.dll' if win else 'libCyclicNativeLoader.so');loaderC=out/'CyclicNativeLoader.c';loaderObj=out/'CyclicNativeLoader.o'
 commands=[['lean','-M1024','--root='+str(out),'-o',str(out/'CyclicNativeLoader.olean'),'-c',str(loaderC),str(loaderSrc)],[str(cc),*flags,str(loaderC),'-o',str(loaderObj)],[str(cc),'-shared',str(loaderObj),'-o',str(loaderLib)]]
 for i,cmd in enumerate(commands):
  code=run(cmd,r,logs/('loader-'+str(i)+'.log'));print('Native loader',i,'actual exit',code,flush=True)
  if code:raise SystemExit(code)
 assert 'initialize_CyclicNativeLoader' in loaderC.read_text(encoding='utf-8')
 for m in modules.values():assert sha(Path(m['source']))==m['sourceSHA256']
 assert settings['lakeManifestSHA256']==sha(r/'lake-manifest.json') and settings['leanToolchainSHA256']==sha(r/'lean-toolchain')
 atomic(result,{'status':'native runtime built; no mathematical verification inferred','settings':settings,'key':key,'libraries':libraries,'loader':{'name':'CyclicNativeLoader','file':str(loaderLib),'sha256':sha(loaderLib),'sourceSHA256':sha(loaderSrc),'cSHA256':sha(loaderC)},'licenses':licenses,'modules':modules,'proofLimit':'-M1024','requiresStandardAxiomAuditAndBothKernels':True})
 print('Licensed native runtime built. Mathematical builds/audits/comparisons remain separate.',flush=True)
if __name__=='__main__':main()
