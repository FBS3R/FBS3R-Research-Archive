import sys, io, contextlib, pickle
from fractions import Fraction as F
src=open('/home/claude/repo/APEX/Certificates/aklt_cert.py').read().replace("sys.exit(1 if FAILS else 0)","")
g={'__name__':'cert'}
sys.argv=['x']
with contextlib.redirect_stdout(io.StringIO()):
    exec(compile(src,'cert','exec'),g)
out={k:g[k] for k in ['Ms','sing','B0','Gs','Pc','Qc','Cc','PAIRS','alg','code']}
pickle.dump(out,open('cert.pkl','wb'))
print(g['Cc'])
print(g['Pc'])
