import re,sys,os

filedir = sys.argv[1]
with open(filedir, "r") as f:
    fdata = f.read()

subst = [["minL_modelL", "minL"], ["GammaP_modelL", "GammaP"], ["andpL_modelL", "andpL"], ["orpL_modelL","orpL"], ["coq_prop_modelL", "coq_prop_L"], ["empL_modelL", "empL"], ["truepL_modelL", "truepL"], ["GammaD1_modelL", "GammaD1"], ["expL_modelL", "expL"], ["allpL_modelL", "allpL"]]
for substpair in subst:
    oldstr = substpair[0]
    newstr = substpair[1]
    fdata = re.sub(oldstr, newstr, fdata)

with open(filedir,"w") as f:
    f.write(fdata)
    sys.exit
