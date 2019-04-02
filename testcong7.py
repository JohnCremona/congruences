from sage.all import EllipticCurve, load, save

from testcong import make_hash, test_cong, test_irred, report
from XE7 import test_isom
import sys

try:
    hashtab7_30 = load('hashtab7_30')
except IOError:
    hashtab7_30 = make_hash(7,11,400000,30)
    hashtab7_30 = dict([(k,v) for k,v in hashtab7_30.items() if len(v)>1])
    save(hashtab7_30, 'hashtab7_30')
    len(hashtab7_30)

def find_bad_pairs(ht=hashtab7_30):
    bad_pairs = []
    for s in ht.values():
        if len(s)>1:
            E1 = EllipticCurve(s[0])
            for r in s[1:]:
                E2 = EllipticCurve(r)
                res, info = test_cong(7,E1,E2, mumax=10^7)
                if not res:
                    report(res,info,7,s[0],r)
                    bad_pairs.append([s[0],r])
    return bad_pairs

# bad_pairs = find_bad_pairs(hashtab7_30)
# previous cell takes ages; this is the output

bad_pairs = [['25921a1', '78400gw1']]
isom_sets = [s for s in hashtab7_30.values() if len(s)>1]
len(isom_sets)
isom_sets_red = []
isom_sets_irred = []
for s in isom_sets:
    isom_sets_irred.append(s) if test_irred(s) else isom_sets_red.append(s)
print("{} irreducible sets, {} reducible sets".format(len(isom_sets_irred),len(isom_sets_red)))
bad_s = [s for s in isom_sets_red if '25921a1' in s][0]
bad_s
bad_s_ok = [bad_s[i] for i in 0,2,3]
bad_s_ok
ind = isom_sets_red.index(bad_s)
#ind = 165
isom_sets_red[ind] == bad_s
isom_sets_red[ind]=bad_s_ok
assert not  [s for s in isom_sets_red if '78400gw1' in s]

from collections import Counter
red_sizes = Counter()
irred_sizes = Counter()

for s in isom_sets_irred:
        irred_sizes[len(s)] += 1
print("irred sizes: {}".format(irred_sizes))

for s in isom_sets_red:
        red_sizes[len(s)] += 1
print("red sizes: {}".format(red_sizes))

def test7(lab1, lab2):
    E1 = EllipticCurve(lab1)
    E2 = EllipticCurve(lab2)
    res1 = test_isom(E1,E2,True)
    res2 = test_isom(E1,E2,False)
    if res1 and res2:
        print("Problem: curves {} and {} are both symplectically and anti-sympectically isomorphic!".format(lab1,lab2))
        return 0
    elif not (res1 or res2):
        print("Problem: curves {} and {} are neither symplectically nor anti-sympectically isomorphic!".format(lab1,lab2))
        return 0
    else:
        return +1 if res1 else -1

nsets = len(isom_sets_irred)
irred_pairs_symp = []
irred_pairs_anti = []
irred_pairs_none = []
irred_pairs_bad = []
for i,s in enumerate(isom_sets_irred):
    print("Set #{}/{} with {} classes ({:.3f}%)".format(i+1,nsets,len(s),float(100.0*(i+1)/nsets)))
    #sys.stdout.write('\r')
    sys.stdout.flush()
    for i1,lab1 in enumerate(s):
        for i2, lab2 in enumerate(s):
            if i1<i2:
                try:
                    res = test7(lab1,lab2)
                    if res==+1:
                        sres = "symplectic"
                        irred_pairs_symp.append([lab1,lab2])
                    elif res==-1:
                        sres = "anti-symplectic"
                        irred_pairs_anti.append([lab1,lab2])
                    elif res==0:
                        sres = "neither"
                        irred_pairs_none.append([lab1,lab2])
                    else:
                        sres = "**********?????????*************"
                        irred_pairs_bad.append([lab1,lab2])
                    print("{} and {}: {}".format(lab1,lab2,sres))
                except:
                    print("error processing set number {}: {} and {}".format(i,lab1,lab2))
