from sage.all import EllipticCurve, load, save

from testcong import make_hash, test_cong, test_irred, report
from XE7 import test_isom
import sys

try:
    hashtab7_50 = load('hashtab7_50')
except IOError:
    hashtab7_50 = make_hash(7,11,500000,50)
    hashtab7_50 = dict([(k,v) for k,v in hashtab7_50.items() if len(v)>1])
    save(hashtab7_50, 'hashtab7_50')
    len(hashtab7_50)

def find_bad_pairs(ht=hashtab7_50):
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

# bad_pairs = find_bad_pairs(hashtab7_50)
# previous cell takes ages; this is the output

bad_pairs = []
isom_sets = [s for s in hashtab7_50.values() if len(s)>1]
len(isom_sets)
isom_sets_red = []
isom_sets_irred = []
for s in isom_sets:
    isom_sets_irred.append(s) if test_irred(s) else isom_sets_red.append(s)
print("{} irreducible sets, {} reducible sets".format(len(isom_sets_irred),len(isom_sets_red)))

from collections import Counter
red_sizes = Counter()
irred_sizes = Counter()

for s in isom_sets_irred:
        irred_sizes[len(s)] += 1
print("irred sizes: {}".format(irred_sizes, max(s for s in irred_sizes)))

for s in isom_sets_red:
        red_sizes[len(s)] += 1
print("red sizes: {} (max = {})".format(red_sizes, max(s for s in red_sizes)))

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


assert irred_pairs_bad == []
assert irred_pairs_none == []
#assert len(irred_pairs_symp) ==  16822
#assert len(irred_pairs_anti) == 6939
print("{}      symplectic mod 7 irreducible pairs".format(len(irred_pairs_symp)))
print("{} anti-symplectic mod 7 irreducible pairs".format(len(irred_pairs_anti)))

# Count how many sets are all symplectic and how many include anti-symplectic congruences:

n_irred_sets_symp=0
n_irred_sets_anti=0
for s in isom_sets_irred:
    if any([lab1,lab2] in irred_pairs_anti for lab1 in s for lab2 in s):
        n_irred_sets_anti +=1
    else:
        n_irred_sets_symp +=1

print("Out of {} irreducible sets, {} consts of symplectic congruences only, while {} include at least one anti-symplectic congruence".format(len(isom_sets_irred),n_irred_sets_symp,n_irred_sets_anti))

# Output symp pairs for Magma

np = 0
fp = "mod7_symppairs.m"
out = open(fp, "w")
out.write('pairs := [\\\n')
for s in irred_pairs_symp[:-1]:
        #print(s[0],s[1])
        out.write('["{}", "{}"],\\\n'.format(s[0],s[1]))
        np += 1
s = irred_pairs_symp[-1]
out.write('["{}", "{}"]\\\n'.format(s[0],s[1]))
np += 1
out.write('];\n')
out.close()
print("Wrote {} pairs to {}".format(np, fp))

# Output anti pairs for Magma

np = 0
fp = "mod7_antipairs.m"
out = open(fp, "w")
out.write('pairs := [\\\n')
for s in irred_pairs_anti[:-1]:
        #print(s[0],s[1])
        out.write('["{}", "{}"],\\\n'.format(s[0],s[1]))
        np += 1
s = irred_pairs_anti[-1]
out.write('["{}", "{}"]\\\n'.format(s[0],s[1]))
np += 1
out.write('];\n')
out.close()
print("Wrote {} pairs to {}".format(np, fp))

def class_js(lab):
    E = EllipticCurve(lab)
    return Set([E1.j_invariant() for E1 in E.isogeny_class()])

def set_js(s):
    return sum([class_js(lab) for lab in s], Set())

irred_js = Set()
JS = irred_js_by_size = {2:Set(), 3:Set(), 4:Set(),5:Set()}
for s in isom_sets_irred:
    js = set_js(s)
    irred_js = irred_js + Set(js)
    irred_js_by_size[len(s)] += Set(js)

print("{} distinct j-invariants in irreducible isogeny classes".format(len(irred_js)))
# 11761
print("By size: {}".format([(n,len(irred_js_by_size[n])) for n in irred_js_by_size.keys()]))
# [(2, 11135), (3, 1455), (4, 340), (5, 36)]


