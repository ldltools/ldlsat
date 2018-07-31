#/usr/bin/env python3

import subprocess
import os
import re
import sys
#ansdir = "/Users/amano/Documents/smartcont.bkup/jan182/ldl/out"
#testdir =  "/Users/amano/go/src/github.com/dsl4sc/tests/ldl/out"

currentdir = os.getcwd()
ansdir = "ans"
testdir = "out"
truedir = "valid"
falsedir = "unsat"

def checkequiv(fname,ansfname):
    res = subprocess.Popen(["diff",currentdir+"/"+testdir+"/"+fname,currentdir+"/"+ansdir+"/"+ansfname],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    out, err = res.communicate()

    testname = fname.rstrip("mso.dot")
    output = out.decode('utf-8').strip()
    output = re.sub(r'^(<|>) *?label.*','',output,flags=(re.MULTILINE))
    output = re.sub(r'^---$','',output,flags=(re.MULTILINE))
    output = re.sub(r'^\d*.\d*$','',output,flags=(re.MULTILINE))
    output = output.strip()
    if output == "":
        print ("{} OK".format(testname))
        return 0
    else:
        print("{} Failed".format(testname))        
        print (output)
        return 1

if __name__ == "__main__":
    res = subprocess.Popen(["ls",testdir], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = res.communicate() 

    outlist = out.decode('utf-8').split("\n")
    dotfiles = list(filter(lambda s:s.endswith("dot"), outlist))
    #print(dotfiles)
    failcount = 0
    print("======== NORMAL TEST =========")
    for f in dotfiles:
       failcount += checkequiv(f,f)
    #    num = f.strip("test").rstrip(".dfa.dot")    
    #    if int(num) <= 45:
    #        failcount += checkequiv(f,f)
       # elif int(num) < 70:
       #     failcount += checkequiv(f,"true.dot")
       # else:
       #     failcount += checkequiv(f,"false.dot")
    print("Failed {} / {}".format(failcount,len(dotfiles)))
    print("")

    print("======== VALIDITY TEST ========")
    failcountv = 0
    res = subprocess.Popen(["ls",testdir+'/'+truedir], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = res.communicate() 
    outlistv = out.decode('utf-8').split("\n")
    dotfilesv = list(filter(lambda s:s.endswith("dot"), outlistv))
    for f in dotfilesv:
        failcountv += checkequiv(f,"true.dot")

    print("Failed {} / {}".format(failcountv,len(dotfilesv))) 
    print("")

    print("======= INVALIDITY TEST =======")
    failcountf = 0
    res = subprocess.Popen(["ls",testdir+'/'+falsedir], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = res.communicate() 
    outlistf = out.decode('utf-8').split("\n")
    dotfilesf = list(filter(lambda s:s.endswith("dot"), outlistf))
    for f in dotfilesf:
        failcountf += checkequiv(f,"false.dot")

    print("Failed {} / {}".format(failcountf,len(dotfilesf)))

    if failcount + failcountf + failcountv > 0:
        sys.exit(1)
    else:
        sys.exit(0)

#print(out)
#print(dotfiles)