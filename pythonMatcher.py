import re
import sys
import time


# Tests to compare
# To run use the following comand
#
#   >  python catastrophic.py

#calculates a matching time for the regular expresion a?{n}(a){n}
def regexTesterSpecial(numOfA):

    print("")
    print("a?{n}(a){n}")
    print("")

    the_file = open('GraphData.txt', 'a')

    for x in range (1,numOfA,1):
        r1 = '((a?){%s})' % x
        r2 = 'a{%s}' % x

        #r1 = ""
        #for i in range(0,x):
        #    r1 += "a?"
        #r2 = ""
        #for i in range(0,x):
        #    r2 += "a"

        r3 = r1 + r2
        strTest = "a" * x
        t0 = time.time()
        m = re.match(r3 , strTest)
        t1 = time.time()

        tim = str((t1-t0))
        the_file.write(tim + ',')

        print (str(x) + ": " + tim)


#calculates a matching time for a given regular expression
def regexTester(regex, numOfA):

    print("")
    print(regex)
    print("")

    the_file = open('GraphData.txt', 'a')

    for x in range (1,numOfA,1):
        strTest = "a" * x
        t0 = time.time()
        m = re.match(regex , strTest)
        t1 = time.time()

        tim = str((t1-t0))
        the_file.write(tim + ',')

        print (str(x) + ": " + tim)


#there is a extended and basic regex implementation (times varie)
regexTesterSpecial(7000)  #Test 0.1
#regexTester('(a*)*b',35)  #Test 0.2

#regexTester('((a*)*)',30) # Test 1
#regexTester('(a+)+',4000) # Test 2
#regexTester('(a|aa)+',100000)  # Test 3
#regexTester('(a|aa)(a|aa)*',100000)  # Test 3
#regexTester('(a|a?)+',4000)  # Test 4
