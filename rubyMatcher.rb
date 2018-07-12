# Regular expression matching in ruby time triles

# Tests to compare
# To run use the following comand
#
#   >  ruby catastrophic.rb


#calculates a matching time for the regular expresion a?{n}(a){n}
def regexTesterSpecial(numOfA)
	numbers = (1..numOfA).step(1)

	#iterate through the numbers
	numbers.each do |i|

		string = "a" * i

		#create a new regular expression based on current value of i
		re_str = "(a?){#{i}}(a){#{i}}"
		#re_str = "a?" * i + "a" * i
		re = Regexp.new(re_str)

		t0 = Time.now
		re.match(string)
		t1 = Time.now

		puts "#{i} %.5f" % (t1 - t0)

	end
end

#calculates a matching time for a given regular expression
def regexTester(regex, numOfA)
	numbers = (1..numOfA)

	#iterate through the numbers
	numbers.each do |i|

		string = ("a" * i) + "b"

		re = Regexp.new(regex)

		t0 = Time.now
		re.match(string)
		t1 = Time.now

		puts "#{i} %.5f" % (t1 - t0)

	end
end


#there is a extended and basic regex implementation (times varie)
regexTesterSpecial(100000)   #Test 0.1
#regexTester("(a*)*b",100000)   #Test 0.2

#regexTester("((a*)*)",4000) # Test 1
#regexTester("(a+)+",4000) # Test 2
#regexTester("(a|aa)+",100000)  # Test 3
#regexTester("(a|aa)(a|aa)*",100000)
#regexTester("(a|a?)+",4000)  # Test 4
