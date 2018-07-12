/**
 * Created by maxhein on 18/03/2018.
 */

import java.io.IOException;
import java.util.regex.*;
import java.io.BufferedWriter;
import java.io.FileWriter;


// a case of catastrophic backtracking in Java
//
// javac Catastrophic.javac
// java Catastrophic
//
//
// The below link to test code using java 8/9
// java 9 runs (a*)*b more efficently
//
// https://www.jdoodle.com/online-java-compiler

public class Catastrophic {

    //calculates a time for how long the regular expression
    //(a?){n}a{n} takes to match a given number of a's
    public static void regexTesterSpecial(int numOfA){

        System.out.println("");
        System.out.println("Test: " + "(a?){n}a{n}");
        System.out.println("================");
        System.out.println("");

        for (int runs = 0; runs < 1; runs++) {
            for (int length = 1; length < numOfA; length += 100) {

                //String r1 = "(a){" + Integer.toString(length) + "}";
                //String r2 = "(a?){" + Integer.toString(length) + "}";

                String r1 = "";
                for(int i = 0; i < length; ++i) { r1 += "a"; }
                String r2 = "";
                for(int i = 0; i < length; ++i) { r2 += "a?"; }


                Pattern pattern = Pattern.compile(r1 + r2);

                // Build input of specified length
                String input = "";
                for (int i = 0; i < length; i++) { input += "a"; }

                long start = System.nanoTime();

                pattern.matcher(input).find();

                String time = ((System.nanoTime() - start) / 1.0e9) + ",";

                // Print out time
                System.out.println(length + " a's : "
                        + (time)
                        + "s");

            }
        }
    }

    //calculates a time for how long it takes for a given
    //reglar expression to match a given number of a's
    public static void regexTester(String regex, int numOfA){

        System.out.println("");
        System.out.println("Test: " + regex);
        System.out.println("================");
        System.out.println("");

        for (int runs = 0; runs < 1; runs++) {

            Pattern pattern = Pattern.compile(regex);

            for (int length = 1; length < numOfA; length += 1) {

                // Build input of specified length
                String input = "";
                for (int i = 0; i < length; i++) { input += "a"; }

                long start = System.nanoTime();
                pattern.matcher(input).find();

                String time = ((System.nanoTime() - start) / 1.0e9) + ",";

                // Print out time
                System.out.println(length + " a's : "
                        + time + "s");
            }
        }
    }

    public static void main(String[] args) {

        //there is a extended and basic regex implementation (times varie)
        regexTesterSpecial(100000);  //Test 0.1
        regexTester("(a*)*b",35);  //Test 0.2

        regexTester("(a*)*",4000);  // Test 1
        regexTester("(a+)+",4000);  // Test 2
        regexTester("(a|aa)+",100000);  // Test 3
        regexTester("(a|aa)(a|aa)*",100000);  // Test 3
        regexTester("(a|a?)+",2700);  // Test 4

    }
}
