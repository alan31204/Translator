# Translator
CSC 254 Assignment 3 README

  Translation

  Po-Chun Chiu(pchiu4) & Yujie Liu(yliu134)

Student ID: 29433254 & 29421244

Email: pchiu4@u.rochester.edu, yliu134@u.rochester.edu

  Yujie Liu is one of the Grace Hopper attendee, so we submit our project on Friday.

Assignment Directory: A3

  TAs should be able to find every files under the A3 directory include translator.ml, README.txt, a.txt, b.txt

  The code are all tested using the school cycle1 CSUG machine.

  The default shell of mine is cshell(csh).

  Use ocamlc or interpretor to test our code.

  It's either ->> ocamlc translator.ml 

              ->> ./a.out

       or     ->> ocaml

              ->> use "translator.ml";;

  We have tested our code by printing out an equivalent C program and test the C program using gcc.

Compile steps:

ocamlc translator.ml

Convert the parse tree to Abstract Syntax Tree:

1\. We used the parser given by professor Scott to generate the parse tree of given language.

2\. There are 2 type of languages given out in the sample code. One is the original calculator grammar, and the other one is the extended calculator grammar named ecg in the code.

3\. There are two sample program in the given code: the sum_ave_prog and the primes_prog.

4\. Now, we have to decorate the original parse tree by adding action routines to the abstract syntax tree.

5\. There are type ast_sl, ast_s, and ast_e.

6\. In ast_s, there are AST_error, AST_assign of (string and ast_e), AST_read of string, AST_write of (ast_e), AST_if of (ast_e and ast_sl), AST_do of ast_sl, and AST_check of ast_e.

7\. In ast_e, there are AST_binop of (string with two ast_e), AST_id of string, and AST_num of string.

8\. Define recursive function of ast_ize for P, SL, S, expr, reln_tail and expr_tail.

9\. In each of the function, we matched the symbols and expected PT_nt(non terminals from parse tree) and give actual meaning of each productions.

10\. In relation tail and expression tail. If the production went to epsilon, then we should return the original left hand side, otherwise our code will lose information in between.

11\. At first we return two strings for every translate function, however, we have to check whether variables have been declared but not used. 

12\. Thus, we declare memory type of storing strings as lists, and for every translate function, take in two memory type objects: db and used. We create a remainder function to check whether if everything in db is in used. If it is, then we will return a empty string(Everything used), otherwise, we will return specific ids that are in db but not in used. (Variables declared but not used)

13\. If any variable declard but unused, the program will print those out in standard output either in OCaml interpreter or by running the executable binary.

Translating to C

We initialized an 100 space array for int as numbers and 100 char* array to store strings.

1\. After we finished generating the correct AST from the parse tree with given proper action routines, we should now be able to do the translation into c.

2\. We create a helper, which is a string of proper C programming code including libraries, declarations, and our designed helper functions.

3\. There are some helper functions that we designed to implement in order to help us check dynamic errors.

4\. These helper functions include getint() for read, putint() for write, divide for checking if divion by zero error, setvar and getvar for assigning actual values to specific identifiers and get assigned values for specific identifiers.

5\. Also, in the getint function, we use scanf to check if there's unexpected end of input if scanf not returning 1.

6\. For every character in str, if it's greater than '9' or smaller than '0', then it's a non rumeric input.

7\. For all of the errors, we just print error messages and exit(1) to stop the code from running.

8\. We then define the recursive function for translate. In each of the function, we match the ast with different AST values.

9\. Each of the translate function should return 2 string, one is for error message, and the other is for correct string concatenation.

10\. Use ^ to concatenate strings together, and we also use tpl1, tpl2, tpl3 storing the contents for getting the strings.

11\. When we translate to C, we translate into the special predefined helper functions in C.s

12\. In translate_expr, we specifically put / condition in front of the other operator condition since we have to check division by 0 using our divide function in C.

13\. By using file, it's easier to check the nonnumeric input and unexpected end of input in C. There are two txt a.txt for nonnumeric input in our directory and b.txt for unexpected end of input.
