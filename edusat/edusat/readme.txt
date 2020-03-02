EduSAT - a SAT solver for educational purposes. (c) ofer strichman
==================================================================

Type edusat -h for options.


1. The folder ..\ includes a solution file for visual studio 2019.

2. ..\release\edusat.exe is a windows executable compiled from the current code. There is a copy of this executable ..\release\edusat_org.exe for reference, in case you change the code and recompile. 

3. test\ includes easy examples in the sat\ and unsat\ folders, and harder examples in the comp17 folder.  It also includes edusat.xlsx with statistics of runs with various configurations. 

4. 'run.bat' runs ..\release\edusat.exe on the sat/unsat examples in the test/ directory. 



Clarifications about the code: 

1. literal indexing: 
Internally, literal i is represented with the integer 2i, and literal -i with the integer 2i-1.
e.g. the clause (3 -4) is represented by (6 7)
See the functions v2l() and l2v() in edusat.h to understand the conversions. 

2. 'BCP_stack' contains the negation of the asserted literals that were not yet processed in BCP. 
watches[lit] contain a list of clauses that contain 'lit'. So if, e.g., we assert literal '8', we insert to BCP_stack the literal '7' (== Neg(8)), and then in BCP we traverse the claues in watches[7]. 
