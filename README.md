miniC_MARS_compiler

This compiler compiles C-like language MARS down to MIPS binarycode that can be simulated using MARS simulator:

(See http://courses.missouristate.edu/KenVollmar/mars/)

This was originally the final project for the Programming Languages Course. 

The initial harness code was shared by Prof. Robert Muller of Boston College. It contains modules that were used except the following ones that were either debugged or coded later:

1. Name
2. Lift
3. CopyProp
4. Control
5. CodeGen

1. Compile
2. Bases
3. Mips
4. Parser
5. Static

I also added a test system and a few test programs to the compiler MakeFile to ensure that the compiler correctly compiles MARS language. 


