#CS3366 Programming Languages

R. Muller

## Problem Set 6: A Compiler for Mars/MiniC

Due: **Friday April 21**, 2017, 11:59PM

### 25 - 27 Points

---

This is a pair project: you are welcome to work with a partner on this problem set. 

The project involves writing the major components of a simple compiler for a clipped version of C, a language that we are calling miniC or Mars. The main advice on completing this project is that you should **start soon**. This is a 25 point problem. The components of the compiler are described in detail below. 

The point totals are as follows:

- **Name** : 5 points

- **Lift** : 5 points

- **CopyProp** (ast) : 1 point extra credit

- **Control** : 5 points

- **Codegen** : 10 points

- **CopyProp** (quads) : 1 point extra credit


You'll find information on the logistics of the project below. The first order of business is to review the existing code to ensure that you understand the overall structure of the compiler. The compiler builds as distributed. As you implement phases, you can try out your compiler on test files in the test/ folder. If you compile test/a.mc you can look in test/a.dbg to see a pretty-print of the compiler's main data structure.

**Required email**

One partner per team must send both Alden and RM an email identifying the team and the parts of the project you plan to work on. Something along the lines of "I will be working with Kevin Grant. We are planning to do the Name, Lift and Control phases." is sufficient.

**What to Submit** 

Each team should push one repository by the due date. The source files should contain comments with the surnames of the team members. 

---


### Name : 5 points: ###

The naming phase of the compiler, is implemented by the source-to-source transformation

  ```
  Name.translate : Ast.program -> Ast.program
  ```

which is found in the harness code file **name.ml**. This is the first transformation executed after the type checker. This translation walks the program tree, preserving all of the program phrases as found but making recursive transformations on **Ast.term**s. In particular, the results of all subterms should be assigned to newly created temporary variables (so-called "fresh" variables) by introducing let terms with fresh variables. For example, the naming transformation, should recursively translate the application term `+(12, a)` to:

```
let x1 = 12 in let x2 = a in let x3 = +(x1, x2) in x3
```

 where x1, x2 and x3 are fresh variables. 

The recursive translation here can give rise to lots of nested-lets. For example `+(+(2, 3), 4)` would translate to

```
let x1 = let x2 = 2 in
         let x3 = 3 in 
         let x4 = +(x2, x3) 
         in 
         x4 in 
let x5 = 4 in
let x6 = +(x1, x5) 
in
x6
```

**Notes**: 

1. After this translation, all of the operands of operators and function calls are simple variables.

2. You can create a fresh variable by calling the harness code function: 

   ```
   Symbol.fresh : unit -> Symbol.t
   ```

3. The harness code in **name.ml** also replaces **and** and **or** terms with lets and ifs; you can leave that code unchanged.

### Lift : 5 points:###

The lifting phase of the compiler, is implemented by the source-to-source translation

```
Lift.translate : Ast.program -> Ast.program 
```

which is found in the harness code file **lift.ml**. This is the second phase executed after the type checker. This translation walks the program tree, preserving all of the program phrases as found but making recursive transformations on **Ast.term**s that lift nested lets according to the following rule:

```
let x1 = let x2 = e2 in e3 in e4 =lift=> let x2 = e2 in let x1 = e3 in e4
```

The result of this transformation should have no terms of the form on the left of the =lift=> above.

### CopyProp (ast) : 1 point###

A let-expression in which the definition term is a variable, is needlessly copying the definition to the let-bound variable. The source-to-source transformation

```
Copyprop.translate : Ast.program -> Ast.program
```

 should remove useless copying from one variable to another:

```
let y = x in e =copyProp=> e[y:=x]
```

Your code should recursively walk the Ast.program tree looking for let-expression of the form shown on the left. Feel free to use the harness code function Copyprop.substitute to perform the substitution `e[y:=x]`.

### Control : 5 points###

The next transformation translates away from the language of Asts: 

```
Control.translate : Ast.program -> Quads.instructionstream 
```

This translation makes the control-flow that is implicit in Ast.statements explicit in the language of quadruples. The target language for this transformation is defined in the harness code file **quads.ml**. This transformation should recursively walk the Ast.program tree, translating each Ast.procedure to an equivalent Quads.procedure. The body of the former is an Ast.statement while the body of the latter is  a Quads.instruction list, i.e., it is a list of simpler, more machine-like instructions that may (or may not) include labels. These labels can be the targets of unconditional (Quads.Jmp) or conditional (Quads.JmpZero) branch instructions. 

- An **Ast.Assign** statement should translate to a **Quads.Get** instruction;

- An **Ast.While** statement of the form **While {expr; statement}**, if **[i1; ...; ik]** is the translation of **expr** and **[ik+2; ..., ik+m]** is the translation of **statement** then 

  ```
  [l1:i1; ...; ik; jzero x, l2; ik+2; ..., ik+m; jmp l1; l2:nop] 
  ```

  (where **x** holds the result of the test term) is the translation;

- An **Ast.IfS** statement of the form **Ast.IfS {expr; thn; els}**, if **[i1; ...; ik]** is the translation of **expr**, **[ik+2; ...; ik+m]** is the translation of **thn** and **[ik+m+2; ...; in]** is the translation of **els** then 

  ```
  [i1; ...; ik; jzero x, l1; ik+2; ..., ik+m; jmp l2; l1:ik+m+2; ..., ik+m; l2:nop]
  ```

   (where **x** holds the result of the test term) is the translation.

### CopyProp (quads) : 1 point###

This is another source-to-source transformation, but this time on the language of **quads**. It should remove any useless copying that might have been introduced by the `Control.translate` transformation. NB: there is no OCaml source code file in the harness code for this transformation and (therefore) this transformation is not used in the **compile.ml** top-level. If you write this transformation, you'll also need to modify the **compile.ml** file to call it.

### Codegen : 10 points###

The final translation is 

```
Codegen.translate : Quads.instructionstream -> Mips.Codestream.codestream
```

This translation deals with storage allocation for procedure and function variables as well as function call and return protocols. For the purposes of this gut-simple compiler, we will allocate storage for all variables (both programmer supplied and the temporaries generated by the compiler) in an activation record allocated on the call stack. The structure of an activation record is 

```
       +----------------------------+
A      |      Caller-Save Regs      |                 higher addresses
A      +----------------------------+
A      |       Value of Arg 1       |                 
A      +--           :            --+
A      |             :              |
A      +--                        --+
A      |       Value of Arg n       |
A      +----------------------------+
A      |       Return Address       |
       +----------------------------+
B      |   Caller's Frame Pointer   | <-- fp
B      +----------------------------+
B      |      Local Variable 1      |
B      +--            :           --+
B      |              :             |
B      +--                        --+
B      |      Local Variable k      |
B      +----------------------------+
B      |   Callee Save Registers    |                 lower addresses
       +----------------------------+
                                      <-- sp
```

where the parts labeled with A (above) are managed by the caller and the parts labeled with B are managed by the callee (i.e., the procedure being called). Since the miniC compiler has no register allocator, there is no need to save or restore the contents of (most) machine registers around procedure calls and returns.  Note that all procedure variables can be referenced indirectly using the frame pointer register fp. In particular, the storage cells allocated for a procedure's parameters are allocated at positive offsets from the fp and storage cells for local variables are allocated at negative offsets from the fp. Activation records are constructed by a combination of actions that are performed

1. around procedure calls, 

2. on procedure entry and 

3. before procedure return.


- **Procedure call**: code is required to push the arguments onto the call stack, to push the return address (ra) register and then transfer to the called procedure using a jump and link (jal) instruction. The code following the jal must restore the ra register and deallocate the storage for the actual arguments (thereby resetting the stack pointer (sp) register.

- **Procedure entry**: code is required to store the callers frame pointer and then allocate storage at the bottom of the activation record for all local variabls (including temporaries).

- **Procedure return**: if the procedure is a function then the value to be returned to the caller must be stored in the value register v0 register and all storage for local variables must be removed from the stack, leaving the sp register pointing at the caller's saved frame pointer on the stack. The return is completed with a jr instruction.


If you are working on the code generator and your partner doesn't have their pieces of the compiler working yet, you can cut-and-paste the following snippet into your compile.ml file for testing purposes.

``` 
module Q = Quads
let quadsPgm1 =
  let f = Label.fromString "f" in
  let n1 = Symbol.fromString "n1" in
  let n2 = Symbol.fromString "n2" in
  let plus = Symbol.fromString "+" in
  let x = Symbol.fresh() in
  let i1 = Q.Instruction(None,
                         Q.Gets(Q.Id x,
                         Q.BinPrimOp(plus, {Q.src1 = Q.Id n1;
                                            Q.src2 = Q.Id n2}))) in
  let i2 = Q.Instruction(None, Q.Ret(Q.Id x))
  in
  [Q.Procedure(f, [n1; n2], [i1; i2])]
```

**Logistics**

After cloning the repository, you'll find that the harness folder contains 20 .ml source files along with a number of other files.  The harness code is configured to be easy to work with in a Unix environment that includes an implementation of OCaml, the Unix make command and the atom editor. The development cycle would look as follows:

```
> atom .                  # or use a different text editor
> make                    # compile your compiler

> ./mc test/a.mc          # assuming that make produced no errors
                          # fix the errors otherwise
> atom test/a.dbg         # to see the debugging info

> make clean              # cleans up intermediate files
```
# MiniC_MARS_compiler
