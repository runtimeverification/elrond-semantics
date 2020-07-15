WebAssembly State and Semantics
===============================

```k
require "data.md"
require "numeric.md"

module WASM
    imports WASM-DATA
    imports WASM-NUMERIC
```

Configuration
-------------

```k
    configuration
      <wasm>
        <instrs> .K </instrs>
        <valstack> .ValStack </valstack>
        <curFrame>
          <locals>    .Map </locals>
          <curModIdx> .Int </curModIdx>
        </curFrame>
        <moduleRegistry> .Map </moduleRegistry>
        <moduleIds> .Map </moduleIds>
        <moduleInstances>
          <moduleInst multiplicity="*" type="Map">
            <modIdx>      0    </modIdx>
            <exports>     .Map </exports>
            <types>       .Map </types>
            <nextTypeIdx> 0    </nextTypeIdx>
            <funcAddrs>   .Map </funcAddrs>
            <nextFuncIdx> 0    </nextFuncIdx>
            <tabIds>      .Map </tabIds>
            <tabAddrs>    .Map </tabAddrs>
            <memIds>      .Map </memIds>
            <memAddrs>    .Map </memAddrs>
            <globIds>     .Map </globIds>
            <globalAddrs> .Map </globalAddrs>
            <nextGlobIdx> 0    </nextGlobIdx>
            <moduleMetadata>
              <moduleId>     </moduleId>
              <funcIds> .Map </funcIds>
              <typeIds> .Map </typeIds>
            </moduleMetadata>
          </moduleInst>
        </moduleInstances>
        <nextModuleIdx> 0 </nextModuleIdx>
        <mainStore>
          <funcs>
            <funcDef multiplicity="*" type="Map">
              <fAddr>    0              </fAddr>
              <fCode>    .Instrs:Instrs </fCode>
              <fType>    .Type          </fType>
              <fLocal>   .Type          </fLocal>
              <fModInst> 0              </fModInst>
              <funcMetadata>
                <funcId> </funcId>
                <localIds> .Map </localIds>
              </funcMetadata>
            </funcDef>
          </funcs>
          <nextFuncAddr> 0 </nextFuncAddr>
          <tabs>
            <tabInst multiplicity="*" type="Map">
              <tAddr> 0    </tAddr>
              <tmax>  .Int </tmax>
              <tsize> 0    </tsize>
              <tdata> .Map </tdata>
            </tabInst>
          </tabs>
          <nextTabAddr> 0 </nextTabAddr>
          <mems>
            <memInst multiplicity="*" type="Map">
              <mAddr> 0      </mAddr>
              <mmax>  .Int   </mmax>
              <msize> 0      </msize>
              <mdata> .Bytes </mdata>
            </memInst>
          </mems>
          <nextMemAddr> 0 </nextMemAddr>
          <globals>
            <globalInst multiplicity="*" type="Map">
              <gAddr>  0         </gAddr>
              <gValue> undefined </gValue>
              <gMut>   .Mut      </gMut>
            </globalInst>
          </globals>
          <nextGlobAddr> 0 </nextGlobAddr>
        </mainStore>
        <deterministicMemoryGrowth> true </deterministicMemoryGrowth>
      </wasm>
```

### Assumptions and invariants

Integers in K are unbounded.
As an invariant, however, for any integer `< iNN > I:Int` on the stack, `I` is between 0 and `#pow(NN) - 1`.
That way, unsigned instructions can make use of `I` directly, whereas signed instructions may need `#signed(iNN, I)`.

The highest address in a memory instance divided by the `#pageSize()` constant (defined below) may not exceed the value in the `<max>` cell, if present.

Since memory data is bytes, all integers in the `Map` in the `<mdata>` cell are bounded to be between 1 and 255, inclusive.
All places in the data with no entry are considered zero bytes.

### Translations to Abstract Syntax

Before execution, the program is translated from the text-format concrete syntax tree into an abstract syntax tree using the following function.
It's full definition is found in the `wasm-text.md` file.

```k
    syntax Stmts ::= text2abstract ( Stmts ) [function]
 // ---------------------------------------------------
```

Instructions
------------

### Text Format

WebAssmebly code consists of instruction sequences.
The basic abstract syntax contains only the `instr` syntax production.
The text format also specifies the `plaininstr`, which corresponds almost exactly to the the `instr` production.

Most instructions are plain instructions.

```k
    syntax Instr ::= PlainInstr
 // ---------------------------
```

### Sequencing

WebAssembly code consists of sequences of statements (`Stmts`).
In this file we define 3 types of statements:

-   Instruction (`Instr`): Administrative or computational instructions.
-   Definitions (`Defn`) : The declarations of `type`, `func`, `table`, `mem` etc.
-   The Declaration of a module.

The sorts `EmptyStmt` and `EmptyStmts` are administrative so that the empty list of `Stmt`, `Instr`, or `Defn` has a unique least sort.

```k
    syntax EmptyStmt
 // ----------------

    syntax Instr ::= EmptyStmt
    syntax Defn  ::= EmptyStmt
    syntax Stmt  ::= Instr | Defn
 // -----------------------------

    syntax EmptyStmts ::= List{EmptyStmt , ""} [klabel(listStmt)]
    syntax Instrs     ::= List{Instr     , ""} [klabel(listStmt)]
    syntax Defns      ::= List{Defn      , ""} [klabel(listStmt)]
    syntax Stmts      ::= List{Stmt      , ""} [klabel(listStmt)]
 // -------------------------------------------------------------

    syntax Instrs ::= EmptyStmts
    syntax Defns  ::= EmptyStmts
    syntax Stmts  ::= Instrs | Defns
 // --------------------------------

    syntax K ::= sequenceStmts  ( Stmts  ) [function]
               | sequenceDefns  ( Defns  ) [function]
               | sequenceInstrs ( Instrs ) [function]
 // -------------------------------------------------
    rule sequenceStmts(.Stmts) => .
    rule sequenceStmts(S SS  ) => S ~> sequenceStmts(SS)

    rule sequenceDefns(.Defns) => .
    rule sequenceDefns(D DS  ) => D ~> sequenceDefns(DS)

    rule sequenceInstrs(.Instrs) => .
    rule sequenceInstrs(I IS   ) => I ~> sequenceInstrs(IS)
```

### Traps

`trap` is the error mechanism of Wasm.
Traps cause all execution to halt, and can not be caught from within Wasm.
We emulate this by consuming everything in the `<instrs>` cell that is not a `Stmt`.
Statements are not part of Wasm semantics, but rather of the embedder, and is where traps can be caught.
Thus, a `trap` "bubbles up" (more correctly, to "consumes the continuation") until it reaches a statement which is not an `Instr` or `Def`.

```k
    syntax Instr ::= "trap"
 // -----------------------
    rule <instrs> trap ~> (_L:Label => .) ... </instrs>
    rule <instrs> trap ~> (_F:Frame => .) ... </instrs>
    rule <instrs> trap ~> (_I:Instr => .) ... </instrs>
    rule <instrs> trap ~> (_D:Defn  => .) ... </instrs>
```

When a single value ends up on the instruction stack (the `<instrs>` cell), it is moved over to the value stack (the `<valstack>` cell).
If the value is the special `undefined`, then `trap` is generated instead.

```k
    rule <instrs> undefined => trap ... </instrs>
    rule <instrs>   V:Val    => .        ... </instrs>
         <valstack> VALSTACK => V : VALSTACK </valstack>
      requires V =/=K undefined
```

Common Operator Machinery
-------------------------

Common machinery for operators is supplied here, based on their categorization.
This allows us to give purely functional semantics to many of the opcodes.

### Constants

Constants are moved directly to the value stack.
Function `#unsigned` is called on integers to allow programs to use negative numbers directly.
**TODO**: Implement `Float` in the format of `-nan`, `nan:0x n:hexnum` and `hexfloat`.

```k
    syntax PlainInstr ::= IValType "." "const" WasmInt
                        | FValType "." "const" Number
 // -------------------------------------------------
    rule <instrs> ITYPE:IValType . const VAL => #chop (< ITYPE > VAL) ... </instrs>
    rule <instrs> FTYPE:FValType . const VAL => #round(  FTYPE , VAL) ... </instrs>
```

### Unary Operations

When a unary operator is the next instruction, the single argument is loaded from the `<valstack>` automatically.
An `*UnOp` operator always produces a result of the same type as its operand.

```k
    syntax PlainInstr ::= IValType "." IUnOp
                        | FValType "." FUnOp
 // ----------------------------------------
    rule <instrs> ITYPE . UOP:IUnOp => ITYPE . UOP C1 ... </instrs>
         <valstack> < ITYPE > C1 : VALSTACK => VALSTACK </valstack>
    rule <instrs> FTYPE . UOP:FUnOp => FTYPE . UOP C1 ... </instrs>
         <valstack> < FTYPE > C1 : VALSTACK => VALSTACK </valstack>
```

### Binary Operations

When a binary operator is the next instruction, the two arguments are loaded from the `<valstack>` automatically.

```k
    syntax PlainInstr ::= IValType "." IBinOp
                        | FValType "." FBinOp
 // -----------------------------------------
    rule <instrs> ITYPE . BOP:IBinOp => ITYPE . BOP C1 C2 ... </instrs>
         <valstack> < ITYPE > C2 : < ITYPE > C1 : VALSTACK => VALSTACK </valstack>
    rule <instrs> FTYPE . BOP:FBinOp => FTYPE . BOP C1 C2 ... </instrs>
         <valstack> < FTYPE > C2 : < FTYPE > C1 : VALSTACK => VALSTACK </valstack>
```

### Test Operations

When a test operator is the next instruction, the single argument is loaded from the `<valstack>` automatically.

```k
    syntax PlainInstr ::= IValType "." TestOp
 // -----------------------------------------
    rule <instrs> TYPE . TOP:TestOp => TYPE . TOP C1 ... </instrs>
         <valstack> < TYPE > C1 : VALSTACK => VALSTACK </valstack>
```

### Relationship Operations

When a relationship operator is the next instruction, the two arguments are loaded from the `<valstack>` automatically.

```k
    syntax PlainInstr ::= IValType "." IRelOp
                        | FValType "." FRelOp
 // -----------------------------------------
    rule <instrs> ITYPE . ROP:IRelOp => ITYPE . ROP C1 C2 ... </instrs>
         <valstack> < ITYPE > C2 : < ITYPE > C1 : VALSTACK => VALSTACK </valstack>
    rule <instrs> FTYPE . ROP:FRelOp => FTYPE . ROP C1 C2 ... </instrs>
         <valstack> < FTYPE > C2 : < FTYPE > C1 : VALSTACK => VALSTACK </valstack>
```

### Conversion Operations

Conversion Operation convert constant elements at the top of the stack to another type.

```k
    syntax PlainInstr ::= ValType "." CvtOp
 // ----------------------------------------
    rule <instrs> TYPE:ValType . CVTOP:Cvti32Op => TYPE . CVTOP C1  ... </instrs>
         <valstack> < i32 > C1 : VALSTACK => VALSTACK </valstack>

    rule <instrs> TYPE:ValType . CVTOP:Cvti64Op => TYPE . CVTOP C1  ... </instrs>
         <valstack> < i64 > C1 : VALSTACK => VALSTACK </valstack>

    rule <instrs> TYPE:ValType . CVTOP:Cvtf32Op => TYPE . CVTOP C1  ... </instrs>
         <valstack> < f32 > C1 : VALSTACK => VALSTACK </valstack>

    rule <instrs> TYPE:ValType . CVTOP:Cvtf64Op => TYPE . CVTOP C1  ... </instrs>
         <valstack> < f64 > C1 : VALSTACK => VALSTACK </valstack>
```

ValStack Operations
-------------------

Operator `drop` removes a single item from the `<valstack>`.
The `select` operator picks one of the second or third stack values based on the first.

```k
    syntax PlainInstr ::= "drop"
 // ----------------------------
    rule <instrs> drop => . ... </instrs>
         <valstack> _ : VALSTACK => VALSTACK </valstack>

    syntax PlainInstr ::= "select"
 // ------------------------------
    rule <instrs> select => . ... </instrs>
         <valstack>
           < i32 > C : < TYPE > V2:Number : < TYPE > V1:Number : VALSTACK
      =>   < TYPE > #if C =/=Int 0 #then V1 #else V2 #fi       : VALSTACK
         </valstack>
```

Structured Control Flow
-----------------------

`nop` does nothing.

```k
    syntax PlainInstr ::= "nop"
 // ---------------------------
    rule <instrs> nop => . ... </instrs>
```

`unreachable` causes an immediate `trap`.

```k
    syntax PlainInstr ::= "unreachable"
 // -----------------------------------
    rule <instrs> unreachable => trap ... </instrs>
```

Labels are administrative instructions used to mark the targets of break instructions.
They contain the continuation to use following the label, as well as the original stack to restore.
The supplied type represents the values that should taken from the current stack.

A block is the simplest way to create targets for break instructions (ie. jump destinations).
It simply executes the block then records a label with an empty continuation.

```k
    syntax Label ::= "label" VecType "{" Instrs "}" ValStack
 // --------------------------------------------------------
    rule <instrs> label [ TYPES ] { _ } VALSTACK' => . ... </instrs>
         <valstack> VALSTACK => #take(lengthValTypes(TYPES), VALSTACK) ++ VALSTACK' </valstack>

    syntax Instr ::= "block" TypeDecls Instrs "end"
                   | "block" VecType   Instrs "end"
 // -----------------------------------------------
    rule <instrs> block TDECLS:TypeDecls IS end => block gatherTypes(result, TDECLS) IS end ... </instrs>
    rule <instrs> block VECTYP:VecType   IS end => sequenceInstrs(IS) ~> label VECTYP { .Instrs } VALSTACK ... </instrs>
         <valstack> VALSTACK => .ValStack </valstack>
```

The `br*` instructions search through the instruction stack (the `<instrs>` cell) for the correct label index.
Upon reaching it, the label itself is executed.

Note that, unlike in the WebAssembly specification document, we do not need the special "context" operator here because the value and instruction stacks are separate.

```k
    syntax PlainInstr ::= "br" Index
 // --------------------------------
    rule <instrs> br _IDX ~> (_S:Stmt => .) ... </instrs>
    rule <instrs> br 0   ~> label [ TYPES ] { IS } VALSTACK' => sequenceInstrs(IS) ... </instrs>
         <valstack> VALSTACK => #take(lengthValTypes(TYPES), VALSTACK) ++ VALSTACK' </valstack>
    rule <instrs> br N:Int ~> _L:Label => br N -Int 1 ... </instrs>
      requires N >Int 0

    syntax PlainInstr ::= "br_if" Index
 // -----------------------------------
    rule <instrs> br_if IDX => br IDX ... </instrs>
         <valstack> < _TYPE > VAL : VALSTACK => VALSTACK </valstack>
      requires VAL =/=Int 0
    rule <instrs> br_if _IDX => .    ... </instrs>
         <valstack> < _TYPE > VAL : VALSTACK => VALSTACK </valstack>
      requires VAL  ==Int 0

    syntax PlainInstr ::= "br_table" ElemSegment
 // --------------------------------------------
    rule <instrs> br_table ES:ElemSegment => br #getElemSegment(ES, minInt(VAL, #lenElemSegment(ES) -Int 1)) ... </instrs>
         <valstack> < _TYPE > VAL : VALSTACK => VALSTACK </valstack>
```

Finally, we have the conditional and loop instructions.

```k
    syntax Instr ::= "if" TypeDecls Instrs "else" Instrs "end"
 // ----------------------------------------------------------
    rule <instrs> if TDECLS:TypeDecls IS else _ end => sequenceInstrs(IS) ~> label gatherTypes(result, TDECLS) { .Instrs } VALSTACK ... </instrs>
         <valstack> < i32 > VAL : VALSTACK => VALSTACK </valstack>
      requires VAL =/=Int 0

    rule <instrs> if TDECLS:TypeDecls _ else IS end => sequenceInstrs(IS) ~> label gatherTypes(result, TDECLS) { .Instrs } VALSTACK ... </instrs>
         <valstack> < i32 > VAL : VALSTACK => VALSTACK </valstack>
      requires VAL ==Int 0

    syntax Instr ::= "loop" TypeDecls Instrs "end"
 // ----------------------------------------------
    rule <instrs> loop TDECLS:TypeDecls IS end => sequenceInstrs(IS) ~> label gatherTypes(result, TDECLS) { loop TDECLS IS end } VALSTACK ... </instrs>
         <valstack> VALSTACK => .ValStack </valstack>
```

Variable Operators
------------------

### Locals

The various `init_local` variants assist in setting up the `locals` cell.

```k
    syntax Instr ::=  "init_local"  Int Val
                   |  "init_locals"     ValStack
                   | "#init_locals" Int ValStack
 // --------------------------------------------
    rule <instrs> init_local INDEX VALUE => . ... </instrs>
         <locals> LOCALS => LOCALS [ INDEX <- VALUE ] </locals>

    rule <instrs> init_locals VALUES => #init_locals 0 VALUES ... </instrs>

    rule <instrs> #init_locals _ .ValStack => . ... </instrs>
    rule <instrs> #init_locals N (VALUE : VALSTACK)
               => init_local N VALUE
               ~> #init_locals (N +Int 1) VALSTACK
               ...
          </instrs>
```

The `*_local` instructions are defined here.

```k
    syntax PlainInstr ::= "local.get" Index
                        | "local.set" Index
                        | "local.tee" Index
 //----------------------------------------
    rule <instrs> local.get I:Int => . ... </instrs>
         <valstack> VALSTACK => VALUE : VALSTACK </valstack>
         <locals> ... I |-> VALUE ... </locals>

    rule <instrs> local.set I:Int => . ... </instrs>
         <valstack> VALUE : VALSTACK => VALSTACK </valstack>
         <locals> ... I |-> (_ => VALUE) ... </locals>

    rule <instrs> local.tee I:Int => . ... </instrs>
         <valstack> VALUE : _VALSTACK </valstack>
         <locals> ... I |-> (_ => VALUE) ... </locals>
```

### Globals

When globals are declared, they must also be given a constant initialization value.
The `GlobalSpec` production is used to define all ways that a global can specified.
Globals can either be specified by giving a type and an initializer expression; or by an import and it's expected type.
The specification can also include export directives.
The importing and exporting parts of specifications are dealt with in the respective sections for import and export.

```k
    syntax TextFormatGlobalType ::= ValType | "(" "mut" ValType ")"
 // ---------------------------------------------------------------

    syntax GlobalType ::= Mut ValType
                        | asGMut (TextFormatGlobalType) [function]
 // --------------------------------------------------------------
    rule asGMut ( (mut T:ValType ) ) => var   T
    rule asGMut (      T:ValType   ) => const T

    syntax Defn       ::= GlobalDefn
    syntax GlobalSpec ::= TextFormatGlobalType Instr
    syntax GlobalDefn ::= "(" "global" OptionalId  GlobalSpec ")"
    syntax Alloc      ::= allocglobal (OptionalId, GlobalType)
 // ----------------------------------------------------------
    rule <instrs> ( global OID:OptionalId TYP:TextFormatGlobalType IS:Instr ) => IS ~> allocglobal(OID, asGMut(TYP)) ... </instrs>

    rule <instrs> allocglobal(OID:OptionalId, MUT:Mut TYP:ValType) => . ... </instrs>
         <valstack> < TYP > VAL : STACK => STACK </valstack>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <globIds> IDS => #saveId(IDS, OID, NEXTIDX) </globIds>
           <nextGlobIdx> NEXTIDX => NEXTIDX +Int 1                </nextGlobIdx>
           <globalAddrs> GLOBS   => GLOBS [ NEXTIDX <- NEXTADDR ] </globalAddrs>
           ...
         </moduleInst>
         <nextGlobAddr> NEXTADDR => NEXTADDR +Int 1 </nextGlobAddr>
         <globals>
           ( .Bag
          => <globalInst>
               <gAddr>  NEXTADDR  </gAddr>
               <gValue> <TYP> VAL </gValue>
               <gMut>   MUT       </gMut>
             </globalInst>
           )
           ...
         </globals>
```

The `get` and `set` instructions read and write globals.

```k
    syntax PlainInstr ::= "global.get" Index
                        | "global.set" Index
 // ----------------------------------------
    rule <instrs> global.get TFIDX => . ... </instrs>
         <valstack> VALSTACK => VALUE : VALSTACK </valstack>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <globIds> IDS </globIds>
           <globalAddrs> ... #ContextLookup(IDS , TFIDX) |-> GADDR ... </globalAddrs>
           ...
         </moduleInst>
         <globalInst>
           <gAddr>  GADDR </gAddr>
           <gValue> VALUE </gValue>
           ...
         </globalInst>

    rule <instrs> global.set TFIDX => . ... </instrs>
         <valstack> VALUE : VALSTACK => VALSTACK </valstack>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <globIds> IDS </globIds>
           <globalAddrs> ... #ContextLookup(IDS , TFIDX) |-> GADDR ... </globalAddrs>
           ...
         </moduleInst>
         <globalInst>
           <gAddr>  GADDR      </gAddr>
           <gValue> _ => VALUE </gValue>
           ...
         </globalInst>
```

Types
-----

### Type Gathering

This defines helper functions that gathers function together.
The function `gatherTypes` keeps the `TypeDecl`s that have the same `TypeKeyWord` as we need and throws away the `TypeDecl` having different `TypeKeyWord`.

```k
    syntax TypeKeyWord ::= "param" | "result"
 // -----------------------------------------

    syntax TypeDecl  ::= "(" TypeDecl ")"     [bracket]
                       | TypeKeyWord ValTypes
                       | "param" Identifier ValType
    syntax TypeDecls ::= List{TypeDecl , ""} [klabel(listTypeDecl)]
 // ---------------------------------------------------------------

    syntax VecType ::=  gatherTypes ( TypeKeyWord , TypeDecls )            [function]
                     | #gatherTypes ( TypeKeyWord , TypeDecls , ValTypes ) [function]
 // ---------------------------------------------------------------------------------
    rule  gatherTypes(TKW , TDECLS:TypeDecls) => #gatherTypes(TKW, TDECLS, .ValTypes)

    rule #gatherTypes( _  ,                                   .TypeDecls , TYPES) => [ TYPES ]
    rule #gatherTypes(TKW , TKW':TypeKeyWord _:ValTypes TDECLS:TypeDecls , TYPES) => #gatherTypes(TKW, TDECLS, TYPES) requires TKW =/=K TKW'
    rule #gatherTypes(TKW , TKW         TYPES':ValTypes TDECLS:TypeDecls , TYPES)
      => #gatherTypes(TKW ,                             TDECLS:TypeDecls , TYPES + TYPES')
    rule #gatherTypes(result , param _ID:Identifier     _:ValType TDECLS:TypeDecls , TYPES) => #gatherTypes(result , TDECLS , TYPES)
    rule #gatherTypes(param  , param _ID:Identifier VTYPE:ValType TDECLS:TypeDecls , TYPES) => #gatherTypes(param  , TDECLS , TYPES + VTYPE .ValTypes)
```

### Type Use

A type use is a reference to a type definition.
It may optionally be augmented by explicit inlined parameter and result declarations.
A type use should start with `'(' 'type' x:typeidx ')'` followed by a group of inlined parameter or result declarations.

# TODO: Remove the middle case (single `(type X)` without declaration), and move to wasm-text.

```k
    syntax TypeUse ::= TypeDecls
                     | "(type" Index ")"           [prefer]
                     | "(type" Index ")" TypeDecls
 // ----------------------------------------------

    syntax FuncType ::= asFuncType ( TypeDecls )         [function, klabel(TypeDeclsAsFuncType)]
                      | asFuncType ( Map, Map, TypeUse ) [function, klabel(TypeUseAsFuncType)  ]
 // --------------------------------------------------------------------------------------------
    rule asFuncType(TDECLS:TypeDecls)                       => gatherTypes(param, TDECLS) -> gatherTypes(result, TDECLS)
    rule asFuncType(   _   ,   _  , TDECLS:TypeDecls)       => asFuncType(TDECLS)
    rule asFuncType(TYPEIDS, TYPES, (type TFIDX ))          => {TYPES[#ContextLookup(TYPEIDS ,TFIDX)]}:>FuncType
    rule asFuncType(TYPEIDS, TYPES, (type TFIDX ) TDECLS )  => asFuncType(TDECLS)
      requires TYPES[#ContextLookup(TYPEIDS, TFIDX)] ==K asFuncType(TDECLS)
```

### Type Declaration

Type could be declared explicitly and could optionally bind with an identifier.
`identifier` for `param` will be used only when the function type is declared when defining a function.
When defining `TypeDefn`, the `identifier` for `param` will be ignored and will not be saved into the module instance.

```k
    syntax Defn     ::= TypeDefn
    syntax TypeDefn ::= #type(type: FuncType, metadata: OptionalId)
    syntax Alloc    ::= alloctype (OptionalId, FuncType)
 // ----------------------------------------------------
    rule <instrs> #type(... type: TYPE, metadata: OID) => alloctype(OID, TYPE) ... </instrs>

    rule <instrs> alloctype(OID, TYPE) => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <typeIds> IDS => #saveId(IDS, OID, NEXTIDX) </typeIds>
           <nextTypeIdx> NEXTIDX => NEXTIDX +Int 1 </nextTypeIdx>
           <types> TYPES => TYPES [NEXTIDX <- TYPE] </types>
           ...
         </moduleInst>
```

Function Declaration and Invocation
-----------------------------------

### Function Local Declaration

```k
    syntax LocalDecl  ::= "(" LocalDecl ")"           [bracket]
                        | "local"            ValTypes
                        | "local" Identifier ValType
    syntax LocalDecls ::= List{LocalDecl , ""}        [klabel(listLocalDecl)]
 // -------------------------------------------------------------------------
```

### Function Declaration

Function declarations can look quite different depending on which fields are ommitted and what the context is.
Here, we allow for an "abstract" function declaration using syntax `func_::___`, and a more concrete one which allows arbitrary order of declaration of parameters, locals, and results.
The `FuncSpec` production is used to define all ways that a global can specified.
A function can either be specified by giving a type, what locals it allocates, and a function body; or by an import and it's expected type.
The specification can also include export directives.
The importing and exporting parts of specifications are dealt with in the respective sections for import and export.

```k
    syntax Defn     ::= FuncDefn
    syntax FuncDefn ::= #func(type: Int, locals: VecType, body: Instrs, metadata: FuncMetadata)
    syntax Alloc    ::= allocfunc ( Int , Int , FuncType , VecType , Instrs , FuncMetadata )
 // ----------------------------------------------------------------------------------------
    rule <instrs> #func(... type: TYPIDX, locals: LOCALS, body: INSTRS, metadata: META) => allocfunc(CUR, NEXTADDR, TYPE, LOCALS, INSTRS, META) ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <types>  ... TYPIDX |-> TYPE ... </types>
           <nextFuncIdx> NEXTIDX => NEXTIDX +Int 1 </nextFuncIdx>
           <funcAddrs> ADDRS => ADDRS [ NEXTIDX <- NEXTADDR ] </funcAddrs>
           ...
         </moduleInst>
         <nextFuncAddr> NEXTADDR => NEXTADDR +Int 1 </nextFuncAddr>

    rule <instrs> allocfunc(MOD, ADDR, TYPE, LOCALS, INSTRS, #meta(... id: OID, localIds: LIDS)) => . ... </instrs>
         <funcs>
           ( .Bag
          => <funcDef>
               <fAddr>    ADDR </fAddr>
               <fCode>    INSTRS   </fCode>
               <fType>    TYPE     </fType>
               <fLocal>   LOCALS   </fLocal>
               <fModInst> MOD      </fModInst>
               <funcMetadata>
                 <funcId> OID </funcId>
                 <localIds> LIDS </localIds>
                 ...
               </funcMetadata>
             </funcDef>
           )
           ...
         </funcs>

    syntax FuncMetadata ::= #meta(id: OptionalId, localIds: Map)
 // ------------------------------------------------------------
```

### Function Invocation/Return

Frames are used to store function return points.
Similar to labels, they sit on the instruction stack (the `<instrs>` cell), and `return` consumes things following it until hitting it.
Unlike labels, only one frame can be "broken" through at a time.

```k
    syntax Frame ::= "frame" Int ValTypes ValStack Map
 // --------------------------------------------------
    rule <instrs> frame MODIDX' TRANGE VALSTACK' LOCAL' => . ... </instrs>
         <valstack> VALSTACK => #take(lengthValTypes(TRANGE), VALSTACK) ++ VALSTACK' </valstack>
         <locals> _ => LOCAL' </locals>
         <curModIdx> _ => MODIDX' </curModIdx>
```

When we invoke a function, the element on the top of the stack will become the last parameter of the function.
For example, when we call `(invoke "foo" (i64.const 100) (i64.const 43) (i32.const 22))`, `(i32.const 22)` will be on the top of `<valstack>`, but it will be the last parameter of this function invocation if this function takes 3 parameters.
That is, whenever we want to `#take` or `#drop` an array of `params`, we need to reverse the array of `params` to make the type of the last parameter matching with the type of the value on the top of stack.
The `#take` function will return the parameter stack in the reversed order, then we need to reverse the stack again to get the actual parameter array we want.

```k
    syntax Instr ::= "(" "invoke" Int ")"
 // -------------------------------------
    rule <instrs> ( invoke FADDR )
               => init_locals #revs(#take(lengthValTypes(TDOMAIN), VALSTACK)) ++ #zero(TLOCALS)
               ~> block [TRANGE] INSTRS end
               ~> frame MODIDX TRANGE #drop(lengthValTypes(TDOMAIN), VALSTACK) LOCAL
               ...
         </instrs>
         <valstack>  VALSTACK => .ValStack </valstack>
         <locals> LOCAL => .Map </locals>
         <curModIdx> MODIDX => MODIDX' </curModIdx>
         <funcDef>
           <fAddr>    FADDR                     </fAddr>
           <fCode>    INSTRS                    </fCode>
           <fType>    [ TDOMAIN ] -> [ TRANGE ] </fType>
           <fLocal>   [ TLOCALS ]               </fLocal>
           <fModInst> MODIDX'                   </fModInst>
           ...
         </funcDef>

    syntax PlainInstr ::= "return"
 // ------------------------------
    rule <instrs> return ~> (_S:Stmt  => .)  ... </instrs>
    rule <instrs> return ~> (_L:Label => .)  ... </instrs>
    rule <instrs> (return => .) ~> _FR:Frame ... </instrs>
```

### Function Call

`call funcidx` and `call_indirect typeidx` are 2 control instructions that invokes a function in the current frame.

```k
    syntax PlainInstr ::= "call" Index
 // ----------------------------------
    rule <instrs> call IDX:Int => ( invoke FADDR ) ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <funcAddrs> ... IDX |-> FADDR ... </funcAddrs>
           ...
         </moduleInst>
```

TODO: Desugar to use a type-index.

```k
    syntax PlainInstr ::= "call_indirect" TypeUse
 // ---------------------------------------------
    rule <instrs> call_indirect TUSE:TypeUse => ( invoke FADDR ) ... </instrs>
         <curModIdx> CUR </curModIdx>
         <valstack> < i32 > IDX : VALSTACK => VALSTACK </valstack>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <typeIds> TYPEIDS </typeIds>
           <types> TYPES </types>
           <tabAddrs> 0 |-> ADDR </tabAddrs>
           ...
         </moduleInst>
         <tabInst>
           <tAddr> ADDR </tAddr>
           <tdata> ... IDX |-> FADDR ... </tdata>
           ...
         </tabInst>
         <funcDef>
           <fAddr> FADDR </fAddr>
           <fType> FTYPE </fType>
           ...
         </funcDef>
      requires asFuncType(TYPEIDS, TYPES, TUSE) ==K FTYPE

    rule <instrs> call_indirect TUSE:TypeUse => trap ... </instrs>
         <curModIdx> CUR </curModIdx>
         <valstack> < i32 > IDX : VALSTACK => VALSTACK </valstack>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <typeIds> TYPEIDS </typeIds>
           <types> TYPES </types>
           <tabAddrs> 0 |-> ADDR </tabAddrs>
           ...
         </moduleInst>
         <tabInst>
           <tAddr> ADDR </tAddr>
           <tdata> ... IDX |-> FADDR ... </tdata>
           ...
         </tabInst>
         <funcDef>
           <fAddr> FADDR </fAddr>
           <fType> FTYPE </fType>
           ...
         </funcDef>
      requires asFuncType(TYPEIDS, TYPES, TUSE) =/=K FTYPE

    rule <instrs> call_indirect _TUSE:TypeUse => trap ... </instrs>
         <curModIdx> CUR </curModIdx>
         <valstack> < i32 > IDX : VALSTACK => VALSTACK </valstack>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <tabAddrs> 0 |-> ADDR </tabAddrs>
           ...
         </moduleInst>
         <tabInst>
           <tAddr> ADDR  </tAddr>
           <tdata> TDATA </tdata>
           ...
         </tabInst>
      requires notBool IDX in_keys(TDATA)
```

Table
-----

When implementing a table, we first need to define the `TableElemType` type to define the type of elements inside a `tableinst`.
Currently there is only one possible value for it which is "funcref".

```k
    syntax TableElemType ::= "funcref"
 // ----------------------------------
```

The allocation of a new `tableinst`.
Currently at most one table may be defined or imported in a single module.
The only allowed `TableElemType` is "funcref", so we ignore this term in the reducted sort.
The table values are addresses into the store of functions.
The `TableSpec` production is used to define all ways that a global can specified.
A table can either be specified by giving its type (limits and `funcref`); by specifying a vector of its initial `elem`ents; or by an import and its expected type.
The specification can also include export directives.
The importing and exporting parts of specifications are dealt with in the respective sections for import and export.

```k
    syntax Defn      ::= TableDefn
    syntax TableType ::= Limits TableElemType
    syntax TableSpec ::= TableType
    syntax TableDefn ::= "(" "table" OptionalId TableSpec ")"
    syntax Alloc     ::= alloctable (OptionalId, Int, OptionalInt)
 // --------------------------------------------------------------
    rule <instrs> ( table OID:OptionalId MIN:Int         funcref ):TableDefn => alloctable(OID, MIN, .Int) ... </instrs>
      requires MIN <=Int #maxTableSize()
    rule <instrs> ( table OID:OptionalId MIN:Int MAX:Int funcref ):TableDefn => alloctable(OID, MIN,  MAX) ... </instrs>
      requires MIN <=Int #maxTableSize()
       andBool MAX <=Int #maxTableSize()

    rule <instrs> alloctable(ID, MIN, MAX) => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <tabIds> IDS => #saveId(IDS, ID, 0) </tabIds>
           <tabAddrs> .Map => (0 |-> NEXTADDR) </tabAddrs>
           ...
         </moduleInst>
         <nextTabAddr> NEXTADDR => NEXTADDR +Int 1 </nextTabAddr>
         <tabs>
           ( .Bag
          => <tabInst>
               <tAddr>   NEXTADDR </tAddr>
               <tmax>    MAX      </tmax>
               <tsize>   MIN      </tsize>
               <tdata>   .Map     </tdata>
             </tabInst>
           )
           ...
         </tabs>
```

Memory
------

When memory is allocated, it is put into the store at the next available index.
Memory can only grow in size, so the minimum size is the initial value.
Currently, only one memory may be accessible to a module, and thus the `<mAddr>` cell is an array with at most one value, at index 0.
The `MemorySpec` production is used to define all ways that a global can specified.
A memory can either be specified by giving its type (limits); by specifying a vector of its initial `data`; or by an import and its expected type.
The specification can also include export directives.
The importing and exporting parts of specifications are dealt with in the respective sections for import and export.

```k
    syntax Defn       ::= MemoryDefn
    syntax MemType    ::= Limits
    syntax MemorySpec ::= MemType
    syntax MemoryDefn ::= "(" "memory" OptionalId MemorySpec ")"
    syntax Alloc      ::= allocmemory (OptionalId, Int, OptionalInt)
 // ----------------------------------------------------------------
    rule <instrs> ( memory OID:OptionalId MIN:Int         ):MemoryDefn => allocmemory(OID, MIN, .Int) ... </instrs>
      requires MIN <=Int #maxMemorySize()
    rule <instrs> ( memory OID:OptionalId MIN:Int MAX:Int ):MemoryDefn => allocmemory(OID, MIN,  MAX) ... </instrs>
      requires MIN <=Int #maxMemorySize()
       andBool MAX <=Int #maxMemorySize()

    rule <instrs> allocmemory(ID, MIN, MAX) => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <memIds> IDS => #saveId(IDS, ID, 0) </memIds>
           <memAddrs> .Map => (0 |-> NEXTADDR) </memAddrs>
           ...
         </moduleInst>
         <nextMemAddr> NEXTADDR => NEXTADDR +Int 1 </nextMemAddr>
         <mems>
           ( .Bag
          => <memInst>
               <mAddr>   NEXTADDR </mAddr>
               <mmax>    MAX      </mmax>
               <msize>   MIN      </msize>
               ...
             </memInst>
           )
           ...
         </mems>
```

The assorted store operations take an address of type `i32` and a value.
The `storeX` operations first wrap the the value to be stored to the bit wdith `X`.
The value is encoded as bytes and stored at the "effective address", which is the address given on the stack plus offset.

```k
    syntax Instr ::= IValType "." StoreOp Int Int
 //                | FValType "." StoreOp Int Float
                   | "store" "{" Int Int Number "}"
 // -----------------------------------------------

    syntax PlainInstr ::= IValType  "." StoreOpM
                        | FValType  "." StoreOpM
 // --------------------------------------------

    syntax StoreOpM ::= StoreOp | StoreOp MemArg
 // --------------------------------------------
    rule <instrs> ITYPE . SOP:StoreOp               => ITYPE . SOP  IDX                          VAL ... </instrs>
         <valstack> < ITYPE > VAL : < i32 > IDX : VALSTACK => VALSTACK </valstack>
    rule <instrs> ITYPE . SOP:StoreOp MEMARG:MemArg => ITYPE . SOP (IDX +Int #getOffset(MEMARG)) VAL ... </instrs>
         <valstack> < ITYPE > VAL : < i32 > IDX : VALSTACK => VALSTACK </valstack>

    rule <instrs> store { WIDTH EA VAL } => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <memAddrs> 0 |-> ADDR </memAddrs>
           ...
         </moduleInst>
         <memInst>
           <mAddr>   ADDR </mAddr>
           <msize>   SIZE </msize>
           <mdata>   DATA => #setRange(DATA, EA, VAL, WIDTH) </mdata>
           ...
         </memInst>
         requires (EA +Int WIDTH) <=Int (SIZE *Int #pageSize())

    rule <instrs> store { WIDTH  EA  _ } => trap ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <memAddrs> 0 |-> ADDR </memAddrs>
           ...
         </moduleInst>
         <memInst>
           <mAddr>   ADDR </mAddr>
           <msize>   SIZE </msize>
           ...
         </memInst>
         requires (EA +Int WIDTH) >Int (SIZE *Int #pageSize())

    syntax StoreOp ::= "store" | "store8" | "store16" | "store32"
 // -------------------------------------------------------------
    rule <instrs> ITYPE . store   EA VAL => store { #numBytes(ITYPE) EA VAL           } ... </instrs>
    rule <instrs> _     . store8  EA VAL => store { 1                EA #wrap(1, VAL) } ... </instrs>
    rule <instrs> _     . store16 EA VAL => store { 2                EA #wrap(2, VAL) } ... </instrs>
    rule <instrs> i64   . store32 EA VAL => store { 4                EA #wrap(4, VAL) } ... </instrs>
```

The assorted load operations take an address of type `i32`.
The `loadX_sx` operations loads `X` bits from memory, and extend it to the right length for the return value, interpreting the bytes as either signed or unsigned according to `sx`.
The value is fetched from the "effective address", which is the address given on the stack plus offset.
Sort `Signedness` is defined in module `BYTES`.

```k
    syntax Instr ::= "load" "{" IValType Int Int Signedness"}"
                   | IValType "." LoadOp Int
 // ----------------------------------------

    syntax PlainInstr ::= IValType "." LoadOpM
                        | FValType "." LoadOpM
 // ------------------------------------------

    syntax LoadOpM ::= LoadOp | LoadOp MemArg
 // -----------------------------------------
    rule <instrs> ITYPE . LOP:LoadOp               => ITYPE . LOP  IDX                          ... </instrs>
         <valstack> < i32 > IDX : VALSTACK         => VALSTACK </valstack>
    rule <instrs> ITYPE . LOP:LoadOp MEMARG:MemArg => ITYPE . LOP (IDX +Int #getOffset(MEMARG)) ... </instrs>
         <valstack> < i32 > IDX : VALSTACK         => VALSTACK </valstack>

    rule <instrs> load { ITYPE WIDTH EA SIGN }
               => < ITYPE > #if SIGN ==K Signed
                                #then #signedWidth(WIDTH, #getRange(DATA, EA, WIDTH))
                                #else #getRange(DATA, EA, WIDTH)
                            #fi
              ...
         </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <memAddrs> 0 |-> ADDR </memAddrs>
           ...
         </moduleInst>
         <memInst>
           <mAddr>   ADDR </mAddr>
           <msize>   SIZE </msize>
           <mdata>   DATA </mdata>
           ...
         </memInst>
      requires (EA +Int WIDTH) <=Int (SIZE *Int #pageSize())

    rule <instrs> load { _ WIDTH EA _ } => trap ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <memAddrs> 0 |-> ADDR </memAddrs>
           ...
         </moduleInst>
         <memInst>
           <mAddr>   ADDR </mAddr>
           <msize>   SIZE </msize>
           ...
         </memInst>
      requires (EA +Int WIDTH) >Int (SIZE *Int #pageSize())

    syntax LoadOp ::= "load"
                    | "load8_u" | "load16_u" | "load32_u"
                    | "load8_s" | "load16_s" | "load32_s"
 // -----------------------------------------------------
    rule <instrs> ITYPE . load     EA:Int => load { ITYPE #numBytes(ITYPE) EA Unsigned } ... </instrs>
    rule <instrs> ITYPE . load8_u  EA:Int => load { ITYPE 1                EA Unsigned } ... </instrs>
    rule <instrs> ITYPE . load16_u EA:Int => load { ITYPE 2                EA Unsigned } ... </instrs>
    rule <instrs> i64   . load32_u EA:Int => load { i64   4                EA Unsigned } ... </instrs>
    rule <instrs> ITYPE . load8_s  EA:Int => load { ITYPE 1                EA Signed   } ... </instrs>
    rule <instrs> ITYPE . load16_s EA:Int => load { ITYPE 2                EA Signed   } ... </instrs>
    rule <instrs> i64   . load32_s EA:Int => load { i64   4                EA Signed   } ... </instrs>
```

`MemArg`s can optionally be passed to `load` and `store` operations.
The `offset` parameter is added to the the address given on the stack, resulting in the "effective address" to store to or load from.
The `align` parameter is for optimization only and is not allowed to influence the semantics, so we ignore it.

```k
    syntax MemArg ::= OffsetArg | AlignArg | OffsetArg AlignArg
 // -----------------------------------------------------------

    syntax OffsetArg ::= "offset=" WasmInt
    syntax AlignArg  ::= "align="  WasmInt
 // --------------------------------------

    syntax Int ::= #getOffset ( MemArg ) [function, functional]
 // -----------------------------------------------------------
    rule #getOffset(           _:AlignArg) => 0
    rule #getOffset(offset= OS           ) => OS
    rule #getOffset(offset= OS _:AlignArg) => OS
```

The `size` operation returns the size of the memory, measured in pages.

```k
    syntax PlainInstr ::= "memory.size"
 // -----------------------------------
    rule <instrs> memory.size => < i32 > SIZE ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <memAddrs> 0 |-> ADDR </memAddrs>
           ...
         </moduleInst>
         <memInst>
           <mAddr>   ADDR </mAddr>
           <msize>   SIZE </msize>
           ...
         </memInst>
```

`grow` increases the size of memory in units of pages.
Failure to grow is indicated by pushing -1 to the stack.
Success is indicated by pushing the previous memory size to the stack.
`grow` is non-deterministic and may fail either due to trying to exceed explicit max values, or because the embedder does not have resources available.
By setting the `<deterministicMemoryGrowth>` field in the configuration to `true`, the sematnics ensure memory growth only fails if the memory in question would exceed max bounds.

```k
    syntax Instr ::= "grow" Int
 // ---------------------------

    syntax PlainInstr ::= "memory.grow"
 // -----------------------------------
    rule <instrs> memory.grow => grow N ... </instrs>
         <valstack> < i32 > N : VALSTACK => VALSTACK </valstack>

    rule <instrs> grow N => < i32 > SIZE ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <memAddrs> 0 |-> ADDR </memAddrs>
           ...
         </moduleInst>
         <memInst>
           <mAddr>   ADDR </mAddr>
           <mmax>    MAX  </mmax>
           <msize>   SIZE => SIZE +Int N </msize>
           ...
         </memInst>
      requires #growthAllowed(SIZE +Int N, MAX)

    rule <instrs> grow N => < i32 > #unsigned(i32, -1) ... </instrs>
         <deterministicMemoryGrowth> DET:Bool </deterministicMemoryGrowth>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <memAddrs> 0 |-> ADDR </memAddrs>
           ...
         </moduleInst>
         <memInst>
           <mAddr>   ADDR </mAddr>
           <mmax>    MAX  </mmax>
           <msize>   SIZE </msize>
           ...
         </memInst>
      requires notBool DET
        orBool notBool #growthAllowed(SIZE +Int N, MAX)

    syntax Bool ::= #growthAllowed(Int, OptionalInt) [function]
 // -----------------------------------------------------------
    rule #growthAllowed(SIZE, .Int ) => SIZE <=Int #maxMemorySize()
    rule #growthAllowed(SIZE, I:Int) => #growthAllowed(SIZE, .Int) andBool SIZE <=Int I
```

However, the absolute max allowed size if 2^16 pages.
Incidentally, the page size is 2^16 bytes.
The maximum of table size is 2^32 bytes.

```k
    syntax Int ::= #pageSize()      [function]
    syntax Int ::= #maxMemorySize() [function]
    syntax Int ::= #maxTableSize()  [function]
 // ------------------------------------------
    rule #pageSize()      => 65536
    rule #maxMemorySize() => 65536
    rule #maxTableSize()  => 4294967296
```

Initializers
------------

### Offset

The `elem` and `data` initializers take an offset, which is an instruction.
This is not optional.
The offset can either be specified explicitly with the `offset` key word, or be a single instruction.

```k
    syntax Offset ::= "(" "offset" Instrs ")"
                    | Instrs
 // ------------------------
```

### Table initialization

Tables can be initialized with element and the element type is always `funcref`.
The initialization of a table needs an offset and a list of functions, given as `Index`s.
A table index is optional and will be default to zero.

```k
    syntax Defn     ::= ElemDefn
    syntax ElemDefn ::= "(" "elem"     Index Offset ElemSegment ")"
                      |     "elem" "{" Index        ElemSegment "}"
    syntax Stmt     ::= #initElements ( Int, Int, Map, ElemSegment )
 // ----------------------------------------------------------------
    rule <instrs> ( elem TABIDX IS:Instrs   ELEMSEGMENT ) => sequenceInstrs(IS) ~> elem { TABIDX ELEMSEGMENT } ... </instrs>
    rule <instrs> ( elem TABIDX (offset IS) ELEMSEGMENT ) => sequenceInstrs(IS) ~> elem { TABIDX ELEMSEGMENT } ... </instrs>

    rule <instrs> elem { TABIDX ELEMSEGMENT } => #initElements ( ADDR, OFFSET, FADDRS, ELEMSEGMENT ) ... </instrs>
         <curModIdx> CUR </curModIdx>
         <valstack> < i32 > OFFSET : STACK => STACK </valstack>
         <moduleInst>
           <modIdx> CUR  </modIdx>
           <funcAddrs> FADDRS </funcAddrs>
           <tabIds>  TIDS </tabIds>
           <tabAddrs> #ContextLookup(TIDS, TABIDX) |-> ADDR </tabAddrs>
           ...
         </moduleInst>

    rule <instrs> #initElements (    _,      _,      _, .ElemSegment ) => . ... </instrs>
    rule <instrs> #initElements ( ADDR, OFFSET, FADDRS,  E:Int ES    ) => #initElements ( ADDR, OFFSET +Int 1, FADDRS, ES ) ... </instrs>
         <tabInst>
           <tAddr> ADDR </tAddr>
           <tdata> DATA => DATA [ OFFSET <- FADDRS[E] ] </tdata>
           ...
         </tabInst>
```

### Memory initialization

Memories can be initialized with data, specified as a list of bytes together with an offset.
The `data` initializer simply puts these bytes into the specified memory, starting at the offset.

```k
    syntax Defn     ::= DataDefn
    syntax DataDefn ::= "(" "data"     Index Offset DataString ")"
                      | "(" "data"           Offset DataString ")"
                      |     "data" "{" Index        Bytes      "}"
 // --------------------------------------------------------------
    // Default to memory 0.
    rule <instrs> ( data       OFFSET:Offset STRINGS ) =>                     ( data   0     OFFSET    STRINGS  ) ... </instrs>
    rule <instrs> ( data MEMID IS:Instrs     STRINGS ) => sequenceInstrs(IS) ~> data { MEMID #DS2Bytes(STRINGS) } ... </instrs>
    rule <instrs> ( data MEMID (offset IS)   STRINGS ) => sequenceInstrs(IS) ~> data { MEMID #DS2Bytes(STRINGS) } ... </instrs>

    // For now, deal only with memory 0.
    rule <instrs> data { MEMIDX DSBYTES } => . ... </instrs>
         <valstack> < i32 > OFFSET : STACK => STACK </valstack>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <memIds> IDS </memIds>
           <memAddrs> #ContextLookup(IDS, MEMIDX) |-> ADDR </memAddrs>
           ...
         </moduleInst>
         <memInst>
           <mAddr> ADDR </mAddr>
           <mdata> DATA => #setRange(DATA, OFFSET, Bytes2Int(DSBYTES, LE, Unsigned), lengthBytes(DSBYTES)) </mdata>
           ...
         </memInst>

    syntax Int ::= Int "up/Int" Int [function]
 // ------------------------------------------
    rule I1 up/Int I2 => (I1 +Int (I2 -Int 1)) /Int I2 requires I2 >Int 0
```

Start Function
--------------

The `start` component of a module declares the function index of a `start function` that is automatically invoked when the module is instantiated, after `tables` and `memories` have been initialized.

```k
    syntax Defn      ::= StartDefn
    syntax StartDefn ::= "(" "start" Index ")"
 // ------------------------------------------
    rule <instrs> ( start IDX:Int ) => ( invoke FADDR ) ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <funcAddrs> ... IDX |-> FADDR ... </funcAddrs>
           ...
         </moduleInst>
```

Export
------

Exports make functions, tables, memories and globals available for importing into other modules.

```k
    syntax Defn       ::= ExportDefn
    syntax ExportDefn ::= "(" "export" WasmString "(" Externval ")" ")"
    syntax Alloc      ::= ExportDefn
 // --------------------------------
    rule <instrs> ( export ENAME ( _:AllocatedKind TFIDX:Index ) ) => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <exports> EXPORTS => EXPORTS [ ENAME <- TFIDX ] </exports>
           ...
         </moduleInst>
```

Imports
-------

Imports need to describe the type of what is imported.
That an import is really a subtype of the declared import needs to be checked at instantiation time.
The value of a global gets copied when it is imported.

```k
    syntax Defn       ::= ImportDefn
    syntax ImportDefn ::= "(" "import" WasmString WasmString ImportDesc ")"
    syntax ImportDesc ::= #funcDesc(id: OptionalId, type: Int)
                        | "(" "table"  OptionalId TableType            ")" [klabel( tabImportDesc)]
                        | "(" "memory" OptionalId MemType              ")" [klabel( memImportDesc)]
                        | "(" "global" OptionalId TextFormatGlobalType ")" [klabel(globImportDesc)]
    syntax Alloc      ::= ImportDefn
 // --------------------------------
    rule <instrs> ( import MOD NAME #funcDesc(... type: TIDX) ) => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <types> TYPES </types>
           <funcAddrs> FS => FS [NEXT <- ADDR] </funcAddrs>
           <nextFuncIdx> NEXT => NEXT +Int 1 </nextFuncIdx>
           ...
         </moduleInst>
         <moduleRegistry> ... MOD |-> MODIDX ... </moduleRegistry>
         <moduleInst>
           <modIdx> MODIDX </modIdx>
           <funcAddrs> ... IDX |-> ADDR ... </funcAddrs>
           <exports>   ... NAME |-> IDX ... </exports>
           ...
         </moduleInst>
         <funcDef>
           <fAddr> ADDR </fAddr>
           <fType> FTYPE </fType>
           ...
         </funcDef>
      requires FTYPE ==K TYPES[TIDX]

    rule <instrs> ( import MOD NAME (table OID:OptionalId (LIM _):TableType) ) => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <tabIds> IDS => #saveId(IDS, OID, 0) </tabIds>
           <tabAddrs> .Map => 0 |-> ADDR </tabAddrs>
           ...
         </moduleInst>
         <moduleRegistry> ... MOD |-> MODIDX ... </moduleRegistry>
         <moduleInst>
           <modIdx> MODIDX </modIdx>
           <tabIds> IDS' </tabIds>
           <tabAddrs> ... #ContextLookup(IDS' , TFIDX) |-> ADDR ... </tabAddrs>
           <exports>  ... NAME |-> TFIDX                        ... </exports>
           ...
         </moduleInst>
         <tabInst>
           <tAddr> ADDR </tAddr>
           <tmax>  MAX  </tmax>
           <tsize> SIZE </tsize>
           ...
         </tabInst>
       requires #limitsMatchImport(SIZE, MAX, LIM)

    rule <instrs> ( import MOD NAME (memory OID:OptionalId LIM:Limits) ) => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <memIds> IDS => #saveId(IDS, OID, 0) </memIds>
           <memAddrs> .Map => 0 |-> ADDR </memAddrs>
           ...
         </moduleInst>
         <moduleRegistry> ... MOD |-> MODIDX ... </moduleRegistry>
         <moduleInst>
           <modIdx> MODIDX </modIdx>
           <memIds> IDS' </memIds>
           <memAddrs> ... #ContextLookup(IDS' , TFIDX) |-> ADDR ... </memAddrs>
           <exports>  ... NAME |-> TFIDX                        ... </exports>
           ...
         </moduleInst>
         <memInst>
           <mAddr> ADDR </mAddr>
           <mmax>  MAX  </mmax>
           <msize> SIZE </msize>
           ...
         </memInst>
       requires #limitsMatchImport(SIZE, MAX, LIM)

    rule <instrs> ( import MOD NAME (global OID:OptionalId TGTYP:TextFormatGlobalType) ) => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <globIds> IDS => #saveId(IDS, OID, NEXT) </globIds>
           <globalAddrs> GS => GS [NEXT <- ADDR] </globalAddrs>
           <nextGlobIdx> NEXT => NEXT +Int 1 </nextGlobIdx>
           ...
         </moduleInst>
         <moduleRegistry> ... MOD |-> MODIDX ... </moduleRegistry>
         <moduleInst>
           <modIdx> MODIDX </modIdx>
           <globIds> IDS' </globIds>
           <globalAddrs> ... #ContextLookup(IDS' , TFIDX) |-> ADDR ... </globalAddrs>
           <exports>     ... NAME |-> TFIDX                        ... </exports>
           ...
         </moduleInst>
         <globalInst>
           <gAddr>  ADDR    </gAddr>
           <gValue> <TYP> _ </gValue>
           <gMut>   MUT     </gMut>
         </globalInst>
       requires asGMut(TGTYP) ==K MUT TYP
```

Tables and memories have proper subtyping, unlike globals and functions where a type is only a subtype of itself.
Subtyping is determined by whether the limits of one table/memory fit in the limits of another.
The following function checks if the limits in the first parameter *match*, i.e. is a subtype of, the limits in the second.

```k
    syntax Bool ::= #limitsMatchImport(Int, OptionalInt, Limits) [function]
 // -----------------------------------------------------------------------
    rule #limitsMatchImport(L1,      _, L2:Int   ) => L1 >=Int L2
    rule #limitsMatchImport( _,   .Int,  _:Int  _) => false
    rule #limitsMatchImport(L1, U1:Int, L2:Int U2) => L1 >=Int L2 andBool U1 <=Int U2
```

Module Instantiation
--------------------

There is some dependencies among definitions that require that we do them in a certain order, even though they may appear in many valid orders.
First, functions, tables, memories and globals get *allocated*.
Then, tables, memories and globals get *instantiated* with elements, data and initialization vectors.
However, since (currently) globals can only make use of imported globals to be instantiated, we can initialize at allocation time.
Finally, the start function is invoked.
Exports may appear anywhere in a module, but can only be performed after what they refer to has been allocated.
Exports that are inlined in a definition, e.g., `func (export "foo") ...`, are safe to extract as they appear.
Imports must appear before any allocations in a module, due to validation.

A subtle point is related to tables with inline `elem` definitions: since these may refer to functions by identifier, we need to make sure that tables definitions come after function definitions.

`sortModule` takes a list of definitions and returns a map with different groups of definitions, preserving the order within each group.
The groups are chosen to represent different stages of allocation and instantiation.

```k
    syntax ModuleDecl ::= #module ( types: Defns, funcs: Defns, tables: Defns, mems: Defns, globals: Defns, elem: Defns, data: Defns, start: Defns, importDefns: Defns, exports: Defns, metadata: ModuleMetadata)
 // -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

    syntax ModuleDecl ::= #emptyModule(OptionalId) [function, functional]
 // ---------------------------------------------------------------------
    rule #emptyModule(OID) =>  #module (... types: .Defns, funcs: .Defns, tables: .Defns, mems: .Defns, globals: .Defns, elem: .Defns, data: .Defns, start: .Defns, importDefns: .Defns, exports: .Defns, metadata: #meta(... id: OID, funcIds: .Map))

    syntax ModuleMetadata ::= #meta(id: OptionalId, funcIds: Map)
 // -------------------------------------------------------------
```

A new module instance gets allocated.
Then, the surrounding `module` tag is discarded, and the definitions are executed, putting them into the module currently being defined.

```k
    rule <instrs> #module(... types: TS, funcs: FS, tables: TABS, mems: MS, globals: GS, elem: EL, data: DAT, start: S,  importDefns: IS, exports: ES,
                         metadata: #meta(... id: OID, funcIds: FIDS))
               => sequenceDefns(TS)
               ~> sequenceDefns(IS)
               ~> sequenceDefns(FS)
               ~> sequenceDefns(GS)
               ~> sequenceDefns(MS)
               ~> sequenceDefns(TABS)
               ~> sequenceDefns(ES)
               ~> sequenceDefns(EL)
               ~> sequenceDefns(DAT)
               ~> sequenceDefns(S)
               ...
         </instrs>
         <curModIdx> _ => NEXT </curModIdx>
         <nextModuleIdx> NEXT => NEXT +Int 1 </nextModuleIdx>
         <moduleIds> IDS => #saveId(IDS, OID, NEXT) </moduleIds>
         <moduleInstances>
           ( .Bag
          => <moduleInst>
               <modIdx> NEXT </modIdx>
               <moduleMetadata>
                 <moduleId> OID </moduleId>
                 <funcIds> FIDS </funcIds>
                 ...
               </moduleMetadata>
               ...
             </moduleInst>
           )
           ...
         </moduleInstances>
```

After a module is instantiated, it should be saved somewhere.
How this is done is up to the embedder.

```k
endmodule
```
