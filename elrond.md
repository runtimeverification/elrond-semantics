Elrond Semantics
================

```k
require "blockchain-k-plugin/krypto.md"
require "wasm-text.md"
require "wasm-coverage.md"
```

Elrond Node
-----------

```k
module ELROND-NODE
    imports DOMAINS
    imports WASM-TEXT

    configuration
      <node>
        <commands> .K </commands>
        <callState>
          <callArgs> .List </callArgs>
          <caller> .Bytes </caller>
          <callee> .Bytes </callee>
          <callValue> 0 </callValue>
          <esdtTokenName> .Bytes </esdtTokenName>
          <esdtValue> 0 </esdtValue>
          <out> .List </out>
          <message> .Bytes </message>
          <returnCode> .ReturnCode </returnCode>
          <interimStates> .List </interimStates>
          <logs> .List </logs>
        </callState>
        <activeAccounts> .Set </activeAccounts>
        <accounts>
          <account multiplicity="*" type="Map">
             <address> .Bytes </address>
             <nonce> 0 </nonce>
             <balance> 0 </balance>
```

If the codeIdx is ".CodeIndex", it means the account is not a contract.
If the codeIdx is an integer, it is the exact module index from the Wasm store which specifies the contract.

```k
             <codeIdx> .CodeIndex </codeIdx>
```
Storage maps byte arrays to byte arrays.

```k
             <storage> .Map </storage>
           </account>
         </accounts>
         <previousBlockInfo>
           <prevBlockTimestamp>  0 </prevBlockTimestamp>
           <prevBlockNonce>      0 </prevBlockNonce>
           <prevBlockRound>      0 </prevBlockRound>
           <prevBlockEpoch>      0 </prevBlockEpoch>
           <prevBlockRandomSeed> padRightBytes(.Bytes, 48, 0) </prevBlockRandomSeed>
         </previousBlockInfo>
         <currentBlockInfo>
           <curBlockTimestamp>  0 </curBlockTimestamp>
           <curBlockNonce>      0 </curBlockNonce>
           <curBlockRound>      0 </curBlockRound>
           <curBlockEpoch>      0 </curBlockEpoch>
           <curBlockRandomSeed> padRightBytes(.Bytes, 48, 0) </curBlockRandomSeed>
         </currentBlockInfo>
       </node>

    syntax ReturnCode    ::= ".ReturnCode"
                           | "OK"          [klabel(OK), symbol]
                           | ExceptionCode
    syntax ExceptionCode ::= "OutOfFunds"
                           | "UserError"   [klabel(UserError), symbol]
 // ------------------------------------------------------------------

    syntax Address ::= Bytes
                     | WasmStringToken
    syntax Bytes ::= #address2Bytes ( Address ) [function, functional]
 // ------------------------------------------------------------------
    rule #address2Bytes(ADDR:WasmStringToken) => String2Bytes(#parseWasmString(ADDR))
    rule #address2Bytes(ADDR:Bytes) => ADDR

    syntax CodeIndex ::= ".CodeIndex" [klabel(.CodeIndex), symbol]
                       | Int
 // ----------------------------------------------------------

    syntax Code ::= ".Code" [klabel(.Code), symbol]
                  | ModuleDecl
 // ----------------------------------------------

endmodule
```

Auto Allocate Host Modules
--------------------------

When `AUTO-ALLOCATE` is imported, an new module will be automatically created and registered whenever necessary to resolve an import.
This makes it possible to implement host modules easily in K.
Accessing the import will result in an instruction being left on the `instrs` cell that can't be resolved in the regular Wasm semantics.
Instead, the embedder can add rules for handling the host import.

Currently, only function imports are supported.
Calling an imported host function will result in `hostCall(MODULE_NAME, FUNCTION_NAME, FUNCTION_TYPE)` being left on the `instrs` cell.

```k
module WASM-AUTO-ALLOCATE
    imports WASM-TEXT

    syntax Stmt ::= "newEmptyModule" WasmString
 // -------------------------------------------
    rule <instrs> newEmptyModule MODNAME => . ... </instrs>
         <moduleRegistry> MR => MR [ MODNAME <- NEXT ] </moduleRegistry>
         <nextModuleIdx> NEXT => NEXT +Int 1 </nextModuleIdx>
         <moduleInstances> ( .Bag => <moduleInst> <modIdx> NEXT </modIdx> ... </moduleInst>) ... </moduleInstances>

    syntax Stmts ::=  autoAllocModules ( ModuleDecl, Map ) [function]
                   | #autoAllocModules ( Defns     , Map ) [function]
 // -----------------------------------------------------------------
    rule  autoAllocModules(#module(... importDefns:IS), MR) => #autoAllocModules(IS, MR)
```

In helper function `#autoAllocModules`, the module registry map is passed along to check if the module being imported from is present.
It is treated purely as a key set -- the actual stored values are not used or stored anywhere.

```k
    rule #autoAllocModules(.Defns, _) => .Stmts
    rule #autoAllocModules((#import(MOD, _, _) DS) => DS, MR) requires MOD in_keys(MR)
    rule #autoAllocModules((#import(MOD, _, _) DS), MR)
      => newEmptyModule MOD #autoAllocModules(DS, MR [MOD <- -1])
      requires notBool MOD in_keys(MR)

    rule <instrs> MD:ModuleDecl
               => sequenceStmts(autoAllocModules(MD, MR))
               ~> MD
              ...
         </instrs>
         <moduleRegistry> MR </moduleRegistry>
      requires autoAllocModules(MD, MR) =/=K .Stmts
      [priority(10)]

    syntax Instr ::= hostCall(String, String, FuncType)
 // ---------------------------------------------------
    rule <instrs> (. => allocfunc(HOSTMOD, NEXTADDR, TYPE, [ .ValTypes ], hostCall(wasmString2StringStripped(MOD), wasmString2StringStripped(NAME), TYPE) .Instrs, #meta(... id: String2Identifier("$auto-alloc:" +String #parseWasmString(MOD) +String ":" +String #parseWasmString(NAME) ), localIds: .Map )))
               ~> #import(MOD, NAME, #funcDesc(... type: TIDX))
              ...
         </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <types> ... TIDX |-> TYPE ... </types>
           ...
        </moduleInst>
        <nextFuncAddr> NEXTADDR => NEXTADDR +Int 1 </nextFuncAddr>
        <moduleRegistry> ... MOD |-> HOSTMOD ... </moduleRegistry>
        <moduleInst>
          <modIdx> HOSTMOD </modIdx>
          <exports> EXPORTS => EXPORTS [NAME <- NEXTFUNC ] </exports>
          <funcAddrs> FS => FS [NEXTFUNC <- NEXTADDR] </funcAddrs>
          <nextFuncIdx> NEXTFUNC => NEXTFUNC +Int 1 </nextFuncIdx>
          <nextTypeIdx> NEXTTYPE => NEXTTYPE +Int 1 </nextTypeIdx>
          <types> TYPES => TYPES [ NEXTTYPE <- TYPE ] </types>
          ...
        </moduleInst>
      requires notBool NAME in_keys(EXPORTS)

    syntax String ::= wasmString2StringStripped ( WasmString ) [function]
                    | #stripQuotes ( String ) [function]
 // ----------------------------------------------------
    rule wasmString2StringStripped(WS) => #stripQuotes(#parseWasmString(WS))

    rule #stripQuotes(S) => replaceAll(S, "\"", "")

endmodule
```

Combine Elrond Node With Wasm
-----------------------------

```k
module ELROND
    imports KRYPTO
    imports WASM-TEXT
    imports WASM-COVERAGE
    imports WASM-AUTO-ALLOCATE
    imports ELROND-NODE

    configuration
      <elrond>
        <wasmCoverage/>
        <node/>
        <bigIntHeap> .Map </bigIntHeap>
        <bytesStack> .BytesStack </bytesStack>
        <logging> "" </logging>
      </elrond>
```

### Helper Functions

#### Bytes Stack

```k
    syntax BytesStack ::= List{Bytes, ":"}
 // --------------------------------------

    syntax BytesOp ::= #pushBytes ( Bytes )
                     | "#dropBytes"
 // ---------------------------------------
    rule <instrs> #pushBytes(BS) => . ... </instrs>
         <bytesStack> STACK => BS : STACK </bytesStack>

    rule <instrs> #dropBytes => . ... </instrs>
         <bytesStack> _ : STACK => STACK </bytesStack>

    syntax InternalInstr ::= "#returnLength"
 // ----------------------------------------
    rule <instrs> #returnLength => i32.const lengthBytes(BS) ... </instrs>
         <bytesStack> BS : _ </bytesStack>
```

#### World State

```k
    syntax Accounts ::= "{" AccountsCellFragment "|" Set "}"
 // --------------------------------------------------------

    syntax InternalCmd ::= "pushWorldState"
 // ---------------------------------------
    rule <commands> pushWorldState => . ... </commands>
         <interimStates> (.List => ListItem({ ACCTDATA | ACCTS })) ... </interimStates>
         <activeAccounts> ACCTS    </activeAccounts>
         <accounts>       ACCTDATA </accounts>
      [priority(60)]

    syntax InternalCmd ::= "popWorldState"
 // --------------------------------------
    rule <commands> popWorldState => . ... </commands>
         <interimStates> (ListItem({ ACCTDATA | ACCTS }) => .List) ... </interimStates>
         <activeAccounts> _ => ACCTS    </activeAccounts>
         <accounts>       _ => ACCTDATA </accounts>
      [priority(60)]

    syntax InternalCmd ::= "dropWorldState"
 // ---------------------------------------
    rule <commands> dropWorldState => . ... </commands>
         <interimStates> (ListItem(_) => .List) ... </interimStates>
      [priority(60)]
```

### Node And Wasm VM Synchronization

- `#endWasm` waits for the Wasm VM to finish the execution and check the return code.

```k
    syntax InternalCmd ::= "#endWasm"
 // ---------------------------------
    rule <commands> #endWasm => dropWorldState ... </commands>
         <returnCode> .ReturnCode => OK </returnCode>
         <instrs> . </instrs>
      [priority(60)]
```

- `#exception` drops the rest of the computation in the `commands` and `instrs` cells and reverts the state.

```k
    syntax InternalCmd ::= #exception ( ExceptionCode )
 // ---------------------------------------------------
    rule <commands> (#exception(EC) ~> _) => popWorldState </commands>
         <returnCode> _ => EC </returnCode>
         <instrs> _ => . </instrs>
      [priority(10)]
```

### Managing Accounts

```k
    syntax InternalCmd ::= createAccount ( Bytes ) [klabel(createAccount), symbol]
 // ------------------------------------------------------------------------------
    rule <commands> createAccount(ADDR) => . ... </commands>
         <activeAccounts> ... (.Set => SetItem(ADDR)) ... </activeAccounts>
         <accounts>
           ( .Bag
          => <account>
               <address> ADDR </address>
               ...
             </account>
           )
           ...
         </accounts>
         <logging> S => S +String " -- initAccount new " +String Bytes2String(ADDR) </logging>
      [priority(60)]

    syntax InternalCmd ::= setAccountFields    ( Bytes, Int, Int, CodeIndex, Map )
                         | setAccountCodeIndex ( Bytes, CodeIndex )
 // ---------------------------------------------------------------
    rule <commands> setAccountFields(ADDR, NONCE, BALANCE, CODEIDX, STORAGE) => . ... </commands>
         <account>
           <address> ADDR </address>
           <nonce> _ => NONCE </nonce>
           <balance> _ => BALANCE </balance>
           <codeIdx> _ => CODEIDX </codeIdx>
           <storage> _ => STORAGE </storage>
         </account>
      [priority(60)]

    rule <commands> setAccountCodeIndex(ADDR, CODEIDX) => . ... </commands>
         <account>
           <address> ADDR </address>
           <codeIdx> _ => CODEIDX </codeIdx>
           ...
         </account>
      [priority(60)]
```

### Transfer Funds

```k
    syntax InternalCmd ::= transferFunds ( Bytes, Bytes, Int )
                         | "#transferSuccess"
 // -----------------------------------------
    rule <commands> transferFunds(ACCT, ACCT, VALUE) => #transferSuccess ... </commands>
         <account>
           <address> ACCT </address>
           <balance> ORIGFROM </balance>
           ...
         </account>
      requires VALUE <=Int ORIGFROM
      [priority(60)]

    rule <commands> transferFunds(ACCTFROM, ACCTTO, VALUE) => #transferSuccess ... </commands>
         <account>
           <address> ACCTFROM </address>
           <balance> ORIGFROM => ORIGFROM -Int VALUE </balance>
           ...
         </account>
         <account>
           <address> ACCTTO </address>
           <balance> ORIGTO => ORIGTO +Int VALUE </balance>
           ...
         </account>
      requires ACCTFROM =/=K ACCTTO andBool VALUE <=Int ORIGFROM
      [priority(60)]

    rule <commands> #transferSuccess => . ... </commands>
         <instrs> . </instrs>
```

### Calling Contract

```k
    syntax InternalCmd ::= callContract ( Bytes, Bytes, Int,     String, List, Int, Int ) [klabel(callContractString)]
                         | callContract ( Bytes, Bytes, Int, WasmString, List, Int, Int ) [klabel(callContractWasmString)]
                         | mkCall       ( Bytes, Bytes, Int, WasmString, List, Int, Int )
 // -------------------------------------------------------------------------------------
    rule <commands> callContract(FROM, TO, VALUE, FUNCNAME:String, ARGS, GASLIMIT, GASPRICE)
                 => callContract(FROM, TO, VALUE, #token("\"" +String FUNCNAME +String "\"", "WasmStringToken"), ARGS, GASLIMIT, GASPRICE)
                    ...
         </commands>
      [priority(60)]

    rule <commands> callContract(FROM, TO, VALUE, FUNCNAME:WasmStringToken, ARGS, GASLIMIT, GASPRICE)
                 => pushWorldState
                 ~> transferFunds(FROM, TO, VALUE)
                 ~> mkCall(FROM, TO, VALUE, FUNCNAME, ARGS, GASLIMIT, GASPRICE)
                 ~> #endWasm
                    ...
         </commands>
      [priority(60)]

    rule <commands> mkCall(FROM, TO, VALUE, FUNCNAME:WasmStringToken, ARGS, _GASLIMIT, _GASPRICE) => . ... </commands>
         <callArgs> _ => ARGS </callArgs>
         <caller> _ => FROM </caller>
         <callee> _ => TO   </callee>
         <callValue> _ => VALUE </callValue>
         <out> _ => .List </out>
         <message> _ => .Bytes </message>
         <returnCode> _ => .ReturnCode </returnCode>
         <logs> _ => .List </logs>
         <bigIntHeap> _ => .Map </bigIntHeap>
         <account>
           <address> TO </address>
           <codeIdx> CODE:Int </codeIdx>
           ...
         </account>
         <moduleInst>
           <modIdx> CODE </modIdx>
           <exports> ... FUNCNAME |-> FUNCIDX:Int </exports>
           <funcAddrs> ... FUNCIDX |-> FUNCADDR:Int ... </funcAddrs>
           ...
         </moduleInst>
         <instrs> . => ( invoke FUNCADDR ) </instrs>
         <logging> S => S +String " -- callContract " +String #parseWasmString(FUNCNAME) </logging>
      [priority(60)]
```

Host Calls
----------

Here, host calls are implemented, by defining the semantics when `hostCall(MODULE_NAME, EXPORT_NAME, TYPE)` is left on top of the `instrs` cell.

### Helper functions

#### Misc

```k
    syntax Bool ::= #hasPrefix ( String , String ) [function, functional]
 // ---------------------------------------------------------------------
    rule #hasPrefix(STR, PREFIX) => true
      requires lengthString(STR) >=Int lengthString(PREFIX)
       andBool substrString(STR, 0, lengthString(PREFIX)) ==String PREFIX

    rule #hasPrefix(STR, PREFIX) => false
      requires notBool (       lengthString(STR) >=Int lengthString(PREFIX)
                       andBool substrString(STR, 0, lengthString(PREFIX)) ==String PREFIX)
```

#### Memory

```k
    syntax InternalInstr ::= #memStoreFromBytesStack ( Int )
                           | #memStore ( offset: Int , bytes: Bytes )
 // -----------------------------------------------------------------
    rule <instrs> #memStoreFromBytesStack(OFFSET) => #memStore(OFFSET, BS) ... </instrs>
         <bytesStack> BS : _ </bytesStack>

    rule <instrs> #memStore(OFFSET, BS) => . ... </instrs>
         <callee> CALLEE </callee>
         <account>
           <address> CALLEE </address>
           <codeIdx> MODIDX:Int </codeIdx>
           ...
         </account>
         <moduleInst>
           <modIdx> MODIDX </modIdx>
           <memAddrs> 0 |-> MEMADDR </memAddrs>
           ...
         </moduleInst>
         <memInst>
           <mAddr> MEMADDR </mAddr>
           <msize> SIZE </msize>
           <mdata> DATA => #setBytesRange(DATA, OFFSET, BS) </mdata>
           ...
         </memInst>
      requires OFFSET +Int lengthBytes(BS) <=Int (SIZE *Int #pageSize())

    syntax InternalInstr ::= #memLoad ( offset: Int , length: Int )
 // ---------------------------------------------------------------
    rule <instrs> #memLoad(OFFSET, LENGTH) => . ... </instrs>
         <bytesStack> STACK => #getBytesRange(DATA, OFFSET, LENGTH) : STACK </bytesStack>
         <callee> CALLEE </callee>
         <account>
           <address> CALLEE </address>
           <codeIdx> MODIDX:Int </codeIdx>
           ...
         </account>
         <moduleInst>
           <modIdx> MODIDX </modIdx>
           <memAddrs> 0 |-> MEMADDR </memAddrs>
           ...
         </moduleInst>
         <memInst>
           <mAddr> MEMADDR </mAddr>
           <msize> SIZE </msize>
           <mdata> DATA </mdata>
           ...
         </memInst>
      requires OFFSET +Int LENGTH <=Int (SIZE *Int #pageSize())
```

#### Storage

Storing a value returns a status code indicating if and how the storage was modified.

TODO: Implement [reserved keys and read-only runtimes](https://github.com/ElrondNetwork/arwen-wasm-vm/blob/d6ea0489081f81fefba002609c34ece1365373dd/arwen/contexts/storage.go#L111).

```k
    syntax InternalInstr ::= "#storageStore"
 // ----------------------------------------
    rule <instrs> #storageStore => #setStorage(KEY, VALUE) ... </instrs>
         <bytesStack> VALUE : KEY : STACK => STACK </bytesStack>

    syntax InternalInstr ::= #setStorage ( Bytes , Bytes )
 // ------------------------------------------------------
    rule <instrs> #setStorage(KEY, VALUE)
               => #isReservedKey(Bytes2String(KEY))
               ~> #writeToStorage(KEY, VALUE)
                  ...
         </instrs>

    syntax InternalInstr ::= #writeToStorage ( Bytes , Bytes )
 // ----------------------------------------------------------
    rule <instrs> #writeToStorage(KEY, VALUE) => i32.const #storageStatus(STORAGE, KEY, VALUE) ... </instrs>
         <callee> CALLEE </callee>
         <account>
           <address> CALLEE </address>
           <storage> STORAGE => #updateStorage(STORAGE, KEY, VALUE) </storage>
           ...
         </account>

    syntax InternalInstr ::= #isReservedKey ( String )
 // --------------------------------------------------
    rule <instrs> #isReservedKey(KEY) => . ... </instrs>
      requires notBool #hasPrefix(KEY, "ELROND")

    rule <commands> (. => #exception(UserError)) ... </commands>
         <instrs> (#isReservedKey(KEY) ~> _) => . </instrs>
         <message> _ => String2Bytes("cannot write to storage under Elrond reserved key") </message>
      requires         #hasPrefix(KEY, "ELROND")

    syntax InternalInstr ::= "#storageLoad"
 // ---------------------------------------
    rule <instrs> #storageLoad => . ... </instrs>
         <bytesStack> KEY : STACK => #lookupStorage(STORAGE, KEY) : STACK </bytesStack>
         <callee> CALLEE </callee>
         <account>
           <address> CALLEE </address>
           <storage> STORAGE </storage>
           ...
         </account>

    syntax Map ::= #updateStorage ( Map , key : Bytes , val : Bytes ) [function, functional]
 // ----------------------------------------------------------------------------------------
    rule #updateStorage(STOR, KEY, VAL) => STOR [KEY <- undef] requires VAL  ==K .Bytes
    rule #updateStorage(STOR, KEY, VAL) => STOR [KEY <- VAL  ] requires VAL =/=K .Bytes

    syntax Bytes ::= #lookupStorage ( Map , key: Bytes ) [function]
 // ---------------------------------------------------------------
    rule #lookupStorage(STORAGE, KEY) => {STORAGE[KEY]}:>Bytes
      requires         KEY in_keys(STORAGE)

    rule #lookupStorage(STORAGE, KEY) => .Bytes
      requires notBool KEY in_keys(STORAGE)

    syntax Int ::= #storageStatus ( Map , key : Bytes , val : Bytes ) [function, functional]
                 | #StorageUnmodified () [function, functional]
                 | #StorageModified   () [function, functional]
                 | #StorageAdded      () [function, functional]
                 | #StorageDeleted    () [function, functional]
 // -----------------------------------------------------------
    rule #storageStatus(STOR, KEY,  VAL) => #StorageUnmodified() requires VAL  ==K .Bytes andBool notBool KEY in_keys(STOR)
    rule #storageStatus(STOR, KEY,  VAL) => #StorageUnmodified() requires VAL =/=K .Bytes andBool         KEY in_keys(STOR) andBool STOR[KEY]  ==K VAL
    rule #storageStatus(STOR, KEY,  VAL) => #StorageModified  () requires VAL =/=K .Bytes andBool         KEY in_keys(STOR) andBool STOR[KEY] =/=K VAL
    rule #storageStatus(STOR, KEY,  VAL) => #StorageAdded     () requires VAL =/=K .Bytes andBool notBool KEY in_keys(STOR)
    rule #storageStatus(STOR, KEY,  VAL) => #StorageDeleted   () requires VAL  ==K .Bytes andBool         KEY in_keys(STOR)

    rule #StorageUnmodified() => 0
    rule #StorageModified  () => 1
    rule #StorageAdded     () => 2
    rule #StorageDeleted   () => 3
```

#### Integer Operation

```k
    syntax Int ::= #cmpInt ( Int , Int ) [function, functional]
 // -----------------------------------------------------------
    rule #cmpInt(I1, I2) => -1 requires I1  <Int I2
    rule #cmpInt(I1, I2) =>  1 requires I1  >Int I2
    rule #cmpInt(I1, I2) =>  0 requires I1 ==Int I2

    syntax Int ::= #bigIntSign ( Int ) [function, functional]
 // ---------------------------------------------------------
    rule #bigIntSign(I) => 0  requires I ==Int 0
    rule #bigIntSign(I) => 1  requires I >Int 0
    rule #bigIntSign(I) => -1 requires I <Int 0

    syntax Int ::= "minSInt32"
                 | "maxSInt32"
                 | "minUInt32"
                 | "maxUInt32"
                 | "minSInt64"
                 | "maxSInt64"
                 | "minUInt64"
                 | "maxUInt64"
 // --------------------------
    rule minSInt32 => -2147483648           [macro] /* -2^31     */
    rule maxSInt32 =>  2147483647           [macro] /*  2^31 - 1 */
    rule minUInt32 =>  0                    [macro]
    rule maxUInt32 =>  4294967296           [macro] /*  2^32 - 1 */
    rule minSInt64 => -9223372036854775808  [macro] /* -2^63     */
    rule maxSInt64 =>  9223372036854775807  [macro] /*  2^63 - 1 */
    rule minUInt64 =>  0                    [macro]
    rule maxUInt64 =>  18446744073709551615 [macro] /*  2^64 - 1 */

    syntax InternalInstr ::= #returnIfUInt64 ( Int , String )
                           | #returnIfSInt64 ( Int , String )
 // ---------------------------------------------------------
    rule <instrs> #returnIfUInt64(V, _) => i64.const V ... </instrs>
      requires          minUInt64 <=Int V andBool V <=Int maxUInt64

    rule <commands> (. => #exception(UserError)) ... </commands>
         <instrs> (#returnIfUInt64(V, ERRORMSG) ~> _) => . </instrs>
         <message> _ => String2Bytes(ERRORMSG) </message>
      requires notBool (minUInt64 <=Int V andBool V <=Int maxUInt64)

    rule <instrs> #returnIfSInt64(V, _) => i64.const V ... </instrs>
      requires          minSInt64 <=Int V andBool V <=Int maxSInt64

    rule <commands> (. => #exception(UserError)) ... </commands>
         <instrs> (#returnIfSInt64(V, ERRORMSG) ~> _) => . </instrs>
         <message> _ => String2Bytes(ERRORMSG) </message>
      requires notBool (minSInt64 <=Int V andBool V <=Int maxSInt64)

    syntax InternalInstr ::= #loadBytesAsUInt64 ( String )
                           | #loadBytesAsSInt64 ( String )
 // ------------------------------------------------------
    rule <instrs> #loadBytesAsUInt64(ERRORMSG) => #returnIfUInt64(Bytes2Int(BS, BE, Unsigned), ERRORMSG) ... </instrs>
         <bytesStack> BS : STACK => STACK </bytesStack>

    rule <instrs> #loadBytesAsSInt64(ERRORMSG) => #returnIfSInt64(Bytes2Int(BS, BE, Signed), ERRORMSG) ... </instrs>
         <bytesStack> BS : STACK => STACK </bytesStack>
```

#### Output

```k
    syntax InternalInstr ::= "#appendToOutFromBytesStack"
                           | #appendToOut ( Bytes )
 // -----------------------------------------------
    rule <instrs> #appendToOutFromBytesStack => . ... </instrs>
         <bytesStack> OUT : STACK => STACK </bytesStack>
         <out> ... (.List => ListItem(OUT)) </out>

    rule <instrs> #appendToOut(OUT) => . ... </instrs>
         <out> ... (.List => ListItem(OUT)) </out>
```

#### Parsing

```k
    syntax String ::= #alignHexString ( String ) [function, functional]
 // -------------------------------------------------------------------
    rule #alignHexString(S) => S             requires         lengthString(S) modInt 2 ==Int 0
    rule #alignHexString(S) => "0" +String S requires notBool lengthString(S) modInt 2 ==Int 0

    syntax Bytes ::= #parseHexBytes     ( String ) [function]
                   | #parseHexBytesAux  ( String ) [function]
 // ---------------------------------------------------------
    rule #parseHexBytes(S)  => #parseHexBytesAux(#alignHexString(S))
    rule #parseHexBytesAux("") => .Bytes
    rule #parseHexBytesAux(S)  => Int2Bytes(lengthString(S) /Int 2, String2Base(S, 16), BE)
      requires 2 <=Int lengthString(S)
```

#### Crypto

```k
    syntax HashBytesStackInstr ::= "#sha256FromBytesStack"
 // ------------------------------------------------------
    rule <instrs> #sha256FromBytesStack => . ... </instrs>
         <bytesStack> (DATA => #parseHexBytes(Sha256(Bytes2String(DATA)))) : _STACK </bytesStack>

    syntax HashBytesStackInstr ::= "#keccakFromBytesStack"
 // ------------------------------------------------------
    rule <instrs> #keccakFromBytesStack => . ... </instrs>
         <bytesStack> (DATA => #parseHexBytes(Keccak256(Bytes2String(DATA)))) : _STACK </bytesStack>

    syntax InternalInstr ::= #hashMemory ( Int , Int , Int ,  HashBytesStackInstr )
 // -------------------------------------------------------------------------------
    rule <instrs> #hashMemory(DATAOFFSET, LENGTH, RESULTOFFSET, HASHINSTR)
               => #memLoad(DATAOFFSET, LENGTH)
               ~> HASHINSTR
               ~> #memStoreFromBytesStack(RESULTOFFSET)
               ~> #dropBytes
               ~> i32.const 0
               ...
          </instrs>
```

#### Log

```k
    syntax LogEntry ::= logEntry ( Bytes , Bytes , List , Bytes ) [klabel(logEntry), symbol]
 // ----------------------------------------------------------------------------------------

    syntax InternalInstr ::= #getArgsFromMemory    ( Int , Int , Int )
                           | #getArgsFromMemoryAux ( Int , Int , Int , Int , Int )
 // ------------------------------------------------------------------------------
    rule <instrs> #getArgsFromMemory(NUMARGS, LENGTHOFFSET, DATAOFFSET)
               => #getArgsFromMemoryAux(NUMARGS, 0, NUMARGS, LENGTHOFFSET, DATAOFFSET)
                  ...
         </instrs>

    rule <instrs> #getArgsFromMemoryAux(NUMARGS, TOTALLEN, 0,  _, _)
               => i32.const TOTALLEN
               ~> i32.const NUMARGS
                  ...
         </instrs>

    rule <instrs> #getArgsFromMemoryAux(NUMARGS, TOTALLEN, COUNTER, LENGTHOFFSET, DATAOFFSET)
               => #memLoad(LENGTHOFFSET, 4)
               ~> #loadArgDataWithLengthOnStack(NUMARGS, TOTALLEN, COUNTER, LENGTHOFFSET, DATAOFFSET)
                  ...
         </instrs>
       requires 0 <Int COUNTER

    syntax InternalInstr ::= #loadArgDataWithLengthOnStack( Int , Int , Int , Int , Int )
                           | #loadArgData                 ( Int , Int , Int , Int , Int , Int )
 // -------------------------------------------------------------------------------------------
    rule <instrs> #loadArgDataWithLengthOnStack(NUMARGS, TOTALLEN, COUNTER, LENGTHOFFSET, DATAOFFSET)
               => #loadArgData(Bytes2Int(ARGLEN, LE, Unsigned), NUMARGS, TOTALLEN, COUNTER, LENGTHOFFSET, DATAOFFSET)
                  ...
         </instrs>
         <bytesStack> ARGLEN : STACK => STACK </bytesStack>


    rule <instrs> #loadArgData(ARGLEN, NUMARGS, TOTALLEN, COUNTER, LENGTHOFFSET, DATAOFFSET)
               => #memLoad(DATAOFFSET, ARGLEN)
               ~> #getArgsFromMemoryAux(NUMARGS, TOTALLEN +Int ARGLEN, COUNTER -Int 1, LENGTHOFFSET +Int 4, DATAOFFSET +Int ARGLEN)
                  ...
         </instrs>

    syntax InternalInstr ::= "#writeLog"
                           | #writeLogAux ( Int , List , Bytes )
 // ------------------------------------------------------------
    rule <instrs> #writeLog => #writeLogAux(NUMTOPICS, .List, DATA) ... </instrs>
         <bytesStack> DATA : STACK => STACK </bytesStack>
         <valstack> <i32> NUMTOPICS : <i32> _ : VALSTACK => VALSTACK </valstack>

    rule <instrs> #writeLogAux(1, TOPICS, DATA) => . ... </instrs>
         <bytesStack> IDENTIFIER : STACK => STACK </bytesStack>
         <callee> CALLEE </callee>
         <logs> ... (.List => ListItem(logEntry(CALLEE, IDENTIFIER, TOPICS, DATA))) </logs>

    rule <instrs> #writeLogAux(NUMTOPICS, TOPICS, DATA)
               => #writeLogAux(NUMTOPICS -Int 1, ListItem(TOPIC) TOPICS, DATA)
                  ...
         </instrs>
         <bytesStack> TOPIC : STACK => STACK </bytesStack>
       requires 1 <Int NUMTOPICS
```

### Elrond API

```k
    // extern void getSCAddress(void *context, int32_t resultOffset);
    rule <instrs> hostCall("env", "getSCAddress", [ i32  .ValTypes ] -> [ .ValTypes ])
               => #memStore(RESULTOFFSET, CALLEE)
                  ...
         </instrs>
         <locals>
           0 |-> <i32> RESULTOFFSET
         </locals>
         <callee> CALLEE </callee>

    // extern int32_t isSmartContract(void *context, int32_t addressOffset);
    rule <instrs> hostCall("env", "isSmartContract", [ i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #memLoad(ADDROFFSET, 32)
               ~> #checkIsSmartContract
                  ...
         </instrs>
         <locals>
           0 |-> <i32> ADDROFFSET
         </locals>

    syntax InternalInstr ::= "#checkIsSmartContract"
 // ------------------------------------------------
    rule <instrs> #checkIsSmartContract => i32.const 1 ... </instrs>
         <bytesStack> ADDR : STACK => STACK </bytesStack>
         <account>
           <address> ADDR </address>
           <codeIdx> _:Int </codeIdx>
           ...
         </account>

    rule <instrs> #checkIsSmartContract => i32.const 0 ... </instrs>
         <bytesStack> ADDR : STACK => STACK </bytesStack>
         <account>
           <address> ADDR </address>
           <codeIdx> .CodeIndex </codeIdx>
           ...
         </account>

    // extern void getExternalBalance(void *context, int32_t addressOffset, int32_t resultOffset);
    rule <instrs> hostCall("env", "getExternalBalance", [ i32 i32 .ValTypes ] -> [ .ValTypes ])
               => #memLoad(ADDROFFSET, 32)
               ~> #getExternalBalance
               ~> #memStoreFromBytesStack(RESULTOFFSET)
               ~> #dropBytes
                  ...
         </instrs>
         <locals>
           0 |-> <i32> ADDROFFSET
           1 |-> <i32> RESULTOFFSET
         </locals>

    syntax InternalInstr ::= "#getExternalBalance"
 // ----------------------------------------------
    rule <instrs> #getExternalBalance => . ... </instrs>
         <bytesStack> ADDR : STACK => Int2Bytes(BAL, BE, Unsigned) : STACK </bytesStack>
         <account>
           <address> ADDR </address>
           <balance> BAL </balance>
           ...
         </account>

    // extern int32_t transferValue(void *context, int32_t dstOffset, int32_t valueOffset, int32_t dataOffset, int32_t length);
    rule <instrs> hostCall("env", "transferValue", [ i32 i32 i32 i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #memLoad(DSTOFFSET, 32)
               ~> #memLoad(VALUEOFFSET, 32)
               ~> #memLoad(DATAOFFSET, LENGTH)
               ~> #transferValue
                  ...
         </instrs>
         <locals>
           0 |-> <i32> DSTOFFSET
           1 |-> <i32> VALUEOFFSET
           2 |-> <i32> DATAOFFSET
           3 |-> <i32> LENGTH
         </locals>

    syntax InternalInstr ::= "#transferValue"
                           | "#waitForTransfer"
 // -------------------------------------------
    rule <commands> (. => transferFunds(CALLEE, DEST, Bytes2Int(VALUE, BE, Unsigned))) ... </commands>
         <instrs> #transferValue => #waitForTransfer ~> i32.const 0 ... </instrs>
         <callee> CALLEE </callee>
         <bytesStack> _DATA : VALUE : DEST : STACK => STACK </bytesStack>

    rule <commands> #transferSuccess => . ... </commands>
         <instrs> #waitForTransfer => . ... </instrs>

    // extern int32_t getArgumentLength(void *context, int32_t id);
    rule <instrs> hostCall("env", "getArgumentLength", [ i32 .ValTypes ] -> [ i32 .ValTypes ]) => i32.const lengthBytes({ARGS[IDX]}:>Bytes) ... </instrs>
         <locals> 0 |-> <i32> IDX </locals>
         <callArgs> ARGS </callArgs>
      requires IDX <Int size(ARGS)

    // extern int32_t getArgument(void *context, int32_t id, int32_t argOffset);
    rule <instrs> hostCall("env", "getArgument", [ i32 i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #memStore(OFFSET, {ARGS[IDX]}:>Bytes)
               ~> i32.const lengthBytes({ARGS[IDX]}:>Bytes)
                  ...
         </instrs>
         <locals>
           0 |-> <i32> IDX
           1 |-> <i32> OFFSET
         </locals>
         <callArgs> ARGS </callArgs>

    // extern int32_t getNumArguments(void *context);
    rule <instrs> hostCall("env", "getNumArguments", [ .ValTypes ] -> [ i32 .ValTypes ]) => i32.const size(ARGS) ... </instrs>
         <callArgs> ARGS </callArgs>

    // extern int32_t storageStore(void *context, int32_t keyOffset, int32_t keyLength , int32_t dataOffset, int32_t dataLength);
    rule <instrs> hostCall("env", "storageStore", [ i32 i32 i32 i32 .ValTypes ] -> [ i32 .ValTypes ] )
               => #memLoad(KEYOFFSET, KEYLENGTH)
               ~> #memLoad(VALOFFSET, VALLENGTH)
               ~> #storageStore
                  ...
         </instrs>
         <locals>
           0 |-> <i32> KEYOFFSET
           1 |-> <i32> KEYLENGTH
           2 |-> <i32> VALOFFSET
           3 |-> <i32> VALLENGTH
         </locals>

    // extern int32_t storageLoadLength(void *context, int32_t keyOffset, int32_t keyLength );
    rule <instrs> hostCall("env", "storageLoadLength", [ i32 i32 .ValTypes ] -> [ i32 .ValTypes ] )
               => #memLoad(KEYOFFSET, KEYLENGTH)
               ~> #storageLoad
               ~> #returnLength
               ~> #dropBytes
                  ...
         </instrs>
         <locals>
           0 |-> <i32> KEYOFFSET
           1 |-> <i32> KEYLENGTH
         </locals>

    // extern int32_t storageLoad(void *context, int32_t keyOffset, int32_t keyLength , int32_t dataOffset);
    rule <instrs> hostCall("env", "storageLoad", [ i32 i32 i32 .ValTypes ] -> [ i32 .ValTypes ] )
               => #memLoad(KEYOFFSET, KEYLENGTH)
               ~> #storageLoad
               ~> #memStoreFromBytesStack(VALOFFSET)
               ~> #returnLength
               ~> #dropBytes
                  ...
         </instrs>
         <locals>
           0 |-> <i32> KEYOFFSET
           1 |-> <i32> KEYLENGTH
           2 |-> <i32> VALOFFSET
         </locals>

    // extern void getCaller(void *context, int32_t resultOffset);
    rule <instrs> hostCall("env", "getCaller", [ i32 .ValTypes ] -> [ .ValTypes ])
               => #memStore(OFFSET, CALLER)
                  ...
         </instrs>
         <locals> 0 |-> <i32> OFFSET </locals>
         <caller> CALLER </caller>

    // extern void checkNoPayment(void *context);
    rule <instrs> hostCall("env", "checkNoPayment", [ .ValTypes ] -> [ .ValTypes ]) => . ... </instrs>
         <callValue> 0 </callValue>
         <esdtValue> 0 </esdtValue>

    // extern int32_t getESDTTokenName(void *context, int32_t resultOffset);
    rule <instrs> hostCall("env", "getESDTTokenName", [ i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #memStore(OFFSET, TOKENNAME)
               ~> i32.const lengthBytes(TOKENNAME)
                  ...
         </instrs>
         <locals> 0 |-> <i32> OFFSET </locals>
         <esdtTokenName> TOKENNAME </esdtTokenName>

    // extern void writeEventLog(void *context, int32_t numTopics, int32_t topicLengthsOffset, int32_t topicOffset, int32_t dataOffset, int32_t dataLength);
    rule <instrs> hostCall("env", "writeEventLog", [ i32 i32 i32 i32 i32 .ValTypes ] -> [ .ValTypes ])
               => #getArgsFromMemory(NUMTOPICS, TOPICLENGTHOFFSET, TOPICOFFSET)
               ~> #memLoad(DATAOFFSET, DATALENGTH)
               ~> #writeLog
                  ...
         </instrs>
         <locals>
           0 |-> <i32> NUMTOPICS
           1 |-> <i32> TOPICLENGTHOFFSET
           2 |-> <i32> TOPICOFFSET
           3 |-> <i32> DATAOFFSET
           4 |-> <i32> DATALENGTH
         </locals>

    // extern void returnData(void* context, int32_t dataOffset, int32_t length);
    rule <instrs> hostCall("env", "finish", [ i32 i32 .ValTypes ] -> [ .ValTypes ])
               => #returnData(OFFSET, LENGTH)
                  ...
         </instrs>
         <locals>
           0 |-> <i32> OFFSET
           1 |-> <i32> LENGTH
         </locals>

    syntax InternalInstr ::= #returnData ( Int, Int )
 // -------------------------------------------------
    rule <instrs> #returnData(OFFSET, LENGTH)
               => #memLoad(OFFSET, LENGTH)
               ~> #appendToOutFromBytesStack
                  ...
         </instrs>

    // extern void signalError(void* context, int32_t messageOffset, int32_t messageLength);
    rule <instrs> hostCall("env", "signalError", [ i32 i32 .ValTypes ] -> [ .ValTypes ] )
               => #memLoad(OFFSET, LENGTH)
               ~> #signalError
                  ...
         </instrs>
         <locals>
           0 |-> <i32> OFFSET
           1 |-> <i32> LENGTH
         </locals>

    syntax InternalInstr ::= "#signalError"
 // ---------------------------------------
    rule <commands> (. => #exception(UserError)) ... </commands>
         <instrs> (#signalError ~> _) => . </instrs>
         <bytesStack> DATA : STACK => STACK </bytesStack>
         <message> MSG => MSG +Bytes DATA </message>

    // extern long long getBlockTimestamp(void *context);
    rule <instrs> hostCall("env", "getBlockTimestamp", [ .ValTypes ] -> [ i64 .ValTypes ]) => i64.const TIMESTAMP ... </instrs>
         <curBlockTimestamp> TIMESTAMP </curBlockTimestamp>

    // extern long long getBlockNonce(void *context);
    rule <instrs> hostCall("env", "getBlockNonce", [ .ValTypes ] -> [ i64 .ValTypes ]) => i64.const NONCE ... </instrs>
         <curBlockNonce> NONCE </curBlockNonce>

    // extern long long getBlockRound(void *context);
    rule <instrs> hostCall("env", "getBlockRound", [ .ValTypes ] -> [ i64 .ValTypes ]) => i64.const ROUND ... </instrs>
         <curBlockRound> ROUND </curBlockRound>

    // extern long long getBlockEpoch(void *context);
    rule <instrs> hostCall("env", "getBlockEpoch", [ .ValTypes ] -> [ i64 .ValTypes ]) => i64.const EPOCH ... </instrs>
         <curBlockEpoch> EPOCH </curBlockEpoch>

    // extern void getBlockRandomSeed(void *context, int32_t resultOffset);
    rule <instrs> hostCall("env", "getBlockRandomSeed", [ i32 .ValTypes ] -> [ .ValTypes ])
               => #memStore(OFFSET, SEED)
                  ...
         </instrs>
         <locals> 0 |-> <i32> OFFSET </locals>
         <curBlockRandomSeed> SEED </curBlockRandomSeed>

    // extern long long getPrevBlockTimestamp(void *context);
    rule <instrs> hostCall("env", "getPrevBlockTimestamp", [ .ValTypes ] -> [ i64 .ValTypes ]) => i64.const TIMESTAMP ... </instrs>
         <prevBlockTimestamp> TIMESTAMP </prevBlockTimestamp>

    // extern long long getPrevBlockNonce(void *context);
    rule <instrs> hostCall("env", "getPrevBlockNonce", [ .ValTypes ] -> [ i64 .ValTypes ]) => i64.const NONCE ... </instrs>
         <prevBlockNonce> NONCE </prevBlockNonce>

    // extern long long getPrevBlockRound(void *context);
    rule <instrs> hostCall("env", "getPrevBlockRound", [ .ValTypes ] -> [ i64 .ValTypes ]) => i64.const ROUND ... </instrs>
         <prevBlockRound> ROUND </prevBlockRound>

    // extern long long getPrevBlockEpoch(void *context);
    rule <instrs> hostCall("env", "getPrevBlockEpoch", [ .ValTypes ] -> [ i64 .ValTypes ]) => i64.const EPOCH ... </instrs>
         <prevBlockEpoch> EPOCH </prevBlockEpoch>

    // extern void getPrevBlockRandomSeed(void *context, int32_t resultOffset);
    rule <instrs> hostCall("env", "getPrevBlockRandomSeed", [ i32 .ValTypes ] -> [ .ValTypes ])
               => #memStore(OFFSET, SEED)
                  ...
         </instrs>
         <locals> 0 |-> <i32> OFFSET </locals>
         <prevBlockRandomSeed> SEED </prevBlockRandomSeed>
```

### BigInt Ops

```k
    syntax InternalInstr ::= #getBigInt ( idx : Int ,  Signedness )
 // ---------------------------------------------------------------
    rule <instrs> #getBigInt(BIGINT_IDX, SIGN) => . ... </instrs>
         <bytesStack> STACK => Int2Bytes({HEAP[BIGINT_IDX]}:>Int, BE, SIGN) : STACK </bytesStack>
         <bigIntHeap> HEAP </bigIntHeap>

    syntax InternalInstr ::= #setBigIntFromBytesStack ( idx: Int , Signedness )
                           | #setBigInt ( idx: Int , value: Bytes , Signedness )
 // ----------------------------------------------------------------------------
    rule <instrs> #setBigIntFromBytesStack(BIGINT_IDX, SIGN) => #setBigInt(BIGINT_IDX, BS, SIGN) ... </instrs>
         <bytesStack> BS : _ </bytesStack>

    rule <instrs> #setBigInt(BIGINT_IDX, BS, SIGN) => . ... </instrs>
         <bigIntHeap> HEAP => HEAP [BIGINT_IDX <- Bytes2Int(BS, BE, SIGN)] </bigIntHeap>
```

```k
    // extern int32_t bigIntNew(void* context, long long smallValue);
    rule <instrs> hostCall("env", "bigIntNew", [ i64 .ValTypes ] -> [ i32 .ValTypes ]) => i32.const size(HEAP) ... </instrs>
         <locals> 0 |-> <i64> INITIAL </locals>
         <bigIntHeap> HEAP => HEAP[size(HEAP) <- INITIAL] </bigIntHeap>

    // extern int32_t bigIntUnsignedByteLength(void* context, int32_t reference);
    rule <instrs> hostCall("env", "bigIntUnsignedByteLength", [ i32 .ValTypes ] -> [ i32 .ValTypes ]) => i32.const lengthBytes(Int2Bytes({HEAP[IDX]}:>Int, BE, Unsigned)) ... </instrs>
         <locals> 0 |-> <i32> IDX </locals>
         <bigIntHeap> HEAP </bigIntHeap>

    // extern int32_t bigIntSignedByteLength(void* context, int32_t reference);
    rule <instrs> hostCall("env", "bigIntSignedByteLength", [ i32 .ValTypes ] -> [ i32 .ValTypes ]) => i32.const lengthBytes(Int2Bytes({HEAP[IDX]}:>Int, BE, Signed)) ... </instrs>
         <locals> 0 |-> <i32> IDX </locals>
         <bigIntHeap> HEAP </bigIntHeap>

    // extern int32_t bigIntGetUnsignedBytes(void* context, int32_t reference, int32_t byteOffset);
    rule <instrs> hostCall("env", "bigIntGetUnsignedBytes", [ i32 i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #getBigInt(IDX, Unsigned)
               ~> #memStoreFromBytesStack(OFFSET)
               ~> #returnLength
               ~> #dropBytes
                  ...
         </instrs>
         <locals> 0 |-> <i32> IDX  1 |-> <i32> OFFSET </locals>

    // extern int32_t bigIntGetSignedBytes(void* context, int32_t reference, int32_t byteOffset);
    rule <instrs> hostCall("env", "bigIntGetSignedBytes", [ i32 i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #getBigInt(IDX, Signed)
               ~> #memStoreFromBytesStack(OFFSET)
               ~> #returnLength
               ~> #dropBytes
                  ...
         </instrs>
         <locals> 0 |-> <i32> IDX  1 |-> <i32> OFFSET </locals>

    // extern void bigIntSetUnsignedBytes(void* context, int32_t destination, int32_t byteOffset, int32_t byteLength);
    rule <instrs> hostCall("env", "bigIntSetUnsignedBytes", [ i32 i32 i32 .ValTypes ] -> [ .ValTypes ])
               => #memLoad(OFFSET, LENGTH)
               ~> #setBigIntFromBytesStack(IDX, Unsigned)
               ~> #dropBytes
                  ...
         </instrs>
         <locals> 0 |-> <i32> IDX 1 |-> <i32> OFFSET 2 |-> <i32> LENGTH </locals>

    // extern void bigIntSetSignedBytes(void* context, int32_t destination, int32_t byteOffset, int32_t byteLength);
    rule <instrs> hostCall("env", "bigIntSetSignedBytes", [ i32 i32 i32 .ValTypes ] -> [ .ValTypes ])
               => #memLoad(OFFSET, LENGTH)
               ~> #setBigIntFromBytesStack(IDX, Signed)
               ~> #dropBytes
                  ...
         </instrs>
         <locals> 0 |-> <i32> IDX 1 |-> <i32> OFFSET 2 |-> <i32> LENGTH </locals>

    // extern void bigIntAdd(void* context, int32_t destination, int32_t op1, int32_t op2);
    rule <instrs> hostCall("env", "bigIntAdd", [ i32 i32 i32 .ValTypes ] -> [ .ValTypes ]) => . ... </instrs>
         <locals> 0 |-> <i32> DST  1 |-> <i32> OP1_IDX  2 |-> <i32> OP2_IDX </locals>
         <bigIntHeap> HEAP => HEAP [DST <- {HEAP[OP1_IDX]}:>Int +Int {HEAP[OP2_IDX]}:>Int] </bigIntHeap>

    // extern void bigIntSub(void* context, int32_t destination, int32_t op1, int32_t op2);
    rule <instrs> hostCall("env", "bigIntSub", [ i32 i32 i32 .ValTypes ] -> [ .ValTypes ]) => . ... </instrs>
         <locals> 0 |-> <i32> DST  1 |-> <i32> OP1_IDX  2 |-> <i32> OP2_IDX </locals>
         <bigIntHeap> HEAP => HEAP [DST <- {HEAP[OP1_IDX]}:>Int -Int {HEAP[OP2_IDX]}:>Int] </bigIntHeap>

    // extern void bigIntMul(void* context, int32_t destination, int32_t op1, int32_t op2);
    rule <instrs> hostCall("env", "bigIntMul", [ i32 i32 i32 .ValTypes ] -> [ .ValTypes ]) => . ... </instrs>
         <locals> 0 |-> <i32> DST  1 |-> <i32> OP1_IDX  2 |-> <i32> OP2_IDX </locals>
         <bigIntHeap> HEAP => HEAP [DST <- {HEAP[OP1_IDX]}:>Int *Int {HEAP[OP2_IDX]}:>Int] </bigIntHeap>

    // extern void bigIntTDiv(void* context, int32_t destination, int32_t op1, int32_t op2);
    rule <instrs> hostCall("env", "bigIntTDiv", [ i32 i32 i32 .ValTypes ] -> [ .ValTypes ]) => . ... </instrs>
         <locals> 0 |-> <i32> DST  1 |-> <i32> OP1_IDX  2 |-> <i32> OP2_IDX </locals>
         <bigIntHeap> HEAP => HEAP [DST <- {HEAP[OP1_IDX]}:>Int /Int {HEAP[OP2_IDX]}:>Int] </bigIntHeap>

    // extern int32_t bigIntSign(void* context, int32_t op);
    rule <instrs> hostCall("env", "bigIntSign", [ i32 .ValTypes ] -> [ i32 .ValTypes ])
               => i32.const #bigIntSign({HEAP[IDX]}:>Int)
                  ...
         </instrs>
         <locals> 0 |-> <i32> IDX </locals>
         <bigIntHeap> HEAP </bigIntHeap>

    // extern int32_t bigIntCmp(void* context, int32_t op1, int32_t op2);
    rule <instrs> hostCall("env", "bigIntCmp", [ i32 i32 .ValTypes ] -> [ i32 .ValTypes ])
               => i32.const #cmpInt({HEAP[IDX1]}:>Int, {HEAP[IDX2]}:>Int)
                  ...
         </instrs>
         <locals> 0 |-> <i32> IDX1  1 |-> <i32> IDX2 </locals>
         <bigIntHeap> HEAP </bigIntHeap>

    // extern void bigIntFinishUnsigned(void* context, int32_t reference);
    rule <instrs> hostCall("env", "bigIntFinishUnsigned", [ i32 .ValTypes ] -> [ .ValTypes ])
               => #getBigInt(IDX, Unsigned)
               ~> #appendToOutFromBytesStack
                  ...
         </instrs>
         <locals> 0 |-> <i32> IDX </locals>

    // extern void bigIntFinishSigned(void* context, int32_t reference);
    rule <instrs> hostCall("env", "bigIntFinishSigned", [ i32 .ValTypes ] -> [ .ValTypes ])
               => #getBigInt(IDX, Signed)
               ~> #appendToOutFromBytesStack
                  ...
         </instrs>
         <locals> 0 |-> <i32> IDX </locals>

    // extern int32_t bigIntStorageStoreUnsigned(void *context, int32_t keyOffset, int32_t keyLength, int32_t source);
    rule <instrs> hostCall("env", "bigIntStorageStoreUnsigned", [ i32 i32 i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #memLoad(KEYOFFSET, KEYLENGTH)
               ~> #getBigInt(BIGINTIDX, Unsigned)
               ~> #storageStore
                  ...
         </instrs>
         <locals>
           0 |-> <i32> KEYOFFSET
           1 |-> <i32> KEYLENGTH
           2 |-> <i32> BIGINTIDX
         </locals>

    // extern int32_t bigIntStorageLoadUnsigned(void *context, int32_t keyOffset, int32_t keyLength, int32_t destination);
    rule <instrs> hostCall("env", "bigIntStorageLoadUnsigned", [ i32 i32 i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #memLoad(KEYOFFSET, KEYLENGTH)
               ~> #storageLoad
               ~> #setBigIntFromBytesStack(DEST, Unsigned)
               ~> #returnLength
               ~> #dropBytes
                  ...
         </instrs>
         <locals>
           0 |-> <i32> KEYOFFSET
           1 |-> <i32> KEYLENGTH
           2 |-> <i32> DEST
         </locals>

    // extern void bigIntGetUnsignedArgument(void *context, int32_t id, int32_t destination);
    rule <instrs> hostCall("env", "bigIntGetUnsignedArgument", [ i32 i32 .ValTypes ] -> [ .ValTypes ]) =>  . ... </instrs>
         <locals> 0 |-> <i32> ARG_IDX  1 |-> <i32> BIG_IDX </locals>
         <callArgs> ARGS </callArgs>
         <bigIntHeap> HEAP => HEAP [BIG_IDX <- Bytes2Int({ARGS[ARG_IDX]}:>Bytes, BE, Unsigned)] </bigIntHeap>

    // extern void bigIntGetSignedArgument(void *context, int32_t id, int32_t destination);
    rule <instrs> hostCall("env", "bigIntGetSignedArgument", [ i32 i32 .ValTypes ] -> [ .ValTypes ]) =>  . ... </instrs>
         <locals> 0 |-> <i32> ARG_IDX  1 |-> <i32> BIG_IDX </locals>
         <callArgs> ARGS </callArgs>
         <bigIntHeap> HEAP => HEAP [BIG_IDX <- Bytes2Int({ARGS[ARG_IDX]}:>Bytes, BE, Signed)] </bigIntHeap>

    // extern void bigIntGetCallValue(void *context, int32_t destination);
    rule <instrs> hostCall("env", "bigIntGetCallValue", [ i32 .ValTypes ] -> [ .ValTypes ]) => . ... </instrs>
         <locals> 0 |-> <i32> IDX </locals>
         <bigIntHeap> HEAP => HEAP[IDX <- VALUE] </bigIntHeap>
         <callValue> VALUE </callValue>

    // extern void bigIntGetExternalBalance(void *context, int32_t addressOffset, int32_t result);
    rule <instrs> hostCall("env", "bigIntGetExternalBalance", [ i32 i32 .ValTypes ] -> [ .ValTypes ])
               => #memLoad(ADDROFFSET, 32)
               ~> #getExternalBalance
               ~> #setBigIntFromBytesStack(RESULT, Unsigned)
               ~> #dropBytes
                  ...
         </instrs>
         <locals>
           0 |-> <i32> ADDROFFSET
           1 |-> <i32> RESULT
         </locals>
```

### SmallInt Ops

```k
    // extern long long smallIntGetUnsignedArgument(void *context, int32_t id);
    rule <instrs> hostCall("env", "smallIntGetUnsignedArgument", [ i32 .ValTypes ] -> [ i64 .ValTypes ])
               => #returnIfUInt64(Bytes2Int({ARGS[ARG_IDX]}:>Bytes, BE, Unsigned), "argument out of range") ... </instrs>
         <locals> 0 |-> <i32> ARG_IDX </locals>
         <callArgs> ARGS </callArgs>

    // extern long long smallIntGetSignedArgument(void *context, int32_t id);
    rule <instrs> hostCall("env", "smallIntGetSignedArgument", [ i32 .ValTypes ] -> [ i64 .ValTypes ])
               => #returnIfSInt64(Bytes2Int({ARGS[ARG_IDX]}:>Bytes, BE, Signed), "argument out of range") ... </instrs>
         <locals> 0 |-> <i32> ARG_IDX </locals>
         <callArgs> ARGS </callArgs>

    // extern void smallIntFinishUnsigned(void* context, long long value);
    rule <instrs> hostCall("env", "smallIntFinishUnsigned", [ i64 .ValTypes ] -> [ .ValTypes ])
               => #appendToOut(Int2Bytes(#unsigned(i64, VALUE), BE, Unsigned))
                  ...
         </instrs>
         <locals> 0 |-> <i64> VALUE </locals>

    // extern void smallIntFinishSigned(void* context, long long value);
    rule <instrs> hostCall("env", "smallIntFinishSigned", [ i64 .ValTypes ] -> [ .ValTypes ])
               => #appendToOut(Int2Bytes(#signed(i64, VALUE), BE, Signed))
                  ...
         </instrs>
         <locals> 0 |-> <i64> VALUE </locals>

    // extern int32_t smallIntStorageStoreUnsigned(void *context, int32_t keyOffset, int32_t keyLength, long long value);
    rule <instrs> hostCall("env", "smallIntStorageStoreUnsigned", [ i32 i32 i64 .ValTypes ] -> [ i32 .ValTypes ])
               => #memLoad(KEYOFFSET, KEYLEN)
               ~> #pushBytes(Int2Bytes(VALUE, BE, Unsigned))
               ~> #storageStore
                  ...
         </instrs>
         <locals>
           0 |-> <i32> KEYOFFSET
           1 |-> <i32> KEYLEN
           2 |-> <i64> VALUE
         </locals>

    // extern int32_t smallIntStorageStoreSigned(void *context, int32_t keyOffset, int32_t keyLength, long long value);
    rule <instrs> hostCall("env", "smallIntStorageStoreSigned", [ i32 i32 i64 .ValTypes ] -> [ i32 .ValTypes ])
               => #memLoad(KEYOFFSET, KEYLEN)
               ~> #pushBytes(Int2Bytes(VALUE, BE, Signed))
               ~> #storageStore
                  ...
         </instrs>
         <locals>
           0 |-> <i32> KEYOFFSET
           1 |-> <i32> KEYLEN
           2 |-> <i64> VALUE
         </locals>

    // extern long long smallIntStorageLoadUnsigned(void *context, int32_t keyOffset, int32_t keyLength);
    rule <instrs> hostCall("env", "smallIntStorageLoadUnsigned", [ i32 i32 .ValTypes ] -> [ i64 .ValTypes ])
               => #memLoad(KEYOFFSET, KEYLENGTH)
               ~> #storageLoad
               ~> #loadBytesAsUInt64("storage value out of range")
                  ...
         </instrs>
         <locals>
           0 |-> <i32> KEYOFFSET
           1 |-> <i32> KEYLENGTH
         </locals>

    // extern long long smallIntStorageLoadSigned(void *context, int32_t keyOffset, int32_t keyLength);
    rule <instrs> hostCall("env", "smallIntStorageLoadSigned", [ i32 i32 .ValTypes ] -> [ i64 .ValTypes ])
               => #memLoad(KEYOFFSET, KEYLENGTH)
               ~> #storageLoad
               ~> #loadBytesAsSInt64("storage value out of range")
                  ...
         </instrs>
         <locals>
           0 |-> <i32> KEYOFFSET
           1 |-> <i32> KEYLENGTH
         </locals>
```

### Crypto API

```k
    // extern int32_t sha256(void* context, int32_t dataOffset, int32_t length, int32_t resultOffset);
    rule <instrs> hostCall("env", "sha256", [ i32 i32 i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #hashMemory(DATAOFFSET, LENGTH, RESULTOFFSET, #sha256FromBytesStack)
                  ...
         </instrs>
         <locals>
           0 |-> <i32> DATAOFFSET
           1 |-> <i32> LENGTH
           2 |-> <i32> RESULTOFFSET
         </locals>

    // extern int32_t keccak256(void *context, int32_t dataOffset, int32_t length, int32_t resultOffset);
    rule <instrs> hostCall("env", "keccak256", [ i32 i32 i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #hashMemory(DATAOFFSET, LENGTH, RESULTOFFSET, #keccakFromBytesStack)
                  ...
         </instrs>
         <locals>
           0 |-> <i32> DATAOFFSET
           1 |-> <i32> LENGTH
           2 |-> <i32> RESULTOFFSET
         </locals>
```

### Other Host Calls

The (incorrect) default implementation of a host call is to just return zero values of the correct type.

```k
    rule <instrs> hostCall("env", "asyncCall", [ DOM ] -> [ CODOM ]) => . ... </instrs>
         <valstack> VS => #zero(CODOM) ++ #drop(lengthValTypes(DOM), VS) </valstack>

endmodule
```
