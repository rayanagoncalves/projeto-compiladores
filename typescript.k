module TYPESCRIPT-SYNTAX 
    import DOMAINS

    syntax Block ::= Stmt 

    syntax Stmt ::= AExp
                |  Stmt Stmt [left]
                | DecVar
                | Assigner
                | AExpMod

    syntax AExp ::= Int 
                | AExp "+" AExp 
                | AExp "-" AExp 
                | AExp "*" AExp 
                | AExp "/" AExp 

    syntax AExpMod ::= Id "++"
                    | Id "--"

    syntax DecVar ::= Id ":" Type

    syntax Type ::= "number" 
                
    syntax Assigner ::= Id "=" AExp [strict(2)]
                        | DecVar "=" AExp [strict(2)]

    syntax Skip ::= "Skip"

    rule I1:Int + I2:Int => I1 +Int I2
    rule I1:Int - I2:Int => I1 -Int I2
    rule I1:Int * I2:Int => I1 *Int I2
    rule I1:Int / I2:Int => I1 /Int I2

    rule S1:Stmt S2:Stmt => S1 ~> S2
    
    rule <k> I:Id : number => Skip ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> 0 </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> I:Id = V:Int => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (_ => V) ... </store>

    rule <k> I:Id => V ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> V ... </store>

    rule <k>I:Id : number = V:Int => Skip ...</k>
        <env> MEnv:Map => MEnv I |-> L </env> 
        <store> MStore:Map => MStore L |-> V</store> 
        <loc> L:Int => L +Int 1</loc> 

    rule <k>I:Id ++ => Skip ...</k>
        <env> ... I |-> L ... </env> 
        <store> ... L |-> (V => V +Int 1) ... </store> 

    rule <k>I:Id -- => Skip ...</k>
        <env> ... I |-> L ... </env> 
        <store> ... L |-> (V => V -Int 1) ... </store> 

    rule Skip => .

    configuration <T>
        <k> $PGM:Block </k>
        <env> .Map </env>
        <store> .Map </store>
        <loc> 1 </loc>
    </T>

endmodule

module TYPESCRIPT
    import DOMAINS
    import TYPESCRIPT-SYNTAX

    syntax KResult ::= Int | Bool
    syntax KVariable ::= Id
endmodule