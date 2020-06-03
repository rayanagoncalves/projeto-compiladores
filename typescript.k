module TYPESCRIPT-SYNTAX 
    import DOMAINS

    syntax Block ::= Stmt                 

    syntax Stmt ::= AExp
                | Stmt Stmt [left]
                | DecVar
                | Assigner
                | AExpMod
                | BExp
                | SExp
                | "if" "(" BExp ")" "{" Block "}" [strict(1)]
                | "if" "(" BExp ")" "{" Block "}" ElseIfStmt [strict(1)]
                | BExp "?" Block ":" Block [strict(1)]
                | "while" "(" BExp ")" "{" Block "}"
                | "do" "{" Block "}" "while" "(" BExp ")" 
                | "for" "(" DecVar "=" AExp ";" BExp ";" AExpMod ")" "{" Block "}"
                | Skip
                | FuncDec
                | FuncCall
                | Array
                | Foreach
                | Print
                | Return


    // SINTAXES PARA FUNÇÕES //
    syntax TypesVal ::= Int | String | Bool
    syntax Params ::= List{Id, ","} 
    syntax FuncDec ::= "function" Id "(" Params ")" "{" Stmt "}"
    syntax Values ::= List{TypesVal, ","}
    syntax FuncCall ::= Id "(" Values ")"
    syntax Local ::= "local" "(" Id "," Stmt ")" 
    syntax Return ::= "return" Id 
                    | "return" TypesVal

    // PRINT //
    syntax Print ::= "console.log" "(" TypesVal ")" 

    syntax AExp ::= Int 
                > left: AExp "/" AExp [seqstrict, left]
                > left: AExp "*" AExp [seqstrict, left]
                | Int "+" AExp [seqstrict, left]
                | AExp "-" AExp [seqstrict, left]
                | Id

    syntax SExp ::= String
                | String "+" SExp [seqstrict, left]
                | Id

    syntax ConcatOrSum ::= Id "+" Id 
        
    syntax BExp ::= Bool
                | AExp ">" AExp [strict]
                | AExp "<" AExp [strict]
                | AExp ">=" AExp [strict]
                | AExp "<=" AExp [strict]
                | AExp "==" AExp [strict]
                | Id
                | BExp "||" BExp [seqstrict]
                | BExp "&&" BExp [seqstrict]
                | "!" BExp [seqstrict, left]

    syntax AExpMod ::= Id "++"
                    | Id "--"

    syntax DecVar ::= Id ":" Type
                    | "var" Id
                    
 //   syntax DecIds ::= "var" Ids

    syntax Type ::= "number" 
                  | "boolean" 
                  | "string"
                
    syntax Assigner ::= DecVar "=" ConcatOrSum 
                        | Id "=" AExp [strict(2)]
                        | DecVar "=" AExp [strict(2)]
                        | Id "=" BExp [strict(2)]
                        | DecVar "=" BExp [strict(2)]
                        | Id "=" SExp [strict(2)]
                        | DecVar "=" SExp [strict(2)]
                        | Id "=" ConcatOrSum 

    syntax ElseIfStmt ::= "else if" "(" BExp ")" "{" Block "}"
                        | "else" "{" Block "}"
                        | "else if" "(" BExp ")" "{" Block "}" ElseIfStmt

//    syntax ListValues ::= List{Int, ","}
    
    // ARRAY
    syntax ListValues ::= List{TypesVal, ","}
    syntax Array ::= "[" ListValues "]"
    syntax Ids ::= List{Id, ","}
    syntax Foreach ::= "foreach" "(" Id "in" Array ")"  "{" Stmt "}"

    // skip
    syntax Skip ::= "Skip"

    rule Skip => .
    
    // OPERAÇÕES ARITMÉTICAS
    rule I1:Int + I2:Int => I1 +Int I2
    rule I1:Int - I2:Int => I1 -Int I2
    rule I1:Int * I2:Int => I1 *Int I2
    rule I1:Int / I2:Int => I1 /Int I2

     // OPERAÇÕES BOOLEANAS
    rule I1:Int < I2:Int => I1 <Int I2
    rule I1:Int > I2:Int => I1 >Int I2
    rule I1:Int <= I2:Int => I1 <=Int I2
    rule I1:Int >= I2:Int => I1 >=Int I2
    rule I1:Int == I2:Int => I1 ==Int I2

   // OU , E , NOT
    rule true || false => true 
    rule true || true => true 
    rule false || false => false 
    rule false || true => true 
    rule true && false => false 
    rule true && true => true 
    rule false && false => false 
    rule false && true => false 
    rule ! true => false
    rule ! false => true
    
    // ESTRUTURAS DE CONDIÇÃO
    rule if (true) { S:Stmt } => S
    rule if (false) { _ } => Skip
    rule if (true) { B } S:ElseIfStmt => B
    rule if (false) { _ } S:ElseIfStmt => S
    rule else if ( B:BExp ) { S1:Stmt } S2:ElseIfStmt => if ( B ) { S1 } S2
    rule else if ( B:BExp ) { S:Stmt } => if ( B ) { S }
    rule else { S } => S

    // IF TERNÁRIO
    rule true ? B:Block : _ => B 
    rule false ? _ : B:Block => B

    // ESTRUTURAS DE REPETIÇÃO
    rule while (B:BExp) { S:Stmt } => if(B){ S while (B) { S } } [structural]

    rule do { S:Stmt } while (B:BExp) => S ~> if(B){ do { S } while (B) } [structural]

    rule for (D:DecVar = V:AExp ; B:BExp ; Amod:AExpMod ) {S} 
        => D = V ~> while (B) { S Amod } [structural]

  //  rule .Ids : T:Type => Skip  
   // rule .Ids : T:Type = _:Int => Skip 

    rule S1:Stmt S2:Stmt => S1 ~> S2 [structural]
    rule local(I:Id, S1:Stmt S2:Stmt) => local(I, S1) ~> local(I, S2) [structural]

    // CONCATENAÇÃO DE STRING
    rule S1:String + S2:String => S1 +String S2
    

    // PEGANDO VALOR DA VARIÁVEL
    rule <k> I:Id => V ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> V ... </store>

    // VARIÁVEIS - INT
    rule <k> I:Id : number => Skip ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> 0 </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> I:Id = V:AExp => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (_ => V) ... </store>

    rule <k>I:Id : number = V:AExp => Skip ...</k>
        <env> MEnv:Map => MEnv I |-> L </env> 
        <store> MStore:Map => MStore L |-> V</store> 
        <loc> L:Int => L +Int 1</loc> 

    rule <k>I:Id ++ => Skip ...</k>
        <env> ... I |-> L ... </env> 
        <store> ... L |-> (V => V +Int 1) ... </store> 

    rule <k>I:Id -- => Skip ...</k>
        <env> ... I |-> L ... </env> 
        <store> ... L |-> (V => V -Int 1) ... </store> 

    rule <k> var I:Id => Skip ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> 0 </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> var I:Id = V:AExp => Skip ...</k>
        <env> MEnv:Map => MEnv I |-> L </env> 
        <store> MStore:Map => MStore L |-> V</store> 
        <loc> L:Int => L +Int 1</loc> 

    // VARIAVEIS - BOOL
    rule <k> var I:Id = V:BExp => Skip ...</k>
        <env> MEnv:Map => MEnv I |-> L </env> 
        <store> MStore:Map => MStore L |-> V</store> 
        <loc> L:Int => L +Int 1</loc>   

    rule <k>I:Id : boolean = V:BExp => Skip ...</k>
        <env> MEnv:Map => MEnv I |-> L </env> 
        <store> MStore:Map => MStore L |-> V</store> 
        <loc> L:Int => L +Int 1</loc> 

    rule <k> I:Id : boolean => Skip ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> false </store>
        <loc> L:Int => L +Int 1 </loc>
    
    rule <k> I:Id = V:BExp => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (_ => V) ... </store>

    // VARIAVEIS - STRING
    rule <k> I:Id : string => Skip ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> "" </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> var I:Id = V:SExp => Skip ...</k>
        <env> MEnv:Map => MEnv I |-> L </env> 
        <store> MStore:Map => MStore L |-> V</store> 
        <loc> L:Int => L +Int 1</loc>

    rule <k>I:Id : string = V:SExp => Skip ...</k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V</store>
        <loc> L:Int => L +Int 1</loc>

    rule <k> I:Id = V:SExp => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (_ => V) ... </store>

    // REGRA SOMAR IDS DIFERENTES - String  
    rule <k> var I:Id = I1:Id + I2:Id => var I = V1 + V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:String  
                L2 |-> V2:String ... 
        </store>   

    rule <k> I:Id = I1:Id + I2:Id =>  I = V1 + V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:String  
                L2 |-> V2:String ... 
        </store>   

    rule <k> I:Id : string = I1:Id + I2:Id =>  I : string = V1 + V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:String  
                L2 |-> V2:String ... 
        </store>    

   // REGRA SOMAR IDS DIFERENTES - INT
    rule <k> var I:Id = I1:Id + I2:Id => var I = V1 + V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:Int  
                L2 |-> V2:Int ... 
        </store>  
    
    rule <k> I:Id = I1:Id + I2:Id =>  I = V1 + V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:Int  
                L2 |-> V2:Int ... 
        </store>   

    rule <k> I:Id : number = I1:Id + I2:Id =>  I : number = V1 + V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:Int  
                L2 |-> V2:Int ... 
        </store>  
    

    // REGRA SUBTRAIR IDS DIFERENTES - INT 
    rule <k> var I:Id = I1:Id - I2:Id => var I = V1 - V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:Int  
                L2 |-> V2:Int ... 
        </store>  
    
    rule <k> I:Id = I1:Id - I2:Id =>  I = V1 - V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:Int  
                L2 |-> V2:Int ... 
        </store>   

    rule <k> I:Id : number = I1:Id - I2:Id =>  I : number = V1 - V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:Int  
                L2 |-> V2:Int ... 
        </store>  

    // REGRA MULTIPLICAR IDS DIFERENTES - INT 
    rule <k> var I:Id = I1:Id * I2:Id => var I = V1 * V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:Int  
                L2 |-> V2:Int ... 
        </store>  
    
    rule <k> I:Id = I1:Id * I2:Id =>  I = V1 * V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:Int  
                L2 |-> V2:Int ... 
        </store>   

    rule <k> I:Id : number = I1:Id * I2:Id =>  I : number = V1 * V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:Int  
                L2 |-> V2:Int ... 
        </store>  

    // REGRA DIVISÃO IDS DIFERENTES - INT 
    rule <k> var I:Id = I1:Id / I2:Id => var I = V1 / V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:Int  
                L2 |-> V2:Int ... 
        </store>  
    
    rule <k> I:Id = I1:Id / I2:Id =>  I = V1 / V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:Int  
                L2 |-> V2:Int ... 
        </store>   

    rule <k> I:Id : number = I1:Id / I2:Id =>  I : number = V1 / V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:Int  
                L2 |-> V2:Int ... 
        </store>  



        // ----------- REGRAS FOREACH ---------

     /*  rule <k>
                foreach (I:Id in [ (V:Int, Vs:ListValues) ] ) { S:Stmt }
                => S ~> foreach (I in [ Vs:ListValues ] ) { S }
                ...
            </k>
            <env> MEnv:Map => MEnv I |-> L </env>
            <store> MStore:Map => MStore L |-> V </store>
            <loc> L:Int => L +Int 1 </loc>
            when notBool (I in keys(MEnv))

        rule <k>
                foreach (I:Id in [ (V:Int, Vs:ListValues) ] ) { S:Stmt }
                => S ~> foreach (I in [ Vs:ListValues ] ) { S }
                ...
            </k>
            <env> ... I |-> L ... </env>
            <store> ... L |-> (_ => V) ... </store>

        rule foreach (I:Id in [ .ListValues ] ) { S:Stmt } => Skip */

        // ---------- REGRAS ARRAYLIST ------------

    /*    rule <k>var I:Id => Skip ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> 0 </store>
        <loc> L:Int => L +Int 1 </loc>
                    
        rule <k> var (I:Id, Xs:Ids) => var Xs ... </k>
            <env> MEnv:Map => MEnv I |-> L </env>
            <store> MStore:Map => MStore L |-> 0 </store>
            <loc> L:Int => L +Int 1 </loc>

        rule <k>var (I:Id, Xs:Ids) = V:Int => var Xs = V ... </k>
            <env> MEnv:Map => MEnv I |-> L </env>
            <store> MStore:Map => MStore L |-> V </store>
            <loc> L:Int => L +Int 1 </loc>

        rule var .Ids => Skip  
        rule var .Ids = _:Int => Skip  */




    

      // REGRA SOMAR IDS IGUAIS - INT (GLOBAL) 
    rule <k> var I:Id = I1:Id + I2:Id => var I = V + I2 ... </k> 
            <env> ... I1 |-> L ... </env>
        <store> 
            ... L |-> V:Int ... 
        </store>  


     rule <k> var I:Id = I1:Int + I2:Id => var I = I1 + V ... </k> 
            <env> ... I2 |-> L ... </env>
        <store> 
            ... L |-> V:Int ... 
        </store>  


    rule <k> I:Id : number = I1:Id + I2:Id => var I = V + I2 ... </k> 
            <env> ... I1 |-> L ... </env>
        <store> 
            ... L |-> V:Int ... 
        </store>  


     rule <k> I:Id : number = I1:Int + I2:Id => I : number = I1 + V ... </k> 
            <env> ... I2 |-> L ... </env>
        <store> 
            ... L |-> V:Int ... 
        </store>  


     rule <k> I:Id : number = I1:Id + I2:Id => I : number = V + I2 ... </k> 
            <env> ... I1 |-> L ... </env>
        <store> 
            ... L |-> V:Int ... 
        </store>  


     rule <k> I:Id = I1:Int + I2:Id =>  I = I1 + V ... </k> 
            <env> ... I2 |-> L ... </env>
        <store> 
            ... L |-> V:Int ... 
        </store>  


   rule <k> I:Id= I1:Id + I2:Id => I = V + I2 ... </k> 
            <env> ... I1 |-> L ... </env>
        <store> 
            ... L |-> V:Int ... 
        </store>  


  // REGRA CONCATENAR IDS IGUAIS - STRING (GLOBAL) 
    rule <k> var I:Id = I1:Id + I2:Id => var I = V + I2 ... </k> 
            <env> ... I1 |-> L ... </env>
        <store> 
            ... L |-> V:String ... 
        </store>  


     rule <k> var I:Id = I1:String + I2:Id => var I = I1 + V ... </k> 
            <env> ... I2 |-> L ... </env>
        <store> 
            ... L |-> V:String ... 
        </store>  


    rule <k> I:Id : string = I1:Id + I2:Id => I : string = V + I2 ... </k> 
            <env> ... I1 |-> L ... </env>
        <store> 
            ... L |-> V:String ... 
        </store>  


     rule <k> I:Id : string = I1:String + I2:Id => I : string = I1 + V ... </k> 
            <env> ... I2 |-> L ... </env>
        <store> 
            ... L |-> V:String ... 
        </store>  


    rule <k> I:Id : string = I1:Id + I2:Id => I : string = V + I2 ... </k> 
            <env> ... I1 |-> L ... </env>
        <store> 
            ... L |-> V:String ... 
        </store>  


     rule <k> I:Id = I1:String + I2:Id =>  I = I1 + V ... </k> 
            <env> ... I2 |-> L ... </env>
        <store> 
            ... L |-> V:String ... 
        </store>  


   rule <k> I:Id= I1:Id + I2:Id => I = V + I2 ... </k> 
            <env> ... I1 |-> L ... </env>
        <store> 
            ... L |-> V:String ... 
        </store>  




    // REGRAS PARA FUNÇÃO

    rule <k> function I:Id (P:Params) { S:Stmt } => Skip ... </k>
        ( .Bag => <thread> 
                <id> I </id>
                <scope> S </scope>
                <params> P </params>
                <temp> P </temp>
                <localEnv> .Map </localEnv>
            </thread>
        )

    rule <k> I:Id (.Values) => local(I, S) ... </k>
        <thread>
            ...
            <id> I </id>
            <scope> S:Stmt </scope>
            <params> P </params> 
            <temp> (.Params => P) </temp> 
            ...
        </thread>
    
    // CHAMADA DA FUNÇÃO
    rule <k> I:Id ((V:TypesVal, Vs:Values)) => I:Id (Vs)  ... </k>
        <thread>
            ...
            <id> I </id>
            <temp> ((P:Id, Ps:Params) => Ps)  </temp>
            <localEnv> Rho:Map => Rho P |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> V </store>
        <loc> L => L +Int 1 </loc>
        
    rule <k> local(FuncId:Id, var I:Id = V:Int ) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> V </store>
        <loc> L => L +Int 1 </loc>

    // ---------- INICIO DAS OPERAÇÕES ARITMÉTICAS NO ESCOPO LOCAL  -----------------

    // INT - SOMA  
    rule <k> local(FuncId:Id, var I:Id = V1:Int + V2:Int) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> (V1 +Int V2) </store>
        <loc> L => L +Int 1 </loc>

    rule <k> local(FuncId:Id, I:Id : number = V1:Int + V2:Int) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> (V1 +Int V2) </store>
        <loc> L => L +Int 1 </loc>

    rule <k> local(FuncId:Id, I:Id = V1:Int + V2:Int) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I |-> L ... </localEnv>
            ...
        </thread>
        <store> ... L |-> (_ => V1 +Int V2) ... </store>

        // INT - SUBTRAÇÃO  ------------------------------------- AINDA TESTAR
    rule <k> local(FuncId:Id, var I:Id = V1:Int - V2:Int) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> (V1 -Int V2) </store>
        <loc> L => L +Int 1 </loc>

    rule <k> local(FuncId:Id, I:Id : number = V1:Int - V2:Int) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> (V1 -Int V2) </store>
        <loc> L => L +Int 1 </loc>

    rule <k> local(FuncId:Id, I:Id = V1:Int - V2:Int) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I |-> L ... </localEnv>
            ...
        </thread>
        <store> ... L |-> (_ => V1 -Int V2) ... </store>

    // INT - MULTIPLICAÇÃO ------------------------------------- AINDA TESTAR
    rule <k> local(FuncId:Id, var I:Id = V1:Int * V2:Int) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> (V1 *Int V2) </store>
        <loc> L => L +Int 1 </loc>

    rule <k> local(FuncId:Id, I:Id : number = V1:Int - V2:Int) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> (V1 *Int V2) </store>
        <loc> L => L +Int 1 </loc>

    rule <k> local(FuncId:Id, I:Id = V1:Int * V2:Int) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I |-> L ... </localEnv>
            ...
        </thread>
        <store> ... L |-> (_ => V1:Int *Int V2:Int) ... </store>


    // INT - DIVISÃO ------------------------------------- AINDA TESTAR
    rule <k> local(FuncId:Id, var I:Id = V1:Int / V2:Int) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> (V1 /Int V2) </store>
        <loc> L => L +Int 1 </loc>

    rule <k> local(FuncId:Id, I:Id : number = V1:Int / V2:Int) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> (V1 /Int V2) </store>
        <loc> L => L +Int 1 </loc>

    rule <k> local(FuncId:Id, I:Id = V1:Int / V2:Int) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I |-> L ... </localEnv>
            ...
        </thread>
        <store> ... L |-> (_ => V1:Int /Int V2:Int) ... </store>

    // INICIO CONCATENAÇÃO STRING (local)

     rule <k> local(FuncId:Id, var I:Id = V1:String + V2:String) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> (V1 +String V2) </store>
        <loc> L => L +Int 1 </loc>

    rule <k> local(FuncId:Id, I:Id : string = V1:String + V2:String) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> (V1 +String V2) </store>
        <loc> L => L +Int 1 </loc>

    rule <k> local(FuncId:Id, I:Id = V1:String + V2:String) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I |-> L ... </localEnv>
            ...
        </thread>
        <store> ... L |-> (_ => V1 +String V2) ... </store>

    // --------------- inicializando variáveis no escopo local - String

    rule <k> local(FuncId:Id, I:Id : string ) => Skip ... </k>
        <thread>
            ...
            <id>FuncId</id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> "" </store>
        <loc> L => L +Int 1 </loc>

    rule <k> local(FuncId:Id, var I:Id ) => Skip ... </k>
        <thread>
            ...
            <id>FuncId</id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> "" </store>
        <loc> L => L +Int 1 </loc>

    // ----------------- inicializando variáveis no escopo local - Number

    rule <k> local(FuncId:Id, I:Id : number ) => Skip ... </k>
        <thread>
            ...
            <id>FuncId</id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> 0 </store>
        <loc> L => L +Int 1 </loc>

    rule <k> local(FuncId:Id, var I:Id ) => Skip ... </k>
        <thread>
            ...
            <id>FuncId</id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> 0 </store>
        <loc> L => L +Int 1 </loc>

     // ------------------ inicializando variáveis no escopo local - Boolean

    rule <k> local(FuncId:Id, I:Id : boolean ) => Skip ... </k>
        <thread>
            ...
            <id>FuncId</id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> false </store>
        <loc> L => L +Int 1 </loc>

    rule <k> local(FuncId:Id, var I:Id ) => Skip ... </k>
        <thread>
            ...
            <id>FuncId</id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> false </store>
        <loc> L => L +Int 1 </loc>

    // COLOCANDO O VALOR INT NAS VARIÁVEIS (LOCAL) -----------------------------------


    rule <k> local(FuncId:Id, I:Id : number = V:Int ) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> V </store>
        <loc> L => L +Int 1 </loc>

    rule <k> local(FuncId:Id, I:Id = V:Int ) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I |-> L ... </localEnv>
            ...
        </thread>
        <store> ... L |-> (_ => V:Int) ... </store>

        

    // COLOCANDO O VALOR STRING NAS VARIÁVEIS (LOCAL)--------------------- 


    rule <k> local(FuncId:Id, I:Id : string = V:String ) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> V </store>
        <loc> L => L +Int 1 </loc>

    rule <k> local(FuncId:Id, I:Id = V:String ) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I |-> L ... </localEnv>
            ...
        </thread>
        <store> ... L |-> (_ => V:String) ... </store>

    rule <k> local(FuncId:Id, var I:Id = V:String ) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> V </store>
        <loc> L => L +Int 1 </loc>

    
    // COLOCANDO O VALOR BOOLEAN NAS VARIÁVEIS (LOCAL)--------------------- 

    rule <k> local(FuncId:Id, I:Id : boolean = V:Bool ) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> V </store>
        <loc> L => L +Int 1 </loc>

    rule <k> local(FuncId:Id, I:Id = V:Bool ) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> V </store>
        <loc> L => L +Int 1 </loc>  

    rule <k> local(FuncId:Id, var I:Id = V:Bool ) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> V </store>
        <loc> L => L +Int 1 </loc>



//  local ( teste , var y = x + x )

    // REGRA SOMAR IDS - INT (LOCAL) 
    rule <k> local(FuncId:Id, var I:Id = I1:Id + I2:Id ) => local(FuncId, var I = V + I2) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I1 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:Int ... 
        </store>  


     rule <k> local(FuncId:Id, var I:Id = I1:Int + I2:Id ) => local(FuncId, var I = I1 + V) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I2 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:Int ... 
        </store>  



    rule <k> local(FuncId:Id, I:Id = I1:Id + I2:Id ) => local(FuncId, I = V + I2) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I1 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:Int ... 
        </store>  


     rule <k> local(FuncId:Id, I:Id = I1:Int + I2:Id ) => local(FuncId, I = I1 + V) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I2 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:Int ... 
        </store>  



    rule <k> local(FuncId:Id, I:Id : number = I1:Id + I2:Id ) => local(FuncId, I : number = V + I2) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I1 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:Int ... 
        </store>  


     rule <k> local(FuncId:Id, I:Id : number = I1:Int + I2:Id ) => local(FuncId, I : number = I1 + V) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I2 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:Int ... 
        </store> 

    // REGRA SUBTRAIR IDS - INT (LOCAL)   ----------------------------------- AINDA TESTAR
    rule <k> local(FuncId:Id, var I:Id = I1:Id - I2:Id ) => local(FuncId, var I = V - I2) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I1 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:Int ... 
        </store>  


     rule <k> local(FuncId:Id, var I:Id = I1:Int - I2:Id ) => local(FuncId, var I = I1 - V) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I2 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:Int ... 
        </store>  



    rule <k> local(FuncId:Id, I:Id = I1:Id - I2:Id ) => local(FuncId, I = V - I2) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I1 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:Int ... 
        </store>  


     rule <k> local(FuncId:Id, I:Id = I1:Int - I2:Id ) => local(FuncId, I = I1 - V) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I2 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:Int ... 
        </store>  



    rule <k> local(FuncId:Id, I:Id : number = I1:Id - I2:Id ) => local(FuncId, I : number = V - I2) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I1 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:Int ... 
        </store>  


     rule <k> local(FuncId:Id, I:Id : number = I1:Int - I2:Id ) => local(FuncId, I : number = I1 - V) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I2 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:Int ... 
        </store>


// REGRA MULTIPLICAR IDS - INT (LOCAL)  ----------------------------------- AINDA TESTAR
    rule <k> local(FuncId:Id, var I:Id = I1:Id * I2:Id ) => local(FuncId, var I = V * I2) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I1 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:Int ... 
        </store>  


     rule <k> local(FuncId:Id, var I:Id = I1:Int * I2:Id ) => local(FuncId, var I = I1 * V) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I2 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:Int ... 
        </store>  



    rule <k> local(FuncId:Id, I:Id = I1:Id * I2:Id ) => local(FuncId, I = V * I2) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I1 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:Int ... 
        </store>  


     rule <k> local(FuncId:Id, I:Id = I1:Int * I2:Id ) => local(FuncId, I = I1 * V) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I2 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:Int ... 
        </store>  



    rule <k> local(FuncId:Id, I:Id : number = I1:Id * I2:Id ) => local(FuncId, I : number = V * I2) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I1 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:Int ... 
        </store>  


     rule <k> local(FuncId:Id, I:Id : number = I1:Int * I2:Id ) => local(FuncId, I : number = I1 * V) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I2 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:Int ... 
        </store>


// REGRA DIVISAO IDS - INT (LOCAL)  ----------------------------------- AINDA TESTAR
    rule <k> local(FuncId:Id, var I:Id = I1:Id / I2:Id ) => local(FuncId, var I = V / I2) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I1 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:Int ... 
        </store>  


     rule <k> local(FuncId:Id, var I:Id = I1:Int / I2:Id ) => local(FuncId, var I = I1 / V) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I2 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:Int ... 
        </store>  



    rule <k> local(FuncId:Id, I:Id = I1:Id / I2:Id ) => local(FuncId, I = V / I2) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I1 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:Int ... 
        </store>  


     rule <k> local(FuncId:Id, I:Id = I1:Int / I2:Id ) => local(FuncId, I = I1 / V) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I2 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:Int ... 
        </store>  



    rule <k> local(FuncId:Id, I:Id : number = I1:Id / I2:Id ) => local(FuncId, I : number = V / I2) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I1 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:Int ... 
        </store>  


     rule <k> local(FuncId:Id, I:Id : number = I1:Int / I2:Id ) => local(FuncId, I : number = I1 / V) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I2 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:Int ... 
        </store> 



    
    // REGRA CONCATENAR IDS - STRING (LOCAL) 
    rule <k> local(FuncId:Id, I:Id : string = I1:Id + I2:Id ) => local(FuncId, I : string = V + I2) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I1 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:String ... 
        </store>  


     rule <k> local(FuncId:Id, I:Id : string = I1:String + I2:Id ) => local(FuncId, I : string = I1 + V) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I2 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:String ... 
        </store> 




    rule <k> local(FuncId:Id, I:Id = I1:Id + I2:Id ) => local(FuncId, I = V + I2) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I1 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:String ... 
        </store>  


     rule <k> local(FuncId:Id, I:Id = I1:String + I2:Id ) => local(FuncId, I = I1 + V) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I2 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:String ... 
        </store> 


      rule <k> local(FuncId:Id, var I:Id = I1:Id + I2:Id ) => local(FuncId, var I = V + I2) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I1 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:String ... 
        </store>  


     rule <k> local(FuncId:Id, var I:Id = I1:String + I2:Id ) => local(FuncId, var I = I1 + V) ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I2 |-> L ... </localEnv>
            ...
        </thread>
        <store> 
            ... L |-> V:String ... 
        </store> 



    // retorno da função 

    rule <k> local(FuncId:Id, return I:Id ) => V ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I |-> L ... </localEnv>
            ...
        </thread>
        <store> ... L |-> V ... </store>

    rule <k> local(FuncId:Id, return T:TypesVal ) => T ... </k> 
        <thread>
            ...
            <id> FuncId </id>
            ...
        </thread>

  //  rule local(I:Id, Return:R S2:Stmt) => local(I, R) ~> Skip [structural]
      



    // print
    rule <k> console.log(T:TypesVal) => Skip </k>
        <out> PSet:Set => PSet SetItem(T) </out>









    configuration <T>
        <k> $PGM:Block </k>
        <functions color="red"> 
            <thread multiplicity="*" color="orange" type="Map"> 
                <id> .K </id>
                <scope> .K </scope>
                <params> .K </params>
                <temp> .K </temp>
                <localEnv> .Map </localEnv>
            </thread> 
        </functions>
        <out> .Set </out>
        <env> .Map </env>
        <store> .Map </store>
        <loc> 1 </loc>
    </T>

endmodule

module TYPESCRIPT
    import DOMAINS
    import TYPESCRIPT-SYNTAX

    syntax KResult ::= Int | Bool | String
    syntax KVariable ::= Id
endmodule