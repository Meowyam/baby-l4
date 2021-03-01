{
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{- HLINT ignore -}

module Parser (
  parseProgram
--  , parseTokens,
) where

import Coordinates
import Lexer
import Syntax

import Prelude
import Control.Monad.Except

}

-- Entry point
%name program Program

-- Lexer structure
%tokentype { Token }


-- Parser monad
%monad { Alex }
%lexer { lexwrap } { Token _ TokenEOF _ }
%error { parseError }

-- Token Names
%token
    assert  { Token _ TokenAssert _  }
    class   { Token _ TokenClass _ }
    decl    { Token _ TokenDecl _  }
    extends { Token _ TokenExtends _  }
    lexicon { Token _ TokenLexicon _  }
    rule    { Token _ TokenRule _  }

    Bool  { Token _ TokenBool _  }
    Int   { Token _ TokenInt _  }

    not    { Token _ TokenNot _  }
    forall { Token _ TokenForall _  }
    exists { Token _ TokenExists _  }
    if     { Token _ TokenIf _  }
    then   { Token _ TokenThen _  }
    else   { Token _ TokenElse _  }
    for    { Token _ TokenFor _  }
    true   { Token _ TokenTrue _  }
    false  { Token _ TokenFalse _  }

    '\\'  { Token _ TokenLambda _  }
    '->'  { Token _ TokenArrow _  }
    '-->' { Token _ TokenImpl _  }
    '||'  { Token _ TokenOr _  }
    '&&'  { Token _ TokenAnd _  }
    '='   { Token _ TokenEq _  }
    '<'   { Token _ TokenLt _  }
    '>'   { Token _ TokenGt _  }
    '+'   { Token _ TokenAdd _  }
    '-'   { Token _ TokenSub _  }
    '*'   { Token _ TokenMul _  }
    '/'   { Token _ TokenDiv _  }
    '%'   { Token _ TokenMod _  }
    '.'   { Token _ TokenDot _  }
    ','   { Token _ TokenComma _  }
    ':'   { Token _ TokenColon _  }
    '('   { Token _ TokenLParen _  }
    ')'   { Token _ TokenRParen _  }
    '{'   { Token _ TokenLBrace _  }
    '}'   { Token _ TokenRBrace _  }

    NUM   { Token _ TokenNum _ }
    VAR   { Token _ TokenSym _ }

-- Operators
%right '->'
%left '.'
%nonassoc if then else
%right '-->'
%right '||'
%right '&&'
%left not
%nonassoc '<' '=' '>'
%left '+' '-'
%left '*' '/' '%'
%left AMINUS
%%

Program :: { Program (Maybe ClassName) CoordRng }
Program : Lexicon  ClassDecls GlobalVarDecls Rules Assertions
                                   { Program (reverse $1) (reverse $2)  (reverse $3) (reverse $4) (reverse $5) }
Lexicon : lexicon Mappings { $2 }
Mappings :                   {[]}
          | Mappings Mapping {$2 : $1 }
Mapping : VAR '->' VAR { Mapping (token_Var_val $1) (token_Var_val $3) }
ClassDecls :                       { [] }
           | ClassDecls ClassDecl  { $2 : $1 }
ClassDecl : class VAR ClassDef     { ClassDecl (ClsNm (token_Var_val $2)) $3 }

ClassDef :  '{' FieldDecls '}'     { ClassDef (Just (ClsNm "Object")) (reverse $2) }
         |   extends VAR '{' FieldDecls '}'
                                   { ClassDef (Just (ClsNm (token_Var_val $2))) (reverse $4) }
FieldDecls :                       { [] }
           | FieldDecls FieldDecl  { $2 : $1 }

FieldDecl : VAR ':' Tp             { FieldDecl (FldNm (token_Var_val $1)) $3 }

GlobalVarDecls :                         { [] }
         | GlobalVarDecls GlobalVarDecl  { $2 : $1 }

GlobalVarDecl : decl VAR ':' Tp          { VarDecl (token_Var_val $2) $4 }

VarDeclsCommaSep :  VarDecl              { [$1] }
         | VarDeclsCommaSep  ',' VarDecl { $3 : $1 }

VarDecl : VAR ':' Tp                     { VarDecl (token_Var_val $1) $3 }


Assertions :                       { [] }
           | Assertions Assertion  { $2 : $1 }
Assertion : assert Expr            { Assertion $2 }

-- Atomic type
ATp   : Bool                      { BoolT }
     | Int                        { IntT }
     | VAR                        { ClassT (ClsNm (token_Var_val $1)) }
     | '(' TpsCommaSep ')'        { let tcs = $2 in if length tcs == 1 then head tcs else TupleT (reverse tcs) }

TpsCommaSep :                      { [] }
            | Tp                   { [$1] }
            | TpsCommaSep ',' Tp   { $3 : $1 }

Tp   : ATp                        { $1 }
     | Tp '->' Tp                 { FunT $1 $3 }


Pattern : VAR                      { VarP (token_Var_val $1) }
    | '(' VarsCommaSep ')'         { let vcs = $2 in if length vcs == 1 then VarP (head vcs) else VarListP (reverse vcs) }

VarsCommaSep :                      { [] }
            | VAR                   { [token_Var_val $1] }
            | VarsCommaSep ',' VAR  {  (token_Var_val $3) : $1 }

Expr : '\\' Pattern ':' ATp '->' Expr  { FunE coordNull $2 $4 $6 }
     | forall VAR ':' Tp '.' Expr      { QuantifE coordNull All (token_Var_val $2) $4 $6 }
     | exists VAR ':' Tp '.' Expr      { QuantifE coordNull Ex (token_Var_val $2) $4 $6 }
     | Expr '-->' Expr             { BinOpE coordNull (BBool BBimpl) $1 $3 }
     | Expr '||' Expr              { BinOpE coordNull (BBool BBor) $1 $3 }
     | Expr '&&' Expr              { BinOpE coordNull (BBool BBand) $1 $3 }
     | if Expr then Expr else Expr { IfThenElseE coordNull $2 $4 $6 }
     | not Expr                    { UnaOpE coordNull (UBool UBneg) $2 }
     | Expr '<' Expr               { BinOpE coordNull (BCompar BClt) $1 $3 }
     | Expr '>' Expr               { BinOpE coordNull (BCompar BCgt) $1 $3 }
     | Expr '=' Expr               { BinOpE coordNull (BCompar BCeq) $1 $3 }
     | Expr '+' Expr               { BinOpE coordNull (BArith BAadd) $1 $3 }
     | Expr '-' Expr               { BinOpE coordNull (BArith BAsub) $1 $3 }
     | '-' Expr %prec AMINUS       { UnaOpE coordNull (UArith UAminus) $2 }
     | Expr '*' Expr               { BinOpE coordNull (BArith BAmul) $1 $3 }
     | Expr '/' Expr               { BinOpE coordNull (BArith BAdiv) $1 $3 }
     | Expr '%' Expr               { BinOpE coordNull (BArith BAmod) $1 $3 }
     | App                         { $1 }

App : App Acc                     { AppE coordNull $1 $2 }
    | Acc                          { $1 }

-- field access
Acc : Acc '.' VAR                  { FldAccE coordNull $1 (FldNm (token_Var_val $3)) }
    | Atom                         { $1 }

Atom : '(' ExprsCommaSep ')'       { let ecs = $2 in if length ecs == 1 then head ecs else TupleE coordNull (reverse ecs) }
     | NUM                         { ValE coordNull (IntV (token_Int_val $1)) }
     | VAR                         { VarE coordNull (GlobalVar (token_Var_val $1)) }
     | true                        { ValE coordNull (BoolV True) }
     | false                       { ValE coordNull (BoolV False) }

ExprsCommaSep :                      { [] }
            | Expr                   { [$1] }
            | ExprsCommaSep ',' Expr  { $3 : $1 }


Rules  :                       { [] }
       | Rules Rule            { $2 : $1}
Rule:  RuleName RuleVarDecls RulePrecond RuleConcl { Rule $1 $2 $3 $4 }

RuleName: rule '<' VAR '>'     { (token_Var_val $3) }

RuleVarDecls :                       { [] }
             | for VarDeclsCommaSep  { reverse $2 }

RulePrecond : if Expr      { $2 }
RuleConcl   : then Expr    { $2 }

{

lexwrap :: (Token -> Alex a) -> Alex a
lexwrap = (alexMonadScan' >>=)

parseError :: Token -> Alex a
parseError (Token p tk s) =
  alexError' p ("parse error at token '" ++ s ++ "'")

parseProgram :: FilePath -> String -> Either Err (Program (Maybe ClassName) CoordRng)
parseProgram = runAlex' program

}
