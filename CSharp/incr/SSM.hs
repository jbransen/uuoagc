{-# LANGUAGE DeriveGeneric #-}
module SSM where

import Control.DeepSeq
import GHC.Generics (Generic)

data Reg = PC | SP | MP | R3 | R4 | R5 | R6 | R7
   deriving Show

r0, r1, r2, r3, r4, r5, r6, r7 :: Reg
r0 = PC
r1 = SP
r2 = MP
r3 = R3
r4 = R4
r5 = R5
r6 = R6
r7 = R7


data Instr 
 = STR Reg | STL Int  | STS Int  | STA Int  -- Store from stack
 | LDR Reg | LDL Int  | LDS Int  | LDA Int  -- Load on stack
 | LDC Int | LDLA Int | LDSA Int | LDAA Int -- Load on stack
 | BRA Int | Bra String                     -- Branch always (relative/to label)
 | BRF Int | Brf String                     -- Branch on false
 | BRT Int | Brt String                     -- Branch on true
 | BSR Int | Bsr String                     -- Branch to subroutine
 | ADD | SUB | MUL | DIV | MOD              -- Arithmetical operations on 2 stack operands
 | EQ  | NE  | LT  | LE  | GT  | GE         -- Relational   operations on 2 stack operands
 | AND | OR  | XOR                          -- Bitwise      operations on 2 stack operands
 | NEG | NOT                                --              operations on 1 stack operand
 | RET | UNLINK | LINK Int | AJS Int        -- Procedure utilities
 | SWP | SWPR Reg | SWPRR Reg Reg | LDRR Reg Reg  -- Various swaps
 | JSR | TRAP Int | NOP | HALT              -- Other instructions
 | LABEL String                             -- Pseudo-instruction for generating a label
 | ANNOTE Reg Int Int String String
   deriving (Show, Generic)

instance NFData Instr

pop :: Instr
pop = AJS (-1)

type Code = [Instr]

formatInstr :: Instr -> String
formatInstr (LABEL s)   = s ++ ":"
formatInstr (ANNOTE r l h c s) = "\tannote " ++ show r ++ " " ++ show l ++ " " 
                                 ++ show h ++ " " ++ c ++ " " ++ show s
formatInstr x           = '\t' : show x

formatCode :: Code -> String
formatCode = filter clean . concatMap ((++"\n") . formatInstr)
  where
    clean :: Char -> Bool
    clean x = notElem x "()\""

codeSize :: Code -> Int
codeSize = sum . map instrSize

instrSize :: Instr -> Int
instrSize (LDRR  _ _) = 3
instrSize (SWPRR _ _) = 3
instrSize (BRA   _  ) = 2
instrSize (BRF   _  ) = 2
instrSize (BRT   _  ) = 2
instrSize (BSR   _  ) = 2
instrSize (Bra   _  ) = 2
instrSize (Brf   _  ) = 2
instrSize (Brt   _  ) = 2
instrSize (Bsr   _  ) = 2
instrSize (LDR   _  ) = 2
instrSize (LDL   _  ) = 2
instrSize (LDS   _  ) = 2
instrSize (LDA   _  ) = 2
instrSize (LDC   _  ) = 2
instrSize (LDLA  _  ) = 2
instrSize (LDSA  _  ) = 2
instrSize (LDAA  _  ) = 2
instrSize (STR   _  ) = 2
instrSize (STL   _  ) = 2
instrSize (STS   _  ) = 2
instrSize (STA   _  ) = 2
instrSize (AJS   _  ) = 2
instrSize (LINK  _  ) = 2
instrSize (TRAP  _  ) = 2
instrSize (SWPR  _  ) = 2
instrSize (LABEL _  ) = 0
instrSize _           = 1
