-- module MakeNFA (makeNfa) where

--------------------------------------------------------------------------------------------------------------------------------------------------
-- The implementation of the paper "Computing ε-free NFA from regular expression in O(n (log(n))^2) time" by C HRISTIAN H AGENAH & A NCA M USCHOLL
--------------------------------------------------------------------------------------------------------------------------------------------------

-- It is used for constructing much better NFAs from regexes without ε-transitions and with few states and O(n (log n)^2 ) transitions in general 
-- This is a massive improvement to Thompson's construction. There is a cost in time by a factor of log^2 (n) and a bigger hidden constant.
-- However, the resulting improved NFA is worth such a cost, especially if it about to later be converted into a DFA.

-- It is worth mentioning that such a construction is at most a factor of log(n) worse from any construction of an NFA with the goal
-- of minimizing the transitions of an NFA, since the lower bound is Ω(n log(n)) for the number of transitions

import RegParser (parseRegexpr, RegExpr(EmptyChar, Kleene, Concat, Union, AnyLetter, Letter) )
import Types



-- makeNfa = snd. makeNfa' . snd. simplifyRegex. parseRegexpr 

-------------------------  Step 0: Definitions of several algebraic types and renamings which will be used below ---------------------------------


type ContainsE = Bool -- Boolean value which checks if a regex can produce the empty string or not
type BranchingFlag = Bool -- In the recursion step of the construction of the CFS system, check whether this regex belongs to another tree
type LastDataInfo = (Int, Int) -- Starting position and |last(F)| are saved here. Corresponding to lastdata array/list
type FirstDataInfo = (Int, Int) -- Starting position and |first(F)| are saved here. Corresponding to firstdata array/list
type Position = Int             -- corresponds to a character but for the linearized regex
type PositionsList = [(Position, Position)] -- a list of all the positions a subtree or a regex has
                                            -- a tuple says it has all the integers in the closed set [a,b] where a,b are the elements of the tuple
type RegInfo = (ContainsE, FirstDataInfo, LastDataInfo, PositionsList, BranchingFlag) -- a summary of information of a subexpression
                                                                                      -- used in the CFS system construction

-- algebraic type used to curry for each subexpression necessary information for the construction of the CFS system
data ModRegExpr = Num (RegInfo, Int) -- replaces the characters and wildcard with Integers
             | ModEmptyChar
             | ModKleene (RegInfo, ModRegExpr)
             | ModConcat (RegInfo, (ModRegExpr,ModRegExpr))
             | ModUnion  (RegInfo, (ModRegExpr,ModRegExpr))
             deriving(Eq, Show)

-- algebraic type used once in the construction of the simplified linearised regex and in the construction of the lastdata and firstdata structures
data ModExpr = NumE Int
             | EmptyCharE
             | KleeneE (ContainsE, PositionsList, ModExpr)
             | ConcatE (ContainsE, PositionsList, (ModExpr, ModExpr))
             | UnionE  (ContainsE, PositionsList, (ModExpr, ModExpr))
             deriving(Eq, Show)



-- Extracts the ContainsE information from a ModExpr regex
getModContainsE :: ModExpr -> ContainsE
--getModContainsE (LetterE _) = False
--getModContainsE AnyLetterE = False
getModContainsE (NumE _) = False
getModContainsE EmptyCharE = True
getModContainsE (KleeneE (_, _, _)) = True
getModContainsE (ConcatE (a, _, _)) = a
getModContainsE (UnionE  (a, _, _)) = a

----------------------------------------------------------------------------------------------------------------------------------
----------------------------------- Step 1: Simplification and linearisation of the regular expression ---------------------------
----------------------------------------------------------------------------------------------------------------------------------

-- Function which simplifies the form of a regular expression by removing redundant unions concats and kleene stars
-- using recursive simplification and checking for several cases described below

-- Also it linearises the expression by transforming every character in the regex uniquely into an integer
-- and keeps a list which informs what character every Int represents

type NextInt = Int -- The int which will be assigned to the next 
type LinearisationMap = [(Int, Char)] -- what character every Int represents

my3Thr :: (a,b,c) -> c
my3Thr (_,_,c) = c
my3Snd :: (a,b,c) -> b
my3Snd (_,b,_) = b
my3Fst :: (a,b,c) -> a
my3Fst (a,_,_) = a


-- An initialisation of an argument before the main procedure
simplifyRegexInitialisation :: RegExpr -> (LinearisationMap, NextInt, ModExpr)
simplifyRegexInitialisation regExpr = simplifyRegex regExpr 1

simplifyRegex :: RegExpr -> NextInt -> (LinearisationMap, NextInt, ModExpr)

-- (reg*)* and reg* produce the same language
simplifyRegex (Kleene (Kleene reg)) n = simplifyRegex (Kleene reg) n

-- (e | e)* == e, (e | reg)* == (reg | e)* == reg* where e is the empty string. Check for those cases
simplifyRegex (Kleene ( Union (reg1, reg2))) n = case reg of
        EmptyCharE ->  (list, nextInt, EmptyCharE)
        (KleeneE a) -> (list, nextInt, KleeneE a)
        (UnionE (_, _,(reg1', reg2'))) ->   if getModContainsE reg1' then (list, nextInt, KleeneE (True, [(n, nextInt-1)], reg2')) else 
                                            if getModContainsE reg2' then (list, nextInt, KleeneE (True, [(n, nextInt-1)], reg1')) else (list, nextInt, KleeneE (True, [(n, nextInt-1)], reg))
        _ ->  (list, nextInt, KleeneE (True, [(n,nextInt-1)], reg))
        where   (list, nextInt, reg) = simplifyRegex (Union (reg1, reg2)) n

-- e* == e, where e is the empty string. Check for this case
simplifyRegex (Kleene reg) n = case simplifyRegex reg n of
                ([], nextInt, EmptyCharE) -> ([], nextInt, EmptyCharE)
                (list, nextInt, reg') -> (list, nextInt, KleeneE (True, [(n, nextInt-1)], reg'))

-- e concat reg = reg concat e = reg. Check for those cases 
simplifyRegex (Concat (reg1, reg2)) n = case reg1' of
            EmptyCharE -> (list2, nextInt', reg2')
            _ -> case reg2' of
                    EmptyCharE -> (list1, nextInt', reg1')
                    reg2' -> (list1 ++ list2, nextInt', ConcatE (isE, [(n, nextInt'-1)], (reg1', reg2')))
            where   (list1, nextInt , reg1') = simplifyRegex reg1 n
                    (list2, nextInt', reg2') = simplifyRegex reg2 nextInt
                    isE = getModContainsE reg1' && getModContainsE reg2'

-- if reg produces e, then: (e | reg) == (reg | e) == reg. Check for those cases
simplifyRegex (Union (reg1, reg2)) n = case reg1' of
            EmptyCharE -> if getModContainsE reg2' then (list2, nextInt', reg2') else (list2, nextInt', UnionE (True, [(n, nextInt'-1)], (EmptyCharE, reg2')))
            _ -> case reg2' of
                EmptyCharE -> if getModContainsE reg1' then (list1, nextInt , reg1') else (list1, nextInt', UnionE (True, [(n, nextInt'-1)], (reg1', EmptyCharE)))
                _ -> (list1 ++ list2, nextInt', UnionE (isE, [(n, nextInt'-1)], (reg1', reg2')))
            where   (list1, nextInt , reg1') = simplifyRegex reg1 n
                    (list2, nextInt', reg2') = simplifyRegex reg2 nextInt
                    isE = getModContainsE reg1' || getModContainsE reg2'

simplifyRegex EmptyChar n = ([], n, EmptyCharE)

simplifyRegex AnyLetter n = ([(n, '.')], n+1, NumE n)

simplifyRegex (Letter a) n = ([(n, a)], n+1, NumE n)

simplifyRegex _ _ = error "Invalid simplifyRegex argument" -- It's invalid to get EndReg, NotEndReg in a input regex


----------------------------------------------------------------------------------------------------------------------------------
----------------------------------- Step 2: Creation of firstdat/lastdata and creating RegInfo for each subexpresion -------------
----------------------------------------------------------------------------------------------------------------------------------

-- First create the firstdata structure
-- the lastdata dataset will be created in a very similar way

-- It is useful to know whether a node is a root node or not of a subtree so that it is known whether the recursion can be stopped
-- in the construction of the firstdata array/list

getRegInfo :: ModRegExpr -> RegInfo
getRegInfo (Num (regInfo,_)) = regInfo
getRegInfo (ModKleene (regInfo,_)) = regInfo
getRegInfo (ModConcat (regInfo,_)) = regInfo
getRegInfo (ModUnion  (regInfo,_)) = regInfo
getRegInfo _ = error "False argument in getRegInfo: Given ModEmptyChar which has RegInfo"

getFdInfo :: ModRegExpr -> FirstDataInfo
getFdInfo (Num ((_,fdInfo,_,_,_),_)) = fdInfo
getFdInfo (ModKleene ((_,fdInfo,_,_,_),_)) = fdInfo
getFdInfo (ModConcat ((_,fdInfo,_,_,_),_)) = fdInfo
getFdInfo (ModUnion  ((_,fdInfo,_,_,_),_)) = fdInfo
getFdInfo _ = error "False argument in getFdInfo: Given ModEmptyChar which has no FirstDataInfo"

getLdInfo :: ModRegExpr -> LastDataInfo
getLdInfo (Num ((_,_,ldInfo,_,_),_)) = ldInfo
getLdInfo (ModKleene ((_,_,ldInfo,_,_),_)) = ldInfo
getLdInfo (ModConcat ((_,_,ldInfo,_,_),_)) = ldInfo
getLdInfo (ModUnion  ((_,_,ldInfo,_,_),_)) = ldInfo
getLdInfo _ = error "False argument in getLdInfo: Given ModEmptyChar which has no LastDataInfo"

--Num (RegInfo, Int) -- replaces the characters and wildcard with Integers
--ModEmptyChar
--ModKleene (RegInfo, ModRegExpr)
--ModConcat (RegInfo, (ModRegExpr,ModRegExpr))
--ModUnion  (RegInfo, (ModRegExpr,ModRegExpr))
-- type RegInfo = (ContainsE, FirstDataInfo, LastDataInfo, PositionsList, BranchingFlag)

type TreePositions = [[Position]]

-- fd root constructs the firstdata structure by finding the the FirstDataInfo for each node in the subtree and returns the a list
-- of lists of the positions of the subtrees defined for the construction of the firstdata structure in reverse order
-- takes as argument a syntax tree of a regular expression and an integer nextInt 
fdRoot :: ModExpr -> NextInt -> (ModRegExpr, NextInt, TreePositions)

fdRoot (KleeneE (containsE, modReg)) n = (ModKleene (regInfo, modReg'), nextInt, treePos) 
    where   (modReg', nextInt, treePos) = fdFirstStage modReg n
            regInfo = getRegInfo modReg'
            
fdRoot (NumE a) n = (Num ((False, (n,1), (0,0), [(a,a)],False),a), n+1, [[a]])

--fdIsRoot (ConcatE (containsE, (modReg1, modReg2))) = 


fdFirstStage :: ModExpr -> nextInt -> (ModRegExpr, NextInt, TreePositions)

--fdFirstStage (KleeneE (conta)) n


----------------------------------------------------------------------------------------------------------------------------------
--------------------------------------------- Step 3: Calculating the CFS systen -------------------------------------------------
----------------------------------------------------------------------------------------------------------------------------------



----------------------------------------------------------------------------------------------------------------------------------
----------------------------------------------- Step 4: Constructing the NFA -----------------------------------------------------
----------------------------------------------------------------------------------------------------------------------------------


----------------------------------------------------------------------------------------------------------------------------------
----------------------------------- Step 5: Removing the linearization from the NFA ----------------------------------------------
----------------------------------------------------------------------------------------------------------------------------------


testing :: [Char] -> (LinearisationMap, NextInt, ModExpr)
testing = simplifyRegexInitialisation . parseRegexpr