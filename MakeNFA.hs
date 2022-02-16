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
import Utilities


-- makeNfa = snd. makeNfa' . snd. simplifyRegex. parseRegexpr 

-------------------------  Step 0: Definitions of several algebraic types and renamings which will be used below ---------------------------------


type ContainsE = Bool -- Boolean value which checks if a regex can produce the empty string or not
type BranchingFlag = Bool -- In the recursion step of the construction of the CFS system, check whether this regex belongs to another tree
type LastDataInfo = (Int, Int) -- Starting position and |last(F)| are saved here. Corresponding to lastdata array/list
type FirstDataInfo = (Int, Int) -- Starting position and |first(F)| are saved here. Corresponding to firstdata array/list
type Position = Int             -- corresponds to a character but for the linearized regex
type NumOfPositions = Int
type PositionsList = (NumOfPositions ,(Position, Position)) -- the number of positions and wich positions a regex has
                                            -- the position tuple says it has all the integers in the closed set [a,b] where a,b are the elements of the tuple
type RegInfo = (ContainsE, FirstDataInfo, LastDataInfo, PositionsList, BranchingFlag) -- a summary of information of a subexpression
                                                                                      -- used in the CFS system construction

-- algebraic type used to curry for each subexpression necessary information for the construction of the CFS system
data ModRegExpr = Num (RegInfo, Int) -- replaces the characters and wildcard with Integers
             | ModEmptyChar
             | ModKleene (RegInfo, ModRegExpr)
             | ModConcat (RegInfo, (ModRegExpr,ModRegExpr))
             | ModUnion  (RegInfo, (ModRegExpr,ModRegExpr))
             deriving(Eq, Show)


-- Extracts the ContainsE information from a ModExpr regex
getModContainsE :: ModRegExpr -> ContainsE
--getModContainsE (LetterE _) = False
--getModContainsE AnyLetterE = False
getModContainsE (Num _) = False
getModContainsE ModEmptyChar = True
getModContainsE (ModKleene (_, _)) = True
getModContainsE (ModConcat ((a,_,_,_,_), _)) = a
getModContainsE (ModUnion  ((a,_,_,_,_), _)) = a

----------------------------------------------------------------------------------------------------------------------------------
----------------------------------- Step 1: Simplification and linearisation of the regular expression ---------------------------
----------------------------------------------------------------------------------------------------------------------------------

-- Function which simplifies the form of a regular expression by removing redundant unions concats and kleene stars
-- using recursive simplification and checking for several cases described below

-- Also it linearises the expression by transforming every character in the regex uniquely into an integer
-- and keeps a list which informs what character every Int represents

type NextInt = Int -- The int which will be assigned to the next 
type LinearisationMap = [(Int, Char)] -- what character every Int represents

produceRegInfo :: ContainsE -> PositionsList -> RegInfo
produceRegInfo containsE posList = (containsE, (0,0), (0,0), posList, False)

-- An initialisation of an argument before the main procedure
simplifyRegexInitialisation :: RegExpr -> (LinearisationMap, NextInt, ModRegExpr)
simplifyRegexInitialisation regExpr = simplifyRegex regExpr 1

simplifyRegex :: RegExpr -> NextInt -> (LinearisationMap, NextInt, ModRegExpr)

-- (reg*)* and reg* produce the same language
simplifyRegex (Kleene (Kleene reg)) n = simplifyRegex (Kleene reg) n

-- (e | e)* == e, (e | reg)* == (reg | e)* == reg* where e is the empty string. Check for those cases
simplifyRegex (Kleene ( Union (reg1, reg2))) n = case reg of
        ModEmptyChar ->  (list, nextInt, ModEmptyChar)
        (ModKleene a) -> (list, nextInt, ModKleene a)
        (ModUnion (_, (reg1', reg2'))) ->   if getModContainsE reg1' then (list, nextInt, ModKleene (regInfo, reg2')) else 
                                            if getModContainsE reg2' then (list, nextInt, ModKleene (regInfo, reg1')) else (list, nextInt, ModKleene (regInfo, reg))
        _ ->  (list, nextInt, ModKleene (regInfo, reg))
        where   (list, nextInt, reg) = simplifyRegex (Union (reg1, reg2)) n
                regInfo = produceRegInfo True (nextInt - n,(n, nextInt-1))

-- e* == e, where e is the empty string. Check for this case
simplifyRegex (Kleene reg) n = case simplifyRegex reg n of
                ([], nextInt, ModEmptyChar) -> ([], nextInt, ModEmptyChar)
                (list, nextInt, reg') -> (list, nextInt, ModKleene (produceRegInfo True (nextInt - n,(n, nextInt-1)), reg'))

-- e concat reg = reg concat e = reg. Check for those cases 
simplifyRegex (Concat (reg1, reg2)) n = case reg1' of
            ModEmptyChar -> (list2, nextInt', reg2')
            _ -> case reg2' of
                    ModEmptyChar -> (list1, nextInt', reg1')
                    reg2' -> (list1 ++ list2, nextInt', ModConcat (produceRegInfo isE (nextInt' - n,(n, nextInt'-1)), (reg1', reg2')))
            where   (list1, nextInt , reg1') = simplifyRegex reg1 n
                    (list2, nextInt', reg2') = simplifyRegex reg2 nextInt
                    isE = getModContainsE reg1' && getModContainsE reg2'

-- if reg produces e, then: (e | reg) == (reg | e) == reg. Check for those cases
simplifyRegex (Union (reg1, reg2)) n = case reg1' of
            ModEmptyChar -> if getModContainsE reg2' then (list2, nextInt', reg2') else (list2, nextInt', ModUnion (regInfo, (ModEmptyChar, reg2')))
            _ -> case reg2' of
                ModEmptyChar -> if getModContainsE reg1' then (list1, nextInt' , reg1') else (list1, nextInt', ModUnion (regInfo, (reg1', ModEmptyChar)))
                _ -> (list1 ++ list2, nextInt', ModUnion (regInfo, (reg1', reg2')))
            where   (list1, nextInt , reg1') = simplifyRegex reg1 n
                    (list2, nextInt', reg2') = simplifyRegex reg2 nextInt
                    isE = getModContainsE reg1' || getModContainsE reg2'
                    regInfo = produceRegInfo isE (nextInt' - n,(n, nextInt'-1))

simplifyRegex EmptyChar n = ([], n, ModEmptyChar)

simplifyRegex AnyLetter n = ([(n, '.')], n+1, Num (produceRegInfo False (1,(n,n)),n))

simplifyRegex (Letter a) n = ([(n, a)], n+1, Num (produceRegInfo False (1,(n,n)),n))

simplifyRegex _ _ = error "Invalid simplifyRegex argument" -- It's invalid to get EndReg, NotEndReg in a input regex


----------------------------------------------------------------------------------------------------------------------------------
----------------------------------- Step 2: Creation of firstdata/lastdata and creating RegInfo for each subexpresion ------------
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
getRegInfo _ = error "False argument in getRegInfo: Given ModEmptyChar which has no RegInfo"

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


type FirstData = [Position]
type LastData = [Position]

-- fd root constructs the firstdata structure by finding the the FirstDataInfo for each node in the subtree and returns the a list
-- of lists of the positions of the subtrees defined for the construction of the firstdata structure in reverse order
-- takes as argument a syntax tree of a regular expression and an integer nextInt 
fdRoot :: ModRegExpr -> NextInt -> FirstData -> (ModRegExpr, NextInt, FirstData)

fdRoot (ModKleene (_, modReg)) n fd = (ModKleene ((True,a2,a3,a4,False), modReg''), nextInt', fd2) 
    where   (modReg', nextInt, fd1) = fdFirstStage modReg n fd
            (modReg'', nextInt', fd2) = fdSecondStage modReg' nextInt fd1
            (_,a2,a3,a4,_) = getRegInfo modReg''

fdRoot (ModConcat ((containsE, _,_,posList,_), (modReg1, modReg2))) n fd
    | getModContainsE modReg1 = let (modReg2', nextInt2, fd1) = fdFirstStage modReg2 n fd
                                    (modReg1', nextInt1, fd2) = fdFirstStage modReg1 nextInt2 fd1
                                    (modReg1'', nextInt1', fd3) = fdSecondStage modReg1' nextInt1  fd2
                                    (modReg2'', nextInt2', fd4) = fdSecondStage modReg2' nextInt1' fd3
                                    
                                    (_,(a21,a22),a3,_,_) = getRegInfo modReg1''
                                    (_,(_,b22),b3,_,_) = getRegInfo modReg2''  in
                                    (ModConcat ((containsE, (a21, a22+b22),a3,posList,False), (modReg1'', modReg2'')), nextInt2', fd4)
    
    | otherwise = let   (modReg1', nextInt, fd1)  = fdFirstStage modReg1 n fd 
                        (modReg1'', nextInt', fd2) = fdSecondStage modReg1' nextInt fd1
                        (modReg2', nextInt'', fd3) = fdRoot modReg2 nextInt' fd2
                        (_,a2,a3,_,_) = getRegInfo modReg1'' in
                        (ModConcat ((containsE, a2, a3, posList, False), (modReg1'', modReg2')), nextInt'', fd3)


fdRoot (ModUnion ((containsE, _,_,posList,_), (modReg1, modReg2))) n fd = case modReg1 of
    ModEmptyChar -> (ModUnion ((True, (b21,b22),b3,posList,False), (modReg1'',modReg2'')), nextInt2', fd4)
    _ ->   case modReg2 of
        ModEmptyChar -> (ModUnion ((True, (a21,a22),a3,posList,False), (modReg1'', modReg2'')), nextInt2', fd4)
        _ -> (ModUnion ((containsE, (a21, a22+b22),a3, posList,False), (modReg1'', modReg2'')), nextInt2', fd4)
    
    where   (modReg2', nextInt2, fd1) = fdFirstStage modReg2 n fd
            (modReg1', nextInt1, fd2) = fdFirstStage modReg1  nextInt2  fd1
            (modReg1'', nextInt1', fd3) = fdSecondStage  modReg1' nextInt1  fd2
            (modReg2'', nextInt2', fd4) = fdSecondStage  modReg2' nextInt1' fd3
            (_,(a21,a22),a3,_,_) = getRegInfo modReg1''
            (_,(b21,b22),b3,_,_) = getRegInfo modReg2''
                                    


fdRoot (Num (_,a)) n fd = (Num ((False, (n,1), (0,0), (1,(a,a)),False),a), n-1, a:fd)

fdRoot ModEmptyChar n fd = (ModEmptyChar, n, fd)

----------------------------------------------------------------------------------------------------------------------------------

fdFirstStage :: ModRegExpr -> NextInt -> FirstData -> (ModRegExpr, NextInt, FirstData)

fdFirstStage (ModKleene (_, modReg)) n fd = (ModKleene ((True, b2,b3,b4, b5), modReg'), nextInt, fd1)
        where   (modReg', nextInt, fd1) = fdFirstStage modReg n fd
                (_,b2,b3,b4,b5) = getRegInfo modReg'

fdFirstStage (ModConcat ((containsE, _,_,posList,_), (modReg1, modReg2))) n fd
    | getModContainsE modReg1 = let (modReg1', nextInt,  fd1) = fdFirstStage modReg1 n fd
                                    (modReg2', nextInt', fd2) = fdFirstStage modReg2 nextInt fd1
                                    (_,( _  ,b22),b3,_,_) = getRegInfo modReg1'
                                    (_,(c21 ,c22),_,_,_) = getRegInfo modReg2'  in
                                    (ModConcat ((containsE, (c21, b22+c22),b3,posList,False), (modReg1', modReg2')), nextInt', fd2)
    
    | otherwise = let   (modReg1', nextInt, fd1)  = fdFirstStage modReg1 n fd
                        (_,b2,b3,_,_) = getRegInfo modReg1' in
                        (ModConcat ((containsE, b2, b3, posList, False), (modReg1', modReg2)), nextInt, fd1)


fdFirstStage (ModUnion ((containsE, _,_,posList,_), (modReg1, modReg2))) n fd = case modReg1 of
    ModEmptyChar -> (ModUnion ((True, (c21,c22),c3,posList,False), (modReg1',modReg2')), nextInt2, fd2)
    _ ->   case modReg2 of
        ModEmptyChar -> (ModUnion ((True, (b21,b22), b3,posList,False), (modReg1', modReg2')), nextInt2, fd2)
        _ -> (ModUnion ((containsE, (c21, b22+c22) , b3,posList,False), (modReg1', modReg2')), nextInt2, fd2)
    
    where   (modReg1', nextInt1, fd1) = fdFirstStage modReg1 n fd
            (modReg2', nextInt2, fd2) = fdFirstStage modReg2 nextInt1 fd1
            (_,(b21,b22),b3,_,_) = getRegInfo modReg1'
            (_,(c21,c22),c3,_,_) = getRegInfo modReg2'
                                    

  
fdFirstStage (Num (_,a)) n fd = (Num ((False, (n,1), (0,0), (1,(a,a)), False),a), n-1, a:fd)

fdFirstStage ModEmptyChar n fd = (ModEmptyChar, n, fd)

----------------------------------------------------------------------------------------------------------------------------------

fdSecondStage :: ModRegExpr -> NextInt -> FirstData -> (ModRegExpr, NextInt, FirstData)

fdSecondStage (ModKleene (_, modReg)) n fd = (ModKleene ((True, a2,a3,a4, False), modReg'), nextInt, fd1)
        where   (modReg', nextInt, fd1) = fdSecondStage modReg n fd
                (_,a2,a3,a4,_) = getRegInfo modReg'

fdSecondStage (ModConcat ((a1,a2,a3,a4,_), (modReg1, modReg2))) n fd = 
                                let fdFunction = if getModContainsE modReg1 then fdSecondStage else fdRoot
                                    (modReg1', nextInt1, fd1) = fdSecondStage modReg1 n fd
                                    (modReg2', nextInt2, fd2) = fdFunction modReg2 nextInt1 fd1 in
                                    (ModConcat ((a1, a2,a3,a4,False), (modReg1', modReg2')), nextInt2, fd2)

fdSecondStage (ModUnion (regInfo, (modReg1, modReg2))) n fd = (ModUnion (regInfo, (modReg1',modReg2')), nextInt2, fd2)
    
    where   (modReg1', nextInt1, fd1) = fdSecondStage modReg1 n fd
            (modReg2', nextInt2, fd2) = fdSecondStage modReg2 nextInt1 fd1

fdSecondStage (Num a) n fd = (Num a, n, fd)

fdSecondStage ModEmptyChar n fd = (ModEmptyChar, n, fd)


----------------------------------------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------------------------------------


-- Now create the Lastdata structure with almost the same logic as the construction of the the FirstData structure 



-- fd root constructs the firstdata structure by finding the the FirstDataInfo for each node in the subtree and returns the a list
-- of lists of the positions of the subtrees defined for the construction of the firstdata structure in reverse order
-- takes as argument a syntax tree of a regular expression and an integer nextInt 
ldRoot :: ModRegExpr -> NextInt -> LastData -> (ModRegExpr, NextInt, LastData)

ldRoot (ModKleene (_, modReg)) n ld = (ModKleene ((True,a2,a3,a4,False), modReg''), nextInt', ld2) 
    where   (modReg', nextInt, ld1) = ldFirstStage modReg n ld
            (modReg'', nextInt', ld2) = ldSecondStage modReg' nextInt ld1
            (_,a2,a3,a4,_) = getRegInfo modReg''

ldRoot (ModConcat ((containsE, ldInfo,_,posList,_), (modReg1, modReg2))) n ld
    | getModContainsE modReg2 = let (modReg2', nextInt2, ld1) = ldFirstStage modReg2 n ld
                                    (modReg1', nextInt1, ld2) = ldFirstStage modReg1 nextInt2 ld1
                                    (modReg2'', nextInt2', ld3) = ldSecondStage modReg2' nextInt1  ld2
                                    (modReg1'', nextInt1', ld4) = ldSecondStage modReg1' nextInt2' ld3
                                    
                                    (_,_,(a31,a32),_,_) = getRegInfo modReg1''
                                    (_,_,(b31,b32),_,_) = getRegInfo modReg2''  in
                                    (ModConcat ((containsE, ldInfo, (a31, a32+b32),posList,False), (modReg1'', modReg2'')), nextInt1', ld4)
    
    | otherwise = let   (modReg2', nextInt, ld1)  = ldFirstStage modReg2 n ld 
                        (modReg2'', nextInt', ld2) = ldSecondStage modReg2' nextInt ld1
                        (modReg1', nextInt'', ld3) = ldRoot modReg1 nextInt' ld2
                        (_,_,a3,_,_) = getRegInfo modReg2'' in
                        (ModConcat ((containsE, ldInfo, a3, posList, False), (modReg1', modReg2'')), nextInt'', ld3)


ldRoot (ModUnion ((containsE, ldInfo,_,posList,_), (modReg1, modReg2))) n ld = case modReg1 of
    ModEmptyChar -> (ModUnion ((True, ldInfo, (b31,b32),posList,False), (modReg1'',modReg2'')), nextInt1', ld4)
    _ ->   case modReg2 of
        ModEmptyChar -> (ModUnion ((True, ldInfo, (a31,a32),posList,False), (modReg1'', modReg2'')), nextInt1', ld4)
        _ -> (ModUnion ((containsE, ldInfo, (a31, a32+b32), posList,False), (modReg1'', modReg2'')), nextInt1', ld4)
    
    where   (modReg2', nextInt2, ld1) = ldFirstStage modReg2 n ld
            (modReg1', nextInt1, ld2) = ldFirstStage modReg1  nextInt2  ld1
            (modReg2'', nextInt2', ld3) = ldSecondStage  modReg2' nextInt1  ld2
            (modReg1'', nextInt1', ld4) = ldSecondStage  modReg1' nextInt2' ld3
            (_,_,(a31,a32),_,_) = getRegInfo modReg1''
            (_,_,(b31,b32),_,_) = getRegInfo modReg2''
                                    


ldRoot (Num ((_,ldInfo,_,_,_),a)) n ld = (Num ((False, ldInfo, (n,1), (1,(a,a)),False),a), n-1, a:ld)

ldRoot ModEmptyChar n ld = (ModEmptyChar, n, ld)

----------------------------------------------------------------------------------------------------------------------------------

ldFirstStage :: ModRegExpr -> NextInt -> LastData -> (ModRegExpr, NextInt, LastData)

ldFirstStage (ModKleene (_, modReg)) n ld = (ModKleene ((True, b2,b3,b4, b5), modReg'), nextInt, ld1)
        where   (modReg', nextInt, ld1) = ldFirstStage modReg n ld
                (_,b2,b3,b4,b5) = getRegInfo modReg'

ldFirstStage (ModConcat ((containsE, ldInfo,_,posList,_), (modReg1, modReg2))) n ld
    | getModContainsE modReg2 = let (modReg2', nextInt,  ld1) = ldFirstStage modReg2 n ld
                                    (modReg1', nextInt', ld2) = ldFirstStage modReg1 nextInt ld1
                                    (_,_,(b31,b32),_,_) = getRegInfo modReg1'
                                    (_,_,( _ ,c32),_,_) = getRegInfo modReg2'  in
                                    (ModConcat ((containsE, ldInfo, (b31, b32+c32),posList,False), (modReg1', modReg2')), nextInt', ld2)
    
    | otherwise = let   (modReg2', nextInt, ld1)  = ldFirstStage modReg2 n ld
                        (_,_,b3,_,_) = getRegInfo modReg2' in
                        (ModConcat ((containsE, ldInfo, b3, posList, False), (modReg1, modReg2')), nextInt, ld1)


ldFirstStage (ModUnion ((containsE, ldInfo,_,posList,_), (modReg1, modReg2))) n ld = case modReg1 of
    ModEmptyChar -> (ModUnion ((True, ldInfo,(c31,c32),posList,False), (modReg1',modReg2')), nextInt1, ld2)
    _ ->   case modReg2 of
        ModEmptyChar -> (ModUnion ((True, ldInfo, (b31,b32), posList,False), (modReg1', modReg2')), nextInt1, ld2)
        _ -> (ModUnion ((containsE, ldInfo, (b31, b32+c32),  posList,False), (modReg1', modReg2')), nextInt1, ld2)
    
    where   (modReg2', nextInt2, ld1) = ldFirstStage modReg2 n ld
            (modReg1', nextInt1, ld2) = ldFirstStage modReg1 nextInt2 ld1
            (_,_,(b31,b32),_,_) = getRegInfo modReg1'
            (_,_,(c31,c32),_,_) = getRegInfo modReg2'
                                    

  
ldFirstStage (Num ((_,ldInfo,_,_,_),a)) n ld = (Num ((False, ldInfo, (n,1), (1,(a,a)), False),a), n-1, a:ld)

ldFirstStage ModEmptyChar n ld = (ModEmptyChar, n, ld)

----------------------------------------------------------------------------------------------------------------------------------

ldSecondStage :: ModRegExpr -> NextInt -> LastData -> (ModRegExpr, NextInt, LastData)

ldSecondStage (ModKleene (_, modReg)) n ld = (ModKleene ((True, a2,a3,a4, False), modReg'), nextInt, ld1)
        where   (modReg', nextInt, ld1) = ldSecondStage modReg n ld
                (_,a2,a3,a4,_) = getRegInfo modReg'

ldSecondStage (ModConcat (regInfo, (modReg1, modReg2))) n ld = 
                                let ldFunction = if getModContainsE modReg2 then ldSecondStage else ldRoot
                                    (modReg2', nextInt2, ld1) = ldSecondStage modReg2 n ld
                                    (modReg1', nextInt1, ld2) = ldFunction modReg1 nextInt2 ld1 in
                                    (ModConcat (regInfo, (modReg1', modReg2')), nextInt1, ld2)

ldSecondStage (ModUnion (regInfo, (modReg1, modReg2))) n ld = (ModUnion (regInfo, (modReg1',modReg2')), nextInt1, ld2)
    
    where   (modReg2', nextInt2, ld1) = ldSecondStage modReg2 n ld
            (modReg1', nextInt1, ld2) = ldSecondStage modReg1 nextInt2 ld1

ldSecondStage (Num a) n ld = (Num a, n, ld)

ldSecondStage ModEmptyChar n ld = (ModEmptyChar, n, ld)


----------------------------------------------------------------------------------------------------------------------------------
--------------------------------------------- Step 3: Calculating the CFS systen -------------------------------------------------
----------------------------------------------------------------------------------------------------------------------------------



----------------------------------------------------------------------------------------------------------------------------------
----------------------------------------------- Step 4: Constructing the NFA -----------------------------------------------------
----------------------------------------------------------------------------------------------------------------------------------


----------------------------------------------------------------------------------------------------------------------------------
----------------------------------- Step 5: Removing the linearization from the NFA ----------------------------------------------
----------------------------------------------------------------------------------------------------------------------------------




----------------------------------- Some functions used for testing the code written ---------------------------------------------


testing :: [Char] -> (LinearisationMap, NextInt, ModRegExpr)
testing = simplifyRegexInitialisation . parseRegexpr

getNumOfPositions :: ModRegExpr -> NumOfPositions
getNumOfPositions ModEmptyChar = 0
getNumOfPositions (Num _) = 1
getNumOfPositions (ModKleene ((_, _,_,(num,_),_),_)) = num
getNumOfPositions (ModUnion  ((_, _,_,(num,_),_),_)) = num
getNumOfPositions (ModConcat ((_, _,_,(num,_),_),_)) = num



testing1 :: [Char] -> (NextInt, NextInt, ModRegExpr, [(Position, NumOfPositions)], [(Position, NumOfPositions)])
testing1 regex = (a1,a2, reg'', myZip fdlist [1..n], myZip ldlist [1..n])
    where   (l, _, reg) = testing regex
            n = getNumOfPositions reg
            (reg',a1, fdlist) = fdRoot reg n [] 
            (reg'',a2, ldlist) = ldRoot reg' n []