module MakeNFA (
testing,
testing1,
testing2,
ModRegExpr(..),
LinearisationMap,
NextInt,
CFSSystem, 
IndexedFirstData, 
IndexedLastData, 
NumPosRem
) where

--------------------------------------------------------------------------------------------------------------------------------------------------
-- The implementation of the paper "Computing ε-free NFA from regular expression in O(n (log(n))^2) time" by C HRISTIAN H AGENAH & A NCA M USCHOLL
--------------------------------------------------------------------------------------------------------------------------------------------------

-- It is used for constructing much better NFAs from regexes without ε-transitions and with few states and O(n (log n)^2 ) transitions in general 
-- This is an improvement to Thompson's construction . There is a cost in time by a factor of log^2 (n) and a bigger hidden constant.
-- However, the resulting improved NFA is worth such a cost, especially if it about to later be converted into a DFA.

-- It is worth mentioning that such a construction is at most a factor of log(n) worse from any construction of an NFA with the goal
-- of minimizing the transitions of an NFA, since the lower bound is at least Ω(n log(n)) for the number of transitions

--import RegParser (parseRegexpr, RegExpr(EmptyChar, Kleene, Concat, Union, AnyLetter, Letter) )
import Types
import Utilities

import DictSet

import RegParser ( parseRegexpr, RegExpr(Letter, Kleene, Concat, Union, EmptyChar, AnyLetter) )

-- makeNfa = snd. makeNfa' . snd. simplifyRegex. parseRegexpr 

-------------------------  Step 0: Definitions of several algebraic types and renamings which will be used below ---------------------------------
import MakeNFAUtilities

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

-- Recursively construct the CFS system

constructFollowSet :: [(Position,Index)] -> [FirstDataInfo] -> [Position]
constructFollowSet [] _ = []
constructFollowSet _ [] = []
constructFollowSet l1@((pos,index):l1s) l2@((dataPos, dataNum):l2s)
    | dataPos <= index && index <= dataPos + (dataNum -1) = pos : constructFollowSet l1s l2
    | dataPos >  index = constructFollowSet l1s l2
    | otherwise = constructFollowSet l1 l2s 

cerror :: [FirstDataInfo] -> [LastDataInfo] -> FirstList -> LastList  -> IndexedInfo -> a
cerror f l fList lList flinfo = error $ "f = " ++ show f ++ " l = " ++ show l ++ " fList = " ++ show fList ++ " lList = " ++ show lList ++ " Indexed = " ++ show flinfo

constructCFS :: CFSSystem -> NextInt -> IndexedInfo -> FStarInfo -> (Bool,[FirstDataInfo],[FirstDataInfo],Int) -> (Bool,[LastDataInfo],[LastDataInfo],Int) -> FirstList -> LastList -> (CFSSystem, NextInt)
constructCFS cfs nextInt flInfo fsInfo (fBool,f1,f2,fnum) (lBool,l1,l2,lnum) fList lList 
    | b1 && b2 = (cfs, nextInt)
    | b1 = ((nextInt, lFollowSet, fList):cfs, nextInt+1)
    | b2 = ((nextInt, lList, fFollowSet):cfs, nextInt+1)
    | otherwise = ((nextInt+1, lFollowSet, fList):(nextInt, lList, fFollowSet):cfs, nextInt+2)
    where   ((f1',_,_), (l1',_,_)) = case fsInfo of
                    (MyJust fsfInfo, MyJust fslInfo) -> rootlistUpdate (fBool,f1,f2,fnum) (MyJust fsfInfo) (lBool,l1,l2,lnum) (MyJust fslInfo) True True
                    _ -> ((f1,f2,fnum), (l1,l2,lnum))
            (flf, fll) = flInfo
            fFollowSet = constructFollowSet flf (f2 ++ f1')
            lFollowSet = constructFollowSet fll (l2 ++ l1')
            b1 = null lList || null fFollowSet
            b2 = null fList || null lFollowSet

cfsConstruction :: ModRegExpr -> IndexedInfo -> CFSSystem -> NextInt -> FStarInfo -> (ModRegExpr, CFSSystem, NextInt, NumPosRem)

cfsConstruction subtree flInfo cfsSystem n fsInfo
    -- The case where the initial regex is the EmptyChar. In that case, nothing needs to be done
    | numPos == 0 =  (ModEmptyChar, [], 0, 0)

    -- The base case is reached
    | numPos == 1 =  let    (cfs, nextInt) = cfsConstructionBaseCase subtree n fsInfo' cfsSystem in
                            --error (show cfs)
                            (subtractPos (setFlag subtree) 1, cfs, nextInt, 1)

    -- The recursion has to be used
    | otherwise = let   (reg', cfs', nextInt, flInfo', k', (fBool,f1,f2,fnum), (lBool,l1,l2,lnum), fList, lList) = cfsConstructionRecCase subtree flInfo cfsSystem n fsInfo' numPos
                        (cfs'', nextInt') = constructCFS cfs' nextInt flInfo' fsInfo' (fBool,f1,f2,fnum) (lBool,l1,l2,lnum) fList lList 
                        (a1, a2, a3, k) = cfsConstruction reg' flInfo' cfs'' nextInt' fsInfo' in
                        --cerror f l fList lList flInfo'--error $ "Got " ++ (show cfs'')
                        --error $ "f = " ++ show f ++ " l = " ++ show l ++ " fsInfoNew" ++ show flInfo'
                        (a1, a2, a3, k+k')

    where   numPos = getNumOfPositions subtree
            --fdInfo = getFdInfo subtree
            --ldInfo = getLdInfo subtree
            fsInfo' = updateFSInfo subtree fsInfo
            --(_,_,_,(_,posTuple),_) = getRegInfo subtree
            --(fd, ld) = extractFirstLastPos flInfo1 fdInfo ldInfo

type CFSResult = (ModRegExpr, CFSSystem, NextInt, IndexedInfo, NumPosRem, (Bool,[FirstDataInfo],[FirstDataInfo],Int), (Bool,[LastDataInfo],[LastDataInfo],Int), FirstList, LastList)

-- The function which constructs the CFS system for the subtree t given the appropriately fdata(t) and ldata(t)
-- This function however is called only right from the recursion step, thus a modification of some parameters have to be made
-- Specifically, flinfo, fsInfo and
cfsConstructionAfterRec :: ModRegExpr -> IndexedInfo -> CFSSystem -> NextInt -> FStarInfo -> CFSResult

cfsConstructionAfterRec subtree flInfo cfsSystem n fsInfo
    -- The case where the initial regex is the EmptyChar. In that case, nothing needs to be done
    | numPos == 0 =  error "cfsConstructionAfterRec: Got numPos = 0"--(ModEmptyChar, [], 0, ([],[]), 0, (False,[],0), (False,[],0),[],[])

    -- The base case is reached
    | numPos == 1 =  let    (cfs, nextInt) = cfsConstructionBaseCase subtree n fsInfo' cfsSystem in
                            (subtractPos (setFlag subtree) 1, cfs, nextInt, flInfo2, 1, (False,[],[],0), (False,[],[],0), fd, ld)

    -- The recursion has to be used
    | otherwise = let   (reg', cfs', nextInt, flInfo', k', (fBool,f1,f2,fnum), (lBool,l1,l2,lnum), fList, lList) = cfsConstructionRecCase subtree flInfo1 cfsSystem n fsInfo' numPos
                        (cfs'', nextInt') = constructCFS cfs' nextInt flInfo' fsInfo' (fBool,f1,f2,fnum) (lBool,l1,l2,lnum) fList lList
                        (a1, a2, a3, k) = cfsConstruction reg' flInfo' cfs'' nextInt' fsInfo' in
                        --error $ "f = " ++ show f ++ " l = " ++ show l ++ " fsInfoNew" ++ show flInfo'
                        (a1, a2, a3, flInfo2, k+k', (False,[],[],0), (False,[],[],0), fd, ld)

    where   numPos = getNumOfPositions subtree
            fdInfo = getFdInfo subtree
            ldInfo = getLdInfo subtree
            fsInfo' = updateFSInfo subtree fsInfo
            (_,_,_,(_,posTuple),_) = getRegInfo subtree
            (flInfo1, flInfo2) = separateFirstLastInfo flInfo posTuple
            (fd, ld) = extractFirstLastPos flInfo1 fdInfo ldInfo
            

            --(containsE, (fdPos,fdNum),(ldPos,ldnum), (posNum, (pos1,pos2)), branchFlag) = getRegInfo subtree


-- The recursive step of the recursion 
cfsConstructionRecCase :: ModRegExpr -> IndexedInfo -> CFSSystem -> NextInt -> FStarInfo -> NumOfPositions -> CFSResult

cfsConstructionRecCase (ModKleene ((_,fdinfo, ldinfo,(posNum,posTuple),flag),reg)) flinfo cfsSystem n fsinfo numPos 
    = (ModKleene ((True, fdinfo, ldinfo, (posNum - k',posTuple),flag),reg'), cfs', nextInt, flinfo', k', (fbool,f1',f2',fnum'),(lbool,l1',l2',fnum'), fList, lList)
    where   (reg', cfs', nextInt, flinfo', k', (fbool,f1,f2,fnum), (lbool,l1,l2,lnum), fList, lList) 
                    = cfsConstructionRecCase reg flinfo cfsSystem n (MyJust fdinfo,MyJust ldinfo) numPos
            ((f1',f2',fnum'),(l1',l2',lnum')) = rootlistUpdate (fbool,f1,f2,fnum) (MyJust fdinfo) (lbool,l1,l2,lnum) (MyJust ldinfo) True True


cfsConstructionRecCase (ModConcat ((containsE,fdInfo, ldInfo,(posNum,posTuple),flag),(reg1,reg2))) flinfo cfsSystem n fsinfo numPos 
    = (ModConcat ((containsE, fdInfo, ldInfo, (posNum - k',posTuple),flag),(reg1', reg2')), cfs', nextInt, flinfo', k', (fbool',f1',f2',fnum'),(lbool',l1',l2',lnum'), fList, lList)
    where   (e1,e2) = (getModContainsE reg1, getModContainsE  reg2)
            (isLeft, isEnd) = findPath numPos reg1 reg2
            (fsf, fsl) = fsinfo
            fsinfoNew = if isLeft then (if e2 then fsf else MyNothing,fsl) else (fsf, if e1 then fsl else MyNothing)
            reg = if isLeft then reg1 else reg2
            (reg', cfs', nextInt, flinfo', k', (fbool,f1,f2,fnum), (lbool, l1,l2,lnum), fList, lList) = if  isEnd then 
                                                                                                    cfsConstructionAfterRec reg flinfo cfsSystem n fsinfoNew else 
                                                                                                    cfsConstructionRecCase reg flinfo cfsSystem n fsinfoNew numPos
            (reg1', reg2') = if isLeft then (reg', reg2) else (reg1, reg')
            (fd',ld') = if isLeft then (MyJust (getFdInfo reg2), MyNothing) else (MyNothing, MyJust (getLdInfo reg1))
            (fbool',lbool')
                | isLeft =  if e2 then (fbool, lbool) else (True, lbool)
                | e1 = (fbool, lbool)
                | otherwise = (fbool, True)   
            ((f1',f2',fnum'),(l1',l2',lnum')) = rootlistUpdate (fbool, f1,f2,fnum) fd' (lbool,l1,l2,lnum) ld' e1 e2

cfsConstructionRecCase (ModUnion ((containsE,fdInfo, ldInfo,(posNum,posTuple),flag),(reg1,reg2))) flinfo cfsSystem n fsinfo numPos 
    = (ModUnion ((containsE, fdInfo, ldInfo, (posNum - k',posTuple),flag),(reg1', reg2')), cfs', nextInt, flinfo', k', (fbool,f1,f2,fnum),(lbool,l1,l2,lnum), fList, lList)
    where   (isLeft, isEnd) = findPath numPos reg1 reg2
            reg = if isLeft then reg1 else reg2
            (reg', cfs', nextInt, flinfo', k', (fbool,f1,f2,fnum), (lbool,l1,l2,lnum), fList, lList) = if   isEnd then 
                                                                        cfsConstructionAfterRec reg flinfo cfsSystem n fsinfo else 
                                                                        cfsConstructionRecCase reg flinfo cfsSystem n fsinfo numPos
            (reg1', reg2') = if isLeft then (reg', reg2) else (reg1, reg')

cfsConstructionRecCase (Num _) _ _ _ _ _ = error "cfsConstructionRecCase: Got Num a, which is not possible in the RecCase"

cfsConstructionRecCase ModEmptyChar _ _ _ _ _ = error "cfsConstructionRecCase: Got ModEmptyChar"

-- Base case for subtree cfs construction when |pos(t)| = 1.
cfsConstructionBaseCase :: ModRegExpr -> NextInt -> FStarInfo -> CFSSystem -> (CFSSystem, NextInt)
cfsConstructionBaseCase (Num ((_,(fdpos,fdnum), (ldpos,ldnum),_,_),a)) n fsinfo cfs = case fsinfo of
    (MyJust (fsfpos,fsfnum),MyJust (fslpos,fslnum)) -> let  f = fsfpos <= fdpos && fsfpos + fsfnum >= fdpos + fdnum -- first(Num a) subset of first(t)
                                                            l = fslpos <= ldpos && fslpos + fslnum >= ldpos + ldnum in -- last(Num a) subset of last(t)
                                                            if f && l then ((n,[a],[a]):cfs, n+1) else (cfs,n)
    _ -> (cfs, n)


cfsConstructionBaseCase (ModKleene ((_,fdinfo,ldinfo,_,_),reg)) n _ cfs = cfsConstructionBaseCase reg n (MyJust fdinfo, MyJust ldinfo) cfs

cfsConstructionBaseCase (ModConcat (_,(reg1,reg2))) n fsInfo cfs = cfsConstructionBaseCase (if flag then reg2 else reg1) n fsInfoNew cfs 
    where   (_,_,_,_,flag) = getRegInfo reg1
            (fsf, fsl) = fsInfo
            fsInfoNew = if not flag then (if getModContainsE reg2 then fsf else MyNothing,fsl) else (fsf, if getModContainsE reg1 then fsl else MyNothing)
    

cfsConstructionBaseCase (ModUnion (_,(reg1,reg2))) n fsinfo cfs = case reg1 of
    ModEmptyChar -> cfsConstructionBaseCase reg2 n fsinfo cfs
    _ -> cfsConstructionBaseCase (if flag then reg2 else reg1) n fsinfo cfs 
    where   (_,_,_,_,flag) = getRegInfo reg1

cfsConstructionBaseCase ModEmptyChar _ _ _ = error "cfsConstructionBaseCase : Got ModEmptyChar"



----------------------------------------------------------------------------------------------------------------------------------
----------------------------------------------- Step 4: Constructing the NFA -----------------------------------------------------
----------------------------------------------------------------------------------------------------------------------------------

--After the construction of the CFS system for the regex R, find the numbers which belong to first(R) and the numbers which belong to the last(R)
--Then create for each number in 


----------------------------------------------------------------------------------------------------------------------------------
----------------------------------- Step 5: Removing the linearization from the NFA ----------------------------------------------
----------------------------------------------------------------------------------------------------------------------------------




----------------------------------- Some functions used for testing the code written ---------------------------------------------


testing :: [Char] -> (LinearisationMap, NextInt, ModRegExpr)
testing = simplifyRegexInitialisation . parseRegexpr

testing1 :: [Char] -> (NextInt, NextInt, ModRegExpr, IndexedFirstData, IndexedLastData)
testing1 regex = (a1,a2, reg'', myZip fdlist [1..n], myZip ldlist [1..n])
    where   (l, _, reg) = testing regex
            n = getNumOfPositions reg
            (reg',a1, fdlist) = fdRoot reg n [] 
            (reg'',a2, ldlist) = ldRoot reg' n []

{- 
type CFSResult = (ModRegExpr, CFSSystem, NextInt, IndexedInfo, NumPosRem, (Bool,[FirstDataInfo],Int), (Bool,[LastDataInfo],Int), FirstList, LastList)

cfsConstructionAfterRec :: ModRegExpr -> IndexedInfo -> CFSSystem -> NextInt -> MyMaybe FStarInfo -> CFSResult
-}


testing2 :: [Char] -> (CFSSystem)
testing2 regex = (cfs)
    where   (a1,a2, reg, indexedFd, indexedLd) = testing1 regex
            (reg', cfs, nextInt, k) = cfsConstruction reg (indexedFd, indexedLd) [] 1 (MyNothing, MyNothing)
