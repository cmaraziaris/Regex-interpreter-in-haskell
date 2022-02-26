module MakeNFAUtilities where

import Utilities

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





type Index = Int --the position in the original list
type IndexedFirstData = [(Position, Index)] -- the FirstData list but every element has its index corresponind to the original firstdata
type IndexedLastData  = [(Position, Index)] -- same as IndexFirstData
type CFS = [Position] -- the positions the CFS contains
type FollowList = [Position] -- The positions which have a common follow set (CFS)
type CFSTuple = (Int, FollowList, CFS)
type CFSSystem = [CFSTuple]   -- The index of the CommonFollowSet, the positions which have in common the CFS as part of their
                                            -- follow-set decomposition, and the CFS itself

-- Functions used for getting specific information from a ModRegExpr
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

getNumOfPositions :: ModRegExpr -> NumOfPositions
getNumOfPositions ModEmptyChar = 0
getNumOfPositions (Num ((_, _,_,(num,_),_),_)) = num
getNumOfPositions (ModKleene ((_, _,_,(num,_),_),_)) = num
getNumOfPositions (ModUnion  ((_, _,_,(num,_),_),_)) = num
getNumOfPositions (ModConcat ((_, _,_,(num,_),_),_)) = num


type FStarInfo = (MyMaybe FirstDataInfo, MyMaybe LastDataInfo)
type IndexedInfo = (IndexedFirstData, IndexedLastData)
type FirstList = [Position] -- from subtree t1 with root F1, save first(F1) `intersection` pos(t1) 
type LastList = [Position]  -- from subtree t1 with root F1, save last(F1)  `intersection` pos(t1)

type NumPosRem = Int    -- The number |pos(t1)| of the subtree t1 which will be computed recursively and then removed
                        -- This number is important since it is necessary that the number of positions of every node/subexpression has to
                        -- be updated every time a new subtree t1 is created in the cfsConstruction


-- Update FStarInfo if current subexpression has for root a KleeneStar node 
updateFSInfo :: ModRegExpr -> FStarInfo -> FStarInfo
updateFSInfo (ModKleene ((_,fdinfo,ldinfo,_,_),_)) _ = (MyJust fdinfo, MyJust ldinfo)
--updateFSInfo (ModConcat )
updateFSInfo _ fsinfo = fsinfo

extractFirstLastPos :: IndexedInfo -> FirstDataInfo -> LastDataInfo -> (FirstList, LastList)
extractFirstLastPos (indexedFd, indexedLd) (fdPos, fdNum) (ldPos, ldNum) = (myMap myFst fd, myMap myFst ld)
    where   p_fd (_,n) =  fdPos <= n && n <= fdPos + (fdNum -1)
            p_ld (_,n) =  ldPos <= n && n <= ldPos + (ldNum -1)
            fd = myFilter p_fd indexedFd
            ld = myFilter p_ld indexedLd

separateFirstLastInfo :: IndexedInfo -> (Position,Position) -> (IndexedInfo,IndexedInfo)
separateFirstLastInfo (indexedFd, indexedLd) (pos1, pos2) = ((fd1,ld1), (fd2,ld2))
    where   p (n,_) = n >= pos1 && n <= pos2
            (fd1, fd2) = mySeparate p indexedFd
            (ld1, ld2) = mySeparate p indexedLd

setFlag :: ModRegExpr -> ModRegExpr
setFlag ModEmptyChar = error "setFlag: Got ModEmptyChar"
setFlag (Num       ((a1, a2, a3, a4, _),a5)) = Num       ((a1,a2,a3,a4,True),a5)
setFlag (ModKleene ((a1, a2, a3, a4, _),a5)) = ModKleene ((a1,a2,a3,a4,True),a5)
setFlag (ModUnion  ((a1, a2, a3, a4, _),a5)) = ModUnion  ((a1,a2,a3,a4,True),a5)
setFlag (ModConcat ((a1, a2, a3, a4, _),a5)) = ModConcat ((a1,a2,a3,a4,True),a5)

subtractPos :: ModRegExpr -> NumPosRem -> ModRegExpr
subtractPos ModEmptyChar _ = ModEmptyChar
subtractPos  (Num       ((a1,a2,a3,(a41,a42),a5),a)) k = Num       ((a1,a2,a3,(a41-k,a42),a5),a)
subtractPos  (ModKleene ((a1,a2,a3,(a41,a42),a5),a)) k = ModKleene ((a1,a2,a3,(a41-k,a42),a5),a)
subtractPos  (ModUnion  ((a1,a2,a3,(a41,a42),a5),a)) k = ModUnion  ((a1,a2,a3,(a41-k,a42),a5),a)
subtractPos  (ModConcat ((a1,a2,a3,(a41,a42),a5),a)) k = ModConcat ((a1,a2,a3,(a41-k,a42),a5),a)

-- |pos(t)| <= 3*|pos(t1)| <= 2*|pos(t)|


type IsLeft = Bool  --checks if findPath chose the left regex
type IsEnd  = Bool  --checks if the chosen regex/subtree (lets call it t1) of findPath satisfies the condition 1/3 |pos(t)| <= |pos(t1)| <= 2/3 |pos(t)| 
                    -- In other words, if IsEnd is True, the search for the subtree t1 has ended, it has be found. Otherwise, the search needs to continue
findPath :: NumOfPositions -> ModRegExpr -> ModRegExpr -> (IsLeft, IsEnd)
findPath _ ModEmptyChar _ = (False, False)
findPath _ _ ModEmptyChar = (True, False)
findPath numPos reg1 reg2 
    | flag1 = (False,False)
    | flag2 = (True, False)
    | b11 && b12 = (True, True)
    | b21 && b22 = (False, True)
    | pos1 > pos2 = (True, False)
    | otherwise = (False, False)
    where   (_,_,_,_,flag1) = getRegInfo reg1
            (_,_,_,_,flag2) = getRegInfo reg2
            pos1 = getNumOfPositions reg1
            pos2 = getNumOfPositions reg2
            b11 = 3*pos1 >= numPos
            b12 = 3*pos1 <= 2*numPos
            b21 = 3*pos2 >= numPos
            b22 = 3*pos2 <= 2*numPos


-- Filter the rootlist
filterRootList :: ([(Int, Int)], Int) -> (Int, Int) -> [(Int, Int)]
filterRootList (l,0) tuple = l
filterRootList ((dataPos,dataNum):l,n) tuple@(dataPos', dataNum') = if f then filteredL else (dataPos,dataNum):filteredL
    where   filteredL = filterRootList (l,n-1) tuple 
            f = dataPos' <= dataPos && dataPos' + dataNum' >= dataPos + dataNum -- (f/l)data is subset of (f/l)data' 

filterRootList _ _ = error "filterRootList; Got [[],n] with n > 0 which should not happen" -- a case which will never happem

rootlistUpdate :: (Bool,[FirstDataInfo], [FirstDataInfo], Int) -> MyMaybe FirstDataInfo -> (Bool,[LastDataInfo], [LastDataInfo],Int) -> MyMaybe LastDataInfo -> ContainsE -> ContainsE -> (([FirstDataInfo], [FirstDataInfo], Int), ([LastDataInfo], [LastDataInfo], Int))

rootlistUpdate (fbool,f1, f2,fnum) fdInfo (lbool,l1, l2,lnum) ldInfo e1 e2 = case (fdInfo,ldInfo) of
        -- the Parent node is KleeneStar
        (MyJust fdInfo', MyJust ldInfo') -> (if fbool then (f1,f2,fnum) else (fdInfo' : filterRootList (f1, fnum) fdInfo',f2,1), if lbool then (l1,l2,lnum) else (ldInfo' : filterRootList (l1, lnum) ldInfo',l2,1))
        -- the parent node of G is of the form G x H
        (MyJust fdInfo', MyNothing) -> (if fbool then (f1,f2,fnum) else if e1 then (fdInfo' : f1, f2,fnum+1) else (f1, fdInfo' : f2, fnum), if e2 then (l1,l2,lnum) else ([], (l1 ++ l2), 0))
        -- the parent node of G is of the form H x G
        (MyNothing, MyJust ldInfo') -> (if e1 then (f1,f2,fnum) else ([], f1 ++ f2, 0), if lbool then (l1,l2,lnum) else if e2 then (ldInfo' : l1, l2, lnum+1) else (l1, ldInfo' : l2, lnum))
        -- the parent node is a Union thus we ignore it
        (MyNothing, MyNothing) -> ((f1,f2,fnum), (l1,l2,lnum)) 

