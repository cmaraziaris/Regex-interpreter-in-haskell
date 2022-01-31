
import RegParser
import Types
import MakeNFA
import NFAtoDFA


regexFullMatch :: ([Char], [Char]) -> Bool
regexFullMatch (regStr, strPat) = searchFull transitions finalStates firstState strPat
    where 
      (_,_,transitions, firstState, finalStates) = nfaToDfa (makeNfa regStr)


searchFull :: Transitions -> States -> StateId -> [Char] -> Bool
searchFull transitions finalStates currState [] = isMember currState finalStates  -- Fully consumed input string
searchFull transitions finalStates currState (c:xs) =
    evalUntil ( == True) . map sFullWrap . map (\(src,dest,char) -> dest) . filter getTrans $ transitions
  where 
    sFullWrap state = searchFull transitions finalStates state xs
    getTrans (src,dest,char) = src == currState && (char == c || char == '.')  -- Bonus: Wildcard


-- Bonus: Partial Matching

regexPartMatch :: ([Char], [Char]) -> [[Char]]
regexPartMatch (regStr, strPat) = searchPart transitions finalStates firstState strPat ""
    where
      (_,_,transitions, firstState, finalStates) = nfaToDfa (makeNfa regStr)

searchPart :: Transitions -> States -> StateId -> [Char] -> [Char] -> [[Char]]
searchPart transitions finalStates currState [] stringSoFar = if isMember currState finalStates then [stringSoFar] else []
searchPart transitions finalStates currState (c:xs) stringSoFar
    | nextState == [] = if isFinalState then [stringSoFar] else []
    | isFinalState = stringSoFar : cont
    | otherwise = cont
  where 
    nextState = map (\(src,dest,char) -> dest) . filter getTrans $ transitions
    cont = searchPart transitions finalStates (head nextState) xs (stringSoFar ++ [c])
    isFinalState = isMember currState finalStates
    getTrans (src,dest,char) = src == currState && char == c


-- Auxiliary

isMember :: Eq t => t -> [t] -> Bool
isMember x [] = False
isMember x (y:xs) = (x == y) || isMember x xs

evalUntil :: (t -> Bool) -> [t] -> Bool
evalUntil f [] = False
evalUntil f (x:xs) = f x || evalUntil f xs