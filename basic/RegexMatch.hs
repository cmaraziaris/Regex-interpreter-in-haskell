
import RegParser
import Types
import MakeNFA
import NFAtoDFA


regexFullMatch :: ([Char], [Char]) -> Bool
regexFullMatch (regStr, strPat) = searchFull transitions finalStates firstState strPat
    where (_,_,transitions, firstState, finalStates) = nfaToDfa (makeNfa regStr)

-- Bonus: Wildcard
searchFull :: Transitions -> States -> StateId -> [Char] -> Bool
searchFull transitions finalStates currState [] = isMember currState finalStates  -- Fully consumed input string
searchFull transitions finalStates currState (c:xs) =
        takeUntil ( == True) . map swrap . map (\(x,y,z) -> y) . filter (\(x,y,z) -> x == currState && (z == c || z == '.')) $ transitions
        where swrap state = searchFull transitions finalStates state xs

-- Bonus: Partial Matching
regexPartMatch :: ([Char], [Char]) -> [[Char]]
regexPartMatch (regStr, strPat) = searchPart transitions finalStates firstState strPat ""
    where (_,_,transitions, firstState, finalStates) = nfaToDfa (makeNfa regStr)


searchPart :: Transitions -> States -> StateId -> [Char] -> [Char] -> [[Char]]
searchPart transitions finalStates currState [] stringSoFar = if isMember currState finalStates then [stringSoFar] else []
searchPart transitions finalStates currState (c:xs) stringSoFar
            | nextState == [] = if isFinalState then [stringSoFar] else []
            | isFinalState = stringSoFar : cont
            | otherwise = cont
            where nextState = map (\(x,y,z) -> y) . filter (\(x,y,z) -> x == currState && z == c) $ transitions
                  cont = searchPart transitions finalStates (head nextState) xs (stringSoFar ++ [c])
                  isFinalState = isMember currState finalStates

isMember :: Eq t => t -> [t] -> Bool
isMember x [] = False
isMember x (y:xs) = (x == y) || isMember x xs

takeUntil :: (t -> Bool) -> [t] -> Bool
takeUntil f [] = False
takeUntil f (x:xs) = f x || takeUntil f xs