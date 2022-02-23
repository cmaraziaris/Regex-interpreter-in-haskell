
import Types
import MakeNFA (makeNfa)
import NFAtoDFA (nfaToDfa)


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


-- Tests // TODO : RM before sending

inputs_full = [("ab|c","ab"), ("ab|.","abd"), ("(ab|.)*","abd")]
outputs_full = [True, False, True]

inputs_part = [("(ab)*", "abababde"), ("(ac|dd)*", "acacddeff")]
outputs_part = [["", "ab","abab","ababab"], ["","ac","acac","acacdd"]]

test_full :: Bool
test_full = (map regexFullMatch inputs_full) == outputs_full

test_part :: Bool
test_part = (map regexPartMatch inputs_part) == outputs_part

test_all :: Bool
test_all = test_full && test_part