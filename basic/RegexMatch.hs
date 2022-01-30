
import RegParser
import Types
import MakeNFA
import NFAtoDFA


regexFullMatch :: ([Char], [Char]) -> Bool
regexFullMatch (regStr, strPat) = search_full transitions finalStates firstState strPat
    where (_,_,transitions, firstState, finalStates) = nfaToDfa (makeNfa regStr)


-- search_full :: Transitions -> States -> StateId -> [Char] -> Bool
-- search_full transitions finalStates currState [] = is_member currState finalStates
-- search_full transitions finalStates currState (c:xs) = if nextState == [] then False else search_full transitions finalStates (head nextState) xs
--         where nextState = map (\(x,y,z) -> y) (filter (\(x,y,z) -> x == currState && z == c) transitions)

is_member x [] = False
is_member x (y:xs) = if x == y then True else is_member x xs


regexPartMatch :: ([Char], [Char]) -> [[Char]]
regexPartMatch (regStr, strPat) = search_part transitions finalStates firstState strPat ""
    where (_,_,transitions, firstState, finalStates) = nfaToDfa (makeNfa regStr)


search_part :: Transitions -> States -> StateId -> [Char] -> [Char] -> [[Char]]
search_part transitions finalStates currState [] stringSoFar = if is_member currState finalStates then [stringSoFar] else []
search_part transitions finalStates currState (c:xs) stringSoFar
            | nextState == [] = if is_member currState finalStates then [stringSoFar] else []
            | is_member currState finalStates = stringSoFar : (search_part transitions finalStates (head nextState) xs (stringSoFar ++ [c]))
            | otherwise = search_part transitions finalStates (head nextState) xs (stringSoFar ++ [c])
            where nextState = map (\(x,y,z) -> y) (filter (\(x,y,z) -> x == currState && z == c) transitions)

-- Bonus: Wildcard
search_full :: Transitions -> States -> StateId -> [Char] -> Bool
search_full transitions finalStates currState [] = is_member currState finalStates
search_full transitions finalStates currState (c:xs)
        | nextState == [] = False
        | length nextState == 1 = search_full transitions finalStates (head nextState) xs
        | otherwise = if (swrap (head nextState) == True) then True else swrap (head (tail nextState)) 
        where nextState = map (\(x,y,z) -> y) (filter (\(x,y,z) -> x == currState && (z == c || z == '.')) transitions)
              swrap state = search_full transitions finalStates state xs