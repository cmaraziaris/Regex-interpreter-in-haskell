import Types ()
import RegParser (parseRegexpr, RegExpr(..))


type ContainsE = Bool

simplifyRegex :: RegExpr -> (ContainsE, RegExpr)

simplifyRegex (Kleene (Kleene reg)) = simplifyRegex (Kleene reg)
simplifyRegex (Kleene reg) = case simplifyRegex reg of
                (_, EmptyChar) -> (True, EmptyChar)
                (_, reg') -> (True, Kleene reg')

simplifyRegex (Concat (reg1, reg2)) = case simplifyRegex reg1 of
            (_ , EmptyChar) -> simplifyRegex reg2
            (containsE1, reg1') -> case simplifyRegex reg2 of
                (_, EmptyChar) -> (containsE1, reg1')
                (containsE2, reg2') -> (containsE1 && containsE2, Concat (reg1', reg2'))

simplifyRegex (Union (reg1, reg2)) = case simplifyRegex reg1 of
            (_ , EmptyChar) -> let (a,b) = simplifyRegex reg2 in if a then (True, b) else (True, Union (EmptyChar, b))
            (containsE1, reg1') -> case simplifyRegex reg2 of
                (_, EmptyChar) -> if containsE1 then (True, reg1') else (True, Union (EmptyChar, reg1'))
                (containsE2, reg2') -> (containsE1 || containsE2, Union (reg1', reg2'))

simplifyRegex EmptyChar = (True, EmptyChar)

simplifyRegex reg = (False, reg)

{- 

makeNfa :: [Char] -> Fsa
makeNfa = snd. makeNfa' . snd. simplifyRegex. parseRegexpr 


type NumOfStates = Int
makeNfa' :: RegExpr -> (NumOfStates, Fsa)

makeNfa' (Letter chr) = ([0,1], [chr], [(0,1,chr)], 0, [1])
makeNfa' AnyLetter    = ([0,1], [], [(0,1,'.')], 0, [1])


makeNfa' (Kleene (Kleene reg)) = makeNfa' (Kleene reg) -- ((str)*)* == (str)* 
makeNfa' (Union (reg1, reg2))
-}