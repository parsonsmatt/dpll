module DPLL where

import           Data.Foldable (asum)
import           Data.List     (nub, (\\))
import           Data.Map      (Map ())
import qualified Data.Map      as Map
import           Data.Maybe    (listToMaybe, mapMaybe, fromJust)
import           Data.Set      (Set ())
import qualified Data.Set      as Set

main = print (dpll ex ["p", "a", "c"] mempty)

dpll :: Clauses -> Symbols -> Model -> Maybe Model
dpll clauses symbols model
  | all (`isTrueIn` model) clauses  = Just model
  | any (`isFalseIn` model) clauses = Nothing
  | otherwise = asum (map (>>= next) controlList)
  where
    next :: Assignment -> Maybe Model
    next (sym := val) =
      dpll clauses (symbols `minus` sym) (model `including` (sym := val))

    controlList :: [Maybe Assignment]
    controlList =
      [ findPureSymbol symbols clauses model
      , findUnitClause clauses model
      , (:= False) <$> listToMaybe symbols
      , (:= True) <$> listToMaybe symbols
      ]

-- Well, now we've done a rather remarkable amount of work without doing
-- anything at all! Let's start defining some types and functions so the
-- above transcription actually means something.
-- Let's analyze what we're doing with the terms to get some idea of what
-- data types will fit for them.
-- A symbol could be anything -- but we'll just use a character for now.

type Symbol = String

-- We did commit to the list data structure for symbols with the `(x:xs)`
-- pattern matching. A set is likely more appropriate, but we'll defer that
-- performance improvement to later.
type Symbols = [Symbol]

minus :: Symbols -> Symbol -> Symbols
minus xs = (xs \\) . pure

-- Clauses is a collection of expressions. An expression is
-- an organization of terms in CNF.
type Clauses = [CNF]

-- With CNF, juxtaposion is conjunctions. We can therefore represent
-- a CNF expression as a list of literals.
type CNF = [Literal]

-- Finally, a literal is a pair of Sign and Symbol.
type Literal = (Sign, Symbol)

-- Of course, a sign is just a function that either negates or
-- doesn't negate a boolean expression.
data Sign = Pos | Neg
  deriving (Eq, Ord, Show)

apply :: Sign -> Bool -> Bool
apply Pos = id
apply Neg = not

n :: Symbol -> Literal
n c = (Neg, c)

p :: Symbol -> Literal
p c = (Pos, c)

-- We can now define the clauses given in the assignment:
ex2 :: Clauses
ex2 =
  [ [ n "p", p "a", p "c" ]
  , [ p "a" ]
  , [ p "p", n "c" ]
  ]

ex :: Clauses
ex =
  [ [ n "p", p "a", p "c" ]
  , [ n "a" ]
  , [ p "p", n "c" ]
  ]

-- The main use we have for the clauses type is to map over it
-- with `isTrueIn` and `isFalseIn`, checking every clause in the
-- list against the model. The model is an assignment of symbols
-- to truth values, so we'll use a map.
type Model = Map Symbol Bool

isTrueIn :: CNF -> Model -> Bool
isTrueIn cnf model = or (mapMaybe f cnf)
  where
    f (sign, symbol) = apply sign <$> Map.lookup symbol model


isFalseIn :: CNF -> Model -> Bool
isFalseIn cnf model = all not literals
  where
    literals = map f cnf
    f (sign, symbol) = apply sign (Map.findWithDefault (apply sign True) symbol model)

-- Right, where were we? We have the following terms not in scope:
-- * :=
-- * findPureSymbol
-- * including
-- * findUnitClause
-- Since `:=` starts with a colon, it has to be a data constructor.
-- It's used to signify assignment of a symbol to a value, so...

data Assignment = (:=) { getSymbol :: Symbol, getValue :: Bool }

instance Show Assignment where
  show (s := v) = "(" ++ s ++ " := " ++ show v ++ ")"


-- Which gives us a rather nice definition of the following:
including :: Model -> Assignment -> Model
including m (sym := val) = Map.insert sym val m

-- The final remaining items that aren't defined are findPureSymbol and
-- findUnitClause.
-- From the textbook,
-- > Pure symbol heuristic: A pure symbol is a symbol that always appears
-- > with the same "sign" in all clauses. For example, in the three clauses
-- > (A ∨ ¬B), (¬B ∨ ¬C), and (C ∨ A), the symbol A is pure because only
-- > the positive literal appears, B is pure because only the negative
-- > literal appears, and C is impure.
-- If a symbol has all negative signs, then the returned assignment is
-- False. If a symbol has all positive signs, then the returned assignment
-- is True.
-- We'll punt refining the clauses with the model to a future function...
findPureSymbol :: Symbols -> Clauses -> Model -> Maybe Assignment
findPureSymbol symbols clauses' model =
  asum (map makeAssignment symbols)
  where
    clauses = refinePure clauses' model

    makeAssignment :: Symbol -> Maybe Assignment
    makeAssignment sym =
      (sym :=) <$> negOrPos (signsForSymbol sym)

    signsForSymbol :: Symbol -> [Sign]
    signsForSymbol sym =
      clauses >>= signsForSymInClause sym

    signsForSymInClause :: Symbol -> CNF -> [Sign]
    signsForSymInClause sym =
      map fst . filter ((== sym) . snd)

    negOrPos :: [Sign] -> Maybe Bool
    negOrPos = getSingleton . nub . applyTrue

    applyTrue :: [Sign] -> [Bool]
    applyTrue = map (`apply` True)

getSingleton :: [a] -> Maybe a
getSingleton [x] = Just x
getSingleton _   = Nothing

-- Again, from the textbook,
-- > Unit clause heuristic: A unit clause was defined earlier as a clause
-- > with just one literal. In the context of DPLL, it also means clauses
-- > in which all literals but one are already assigned false by the model.
-- > For example, if the model contains B = true, then (¬B ∨ ¬C) simplifies
-- > to ¬C, which is a unit clause. Obviously, for this clause to be true,
-- > C must be set to false. The unit clause heuristic assigns all such symbols
-- > before branching on the remainder.
-- As above, we'll punt refining the clauses with the model.
findUnitClause :: Clauses -> Model -> Maybe Assignment
findUnitClause clauses' model =
  assignSymbol <$> firstUnitClause
  where
    clauses :: Clauses
    clauses = refineUnit clauses' model

    firstUnitClause :: Maybe Literal
    firstUnitClause =
      asum (map (getSingleton . mapMaybe ifInModel) clauses)

    ifInModel :: Literal -> Maybe Literal
    ifInModel (sign, symbol) =
      case Map.lookup symbol model of
           Just _ -> Nothing
           _ -> Just (sign, symbol)

    assignSymbol :: Literal -> Assignment
    assignSymbol (sign, symbol) = symbol := apply sign True

{-
Now, in the previous functions, we punted refining the clauses.
It's time to do that. We'll start by folding the model and clauses
into a new set of clauses. The helper function will go through
each symbol in the model, find the relevant clauses, and modify
them appropriately.

For a pure symbol, the given optimization (from the book):

> Note that, in determining the purity of a symbol, the algorithm can
> ignore clauses that are already known to be true in the model constructed
> so far. For example, if the model contains B = false, then the clause
> (¬B ∨ ¬C) is already true, and in the remaining clauses C appears only
> as a positive literal; therefore C becomes pure.

The algorithm can then be described as: For each symbol in the model, find
each clause in the clauses which is already true given the symbol's assigned
value. In our representation of the above, we'd get:

    helper 'b' False

so we'd want to first find the clauses with `(not, 'b')` as a member.
Then, we'd remove the clauses that are true given the assignment. So the
CNF: [(neg, 'b'), (neg, 'c')] would become [(neg, 'c')], a pure variable.

-}
refinePure :: Clauses -> Model -> Clauses
refinePure = Map.foldrWithKey f
  where
    f :: Symbol -> Bool -> Clauses -> Clauses
    f sym val = map discardTrue
      where
        discardTrue =
          filter (not . clauseIsTrue)
        clauseIsTrue (sign, symbol) =
          symbol == sym && apply sign val

{-
The optimization from the text for the unit clause is:

> In the context of DPLL, it also means clauses in which all literals but one
> are already assigned false by the model. For example, if the model contains
> B = true, then (¬B ∨ ¬C) simplifies to ¬C, which is a unit clause. Obviously,
> for this clause to be true, C must be set to false. The unit clause
> heuristic assigns all such symbols before branching on the remainder.

Rather than folding the model, we'll fold the clauses. Given a model where
(b, True) and a clause [(neg, 'b'), (neg, 'c')], this will transform it in
the following steps:
-}
refineUnit :: Clauses -> Model -> Clauses
refineUnit clauses model = map refine clauses
  where
    refine :: CNF -> CNF
    refine cnf =
      case allButOneFalse cnf of
           Just (s := True) -> [p s]
           Just (s := False) -> [n s]
           Nothing -> cnf

    allButOneFalse :: CNF -> Maybe Assignment
    allButOneFalse =
      getSingleton . filter (not . getValue) . map assign

    assign :: Literal -> Assignment
    assign (sign, sym) =
      sym := Map.findWithDefault (apply sign True) sym model

test e = dpll e ["p", "a", "c"] mempty

wat = Map.fromList [("a",False),("c",False),("p",False)]


showModel :: Model -> String
showModel = unlines . map (show . snd) . Map.toList . Map.mapWithKey (:=)

showOnlyTrue :: Model -> String
showOnlyTrue = unlines . map (show . snd) . filter (getValue . snd) . Map.toList . Map.mapWithKey (:=)

{-
Finally, we can encode the three coloring problem for Australia, and use
the algorithm to solve it.
To encode that a single state has a single color, that has the form:
-}

colors :: [Symbol]
colors = [green, blue, red]

green = "-green"
blue = "-blue"
red = "-red"

states :: [Symbol]
states =
  [ western
  , southern
  , northern
  , queensland
  , newSouthWales
  , victoria
  ]

western  = "Western"
southern = "Southern"
northern = "Northern"
queensland = "Queensland"
newSouthWales = "New South Wales"
victoria = "Victoria"
hasColor :: Symbol -> Clauses
hasColor st = 
   [ [ p $ st `is` green
     , p $ st `is` blue
     , p $ st `is` red
     ]
   , [ n $ st `is` blue
     , n $ st `is` red
     ]
   , [ n $ st `is` green
     , n $ st `is` red
     ]
   , [ n $ st `is` green
     , n $ st `is` blue
     ]
   ]

is :: Symbol -> Symbol -> Symbol
is = (++)

(/\) :: Clauses -> Clauses -> Clauses
(/\) = (++)

(/\:) :: Monad m => m a -> (a -> m b) -> m b
(/\:) = (>>=)


initialConditions :: Clauses
initialConditions = states /\: hasColor

{-
Now we've established that each state has a color that is either blue,
green, or red. We'll encode a way of saying that adjacent states must
be of different colors. With only two states and two colors, we could say:
$$a_1 \lor \neg b_1 \land \neg a_1 \lor b_1 \land a_2 \lor \neg b_2 \land \neg a_2 \lor b_2$$
-}

adjNotEqual :: (Symbol, Symbol) -> Clauses
adjNotEqual (a, b) = colors /\: bothAreNot
  where
    bothAreNot color =
      [ [ n $ a `is` color
        , n $ b `is` color
        ]
      ]

{-
Now we need a list of adjacent states...
-}

adjStates :: [(Symbol, Symbol)]
adjStates =
  [ (western, northern)
  , (western, southern)
  , (northern, southern)
  , (northern, queensland)
  , (southern, newSouthWales)
  , (southern, victoria)
  , (southern, queensland)
  , (newSouthWales, queensland)
  , (newSouthWales, victoria)
  ]

{-
And this gives us our final set of clauses:
-}

adjacentNotEqual = adjStates /\: adjNotEqual

australiaClauses =
  initialConditions /\ adjacentNotEqual

australiaSymbols =
  is <$> states <*> colors

australiaSolution =
  dpll australiaClauses australiaSymbols mempty

prettyAustralia = showModel <$> australiaSolution

printPlease = putStrLn (fromJust prettyAustralia)
